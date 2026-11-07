"""
AstrBot 微信群管理插件
适配：wechat_agent 适配器（个人微信 agent-wechat 守护进程），AstrBot 桌面版 / 源码版均可。

功能：
  1. 定时提醒：可 @全体成员 或 @指定成员（按微信号/群昵称），内容自定义、支持变量
     —— 既能在 WebUI 插件配置面板里可视化增删规则，也能用聊天指令创建
  2. 退群 / 入群监控：多行明细播报（微信号 / 群昵称 / 时间），模板可自定义
  3. 群管理增强：建群 / 改群名 / 拉人 / 踢人 / 退群 / 清群公告 /
     改群内昵称 / 置顶会话 / 免打扰，破坏性操作带二次确认
  4. 官方接龙引子：发「📋 接龙功能测试：
0. 标题内容
1. 第一个人」文本，微信显示「参与接龙」；只发起不参与
  5. 只读查询：群列表、群资料、群成员、联系人、守护进程能力
  6. 指令管理，仅管理员可用

实现要点（针对 wechat_agent 实测 API）：
  - 客户端：event.platform.get_client()，返回 WeChatClient
  - 拉成员：await client.group_lookup(thread_id)（优先，读 contact.db），
            为空时回退 await client.group_members(thread_id)
  - 发送：优先 adapter.send_chain(thread_id, MessageChain)，
          该入口把 AtAll -> mention_all、At(qq=wxid) -> mentions.userIds
  - 群变更：await client.request(method, client._acc(suffix), json_body=..., headers={"Idempotency-Key": ...})，
            返回 operation 后轮询 client.operation(op_id) 直到终态
  - 调度：纯 asyncio 循环，零第三方依赖（桌面版环境封闭）
  - 配置持久化：AstrBot KV

注意：退群/入群时间是「轮询检测到变动的时间」，不是微信服务器记录的精确时刻，
      最多滞后一个轮询间隔。微信号为守护进程返回的成员 id（wxid），非用户自定义微信号。
"""

import asyncio
import re
import time
import uuid
from collections import deque
from datetime import datetime
from typing import Any, Dict, List, Optional, Set, Tuple

from astrbot.api import AstrBotConfig, logger
from astrbot.api.event import AstrMessageEvent, MessageChain, filter
from astrbot.api.event.filter import EventMessageType, PermissionType
from astrbot.api.message_components import At, AtAll, Plain
from astrbot.api.star import Context, Star, register
from astrbot.api.web import json_response, request as web_request

PLATFORM_NAMES = {"wechat_agent", "wechat", "gewechat"}
KV_MONITORED = "wxga_monitored"
KV_SCHEDULES = "wxga_schedules"
KV_NOTIFY = "wxga_notify_group"
KV_GROUPS = "wxga_groups"

_RE_TIME_ONLY = re.compile(r"^(\d{1,2}):(\d{2})$")
_RE_TIME_DOW = re.compile(r"^([\w,\-]+)\s+(\d{1,2}):(\d{2})$")
_RE_DOW_ONLY = re.compile(r"^[a-z0-9,\-]+$", re.I)
_DOW_NAMES = {"mon": 0, "tue": 1, "wed": 2, "thu": 3, "fri": 4, "sat": 5, "sun": 6}

DEFAULT_LEAVE_TEMPLATE = (
    "{nickname} 什么时候离开了本群\n"
    "微信号：{wxid}\n"
    "群昵称：{nickname}\n"
    "退群时间：{time}"
)
DEFAULT_JOIN_TEMPLATE = (
    "{nickname} 什么时候加入了本群\n"
    "微信号：{wxid}\n"
    "群昵称：{nickname}\n"
    "入群时间：{time}"
)

# ---- 群变更（agent-wechat daemon REST）----------------------------------
# 已经用不存在的群 id 逐个安全探测过，方法与请求体字段均确认可用。
_MUTATION_OK_STATES = {
    "succeeded", "completed", "success", "accepted", "done",
    "server_accepted", "confirmed", "available",
}
_MUTATION_FAIL_STATES = {
    "failed", "cancelled", "canceled", "expired", "rejected",
    "needs_review", "partial", "unsupported", "error",
}
_MUTATION_ERROR_HINTS = {
    "group_contact_unavailable": "群不存在或守护进程联系人缓存未同步。用 /群列表 查真实群 id，或稍等同步完成后重试。",
    "invalid_group_members": "成员数量/格式不合法：建群需 2~40 人，增删成员至少 1 人且必须填 wxid（不是昵称）。",
    "invalid_group_text": "群名或群内昵称为空，或含有微信不支持的字符。",
    "invalid_group_id": "群 id 格式不对，应为 xxxxx@chatroom。",
    "invalid_group_identity": "群身份校验失败，确认机器人仍在该群内。",
    "invalid_group_idempotency_key": "幂等键异常，重试一次即可。",
    "group_state_incomplete": "群资料尚未同步完整，稍后重试。",
    "group_rpc": "微信服务端调用失败，稍后重试。",
    "group_operation_identity_conflict": "同一幂等键对应了不同请求，请稍后重试。",
    "unsupported_capability": "当前微信版本/守护进程不支持该操作，用 /群管能力 查看支持列表。",
    "admin_required": "需要群主或管理员权限，当前账号权限不足。",
    "forbidden": "权限不足：守护进程能力标注 groupMutationScope=admin（仅群主/管理员）。",
    "permission_denied": "权限不足：需要群主或管理员。",
    "auth_required": "微信登录态失效，请在守护进程重新登录。",
    "needs_review": "守护进程判定该操作需要人工复核，未自动执行。",
    "rate_limited": "操作太频繁，稍后再试。",
}
_RE_ON = re.compile(r"^(on|1|true|yes|开|开启|置顶|免打扰)$", re.I)
_RE_OFF = re.compile(r"^(off|0|false|no|关|关闭|取消置顶|取消免打扰)$", re.I)


def _time_vars() -> Dict[str, str]:
    """模板可用变量：完整时间 / 时钟 / 日期 / 星期。"""
    now = datetime.now()
    return {
        "time": now.strftime("%Y-%m-%d %H:%M:%S"),
        "clock": now.strftime("%H:%M"),
        "date": now.strftime("%Y-%m-%d"),
        "weekday": "星期" + "一二三四五六日"[now.weekday()],
    }


def _normalize_chatroom(gid: str) -> str:
    """规范成 xxxx@chatroom 形式（wechat_agent 的 thread_id）。"""
    gid = (gid or "").strip()
    return gid if gid.endswith("@chatroom") else gid + "@chatroom"


def _parse_dow(expr: Optional[str]) -> Set[int]:
    """把 'mon-fri' / '1-5' / 'mon,wed,fri' 解析成 Python weekday 集合（0=周一）。空=全部。"""
    if not expr:
        return set(range(7))
    out: Set[int] = set()
    for part in str(expr).lower().replace(" ", "").split(","):
        if not part:
            continue
        rng = re.match(r"^(\w+)-(\w+)$", part)
        if rng:
            a, b = rng.group(1), rng.group(2)
            ai = _DOW_NAMES.get(a, int(a) if a.isdigit() else 0)
            bi = _DOW_NAMES.get(b, int(b) if b.isdigit() else 6)
            out.update(range(min(ai, bi), max(ai, bi) + 1))
        elif part.isdigit():
            out.add(int(part))
        elif part in _DOW_NAMES:
            out.add(_DOW_NAMES[part])
    return out or set(range(7))


@register(
    "astrbot_plugin_wechat_group_admin",
    "青璃",
    "微信群管理：面板化定时@/发起官方接龙、命令双向同步、群设置变更（wechat_agent 适配器）",
    "1.7.1",
    "https://github.com/AstrBotDevs/AstrBot",
)
class WechatGroupAdmin(Star):
    def __init__(self, context: Context, config: AstrBotConfig):
        super().__init__(context)
        self.config = config
        self.adapter = None       # WeChatAgentAdapter 实例
        self.client = None        # WeChatClient 实例
        self.groups: Dict[str, Dict[str, Any]] = {}      # gid -> {umo, thread_id, name}
        self.snapshots: Dict[str, Dict[str, str]] = {}   # gid -> {member_id: 群昵称}
        self.snapshots_wx: Dict[str, Dict[str, str]] = {}  # gid -> {member_id: 微信昵称}
        self.snapshot_source: Dict[str, str] = {}        # gid -> 上次用的成员接口名
        self._pending_diff: Dict[str, Dict[str, Any]] = {}  # gid -> 待确认差比（防误报）
        self.monitored: List[str] = []
        self.schedules: List[Dict[str, Any]] = []
        self.notify_group: str = ""
        self._fired: Set[str] = set()
        self._last_poll = time.time()
        self._warned_no_client = False
        self._last_send_error: str = ""
        self._pending: Dict[str, Dict[str, Any]] = {}   # 破坏性操作的待确认记录
        self._events: deque = deque(maxlen=500)         # 退群/入群/拦截事件（内存，重启清空）
        self._last_groups_fetch: float = 0              # 上次从微信拉群列表的时间
        self._loop_task: Optional[asyncio.Task] = None
        self._register_web_apis()                        # views/dashboard 管理页后端 API
        asyncio.create_task(self._async_init())

    # ===================================================================
    # 生命周期 / 调度
    # ===================================================================
    # ---------- 配置面板 = 唯一数据源 ----------
    @property
    def _opts(self) -> dict:
        """全部插件数据存于 config['options']（schema 声明为 type=dict，重载不清理）。

        WebUI 自带配置页因此只需一个入口，所有参数在插件管理面板里维护。
        """
        o = self.config.get("options")
        if not isinstance(o, dict):
            o = {}
            self.config["options"] = o
        return o

    @staticmethod
    def _normalize_gid(value) -> str:
        """把 UMO / 纯群号 / 群 ID 统一成 xxx@chatroom。"""
        s = str(value or "").strip()
        if not s:
            return ""
        if ":" in s:                       # wechat_agent:GroupMessage:xxx@chatroom
            s = s.rsplit(":", 1)[-1].strip()
        if s and "@" not in s:
            s += "@chatroom"
        return s

    async def _save_config(self) -> bool:
        """把命令产生的改动写回插件配置文件，WebUI 面板即可看到。不触发热重载。"""
        try:
            fn = getattr(self.config, "save_config_async", None)
            if fn:
                await fn()
            else:
                self.config.save_config()
            return True
        except Exception as e:
            logger.error(f"[群管] 回写配置面板失败：{e}")
            return False

    def _rules(self) -> List[dict]:
        v = self._opts.get("at_schedules") or []
        return [dict(x) for x in v if isinstance(x, dict)] if isinstance(v, list) else []

    async def _register_group_option(self, umo: str) -> None:
        """把新发现的群会话写进面板「已发现的群」，供可视化选择。只在出现新群时落盘。"""
        if not umo or ":GroupMessage:" not in str(umo):
            return
        opts = self._opts.get("group_options") or []
        if not isinstance(opts, list):
            opts = []
        if umo in opts:
            return
        opts.append(str(umo))
        self._opts["group_options"] = opts[-100:]
        await self._save_config()
        logger.info(f"[群管] 已把新群加入面板群选项：{umo}")

    def _monitored_from_config(self) -> List[str]:
        v = self._opts.get("monitored_groups") or []
        out: List[str] = []
        for x in v if isinstance(v, list) else []:
            g = self._normalize_gid(x)
            if g and g not in out:
                out.append(g)
        return out

    def _dow_to_flags(self, dow) -> dict:
        days = _parse_dow(dow)
        return {k: (i in days) for i, k in enumerate(self._WD_KEYS)}

    def _task_to_rule(self, t: dict) -> dict:
        """标准任务 → 面板规则（命令添加、旧 KV 迁移共用）。"""
        dow = t.get("day_of_week")
        weekly = bool(dow)
        flags = self._dow_to_flags(dow) if weekly else {k: True for k in self._WD_KEYS}
        return {
            "__template_key": "at_schedule",
            "enabled": True,
            "group_id": self._normalize_gid(t.get("group_id")),
            "repeat": "weekly" if weekly else "daily",
            **flags,
            "time": f"{int(t['hour']):02d}:{int(t['minute']):02d}",
            "target": "members" if t.get("target") == "members" else "all",
            "members": ",".join(str(m) for m in (t.get("members") or [])),
            "content": str(t.get("content") or ""),
            "note": "由指令添加/旧版迁移",
        }

    def _load_state_from_config(self):
        """刷新内存镜像。所有命令与调度都以此为唯一依据。"""
        self.schedules = self._config_at_tasks()
        self.monitored = self._monitored_from_config()
        self.notify_group = self._normalize_gid(self._opts.get("notify_group") or "")

    async def _migrate_kv_to_config(self):
        """旧版 KV 里的任务/监控群一次性搬进面板，之后不再用 KV 存这些。"""
        try:
            old_sched = (await self.get_kv_data(KV_SCHEDULES, [])) or []
            old_mon = (await self.get_kv_data(KV_MONITORED, [])) or []
            old_notify = (await self.get_kv_data(KV_NOTIFY, "")) or ""
        except Exception as e:
            logger.warning(f"[群管] 读取旧 KV 失败：{e}")
            return
        if not (old_sched or old_mon or old_notify):
            return
        rules = self._rules()
        seen = {(self._normalize_gid(r.get("group_id")), str(r.get("time") or ""),
                 str(r.get("content") or "")) for r in rules}
        added = 0
        for t in old_sched:
            if not isinstance(t, dict):
                continue
            r = self._task_to_rule(t)
            key = (r["group_id"], r["time"], r["content"])
            if r["group_id"] and key not in seen:
                rules.append(r)
                seen.add(key)
                added += 1
        mons = self._monitored_from_config()
        for g in old_mon:
            g = self._normalize_gid(g)
            if g and g not in mons:
                mons.append(g)
        self._opts["at_schedules"] = rules
        self._opts["monitored_groups"] = mons
        if old_notify and not self._opts.get("notify_group"):
            self._opts["notify_group"] = self._normalize_gid(old_notify)
        await self._save_config()
        try:
            await self.put_kv_data(KV_SCHEDULES, [])
            await self.put_kv_data(KV_MONITORED, [])
            await self.put_kv_data(KV_NOTIFY, "")
        except Exception:
            pass
        logger.info(f"[群管] 旧 KV 已迁移到配置面板：任务 +{added} 条，监控群 {len(mons)} 个")

    def _try_capture_client(self) -> bool:
        """启动/重载后直接从平台管理器抓 wechat_agent 客户端，不必等群里来消息。"""
        try:
            pm = getattr(self.context, "platform_manager", None)
            insts = list(getattr(pm, "platform_insts", []) or [])
        except Exception:
            insts = []
        for plat in insts:
            name = ""
            try:
                meta = plat.meta()
                name = str(getattr(meta, "name", "") or getattr(meta, "id", "") or "")
            except Exception:
                pass
            if name and name not in PLATFORM_NAMES and "wechat" not in name.lower():
                continue
            try:
                getter = getattr(plat, "get_client", None)
                client = getter() if getter else getattr(plat, "client", None)
            except Exception:
                client = None
            if client is not None:
                self.adapter, self.client = plat, client
                logger.info(f"[群管] 已捕获 wechat_agent 客户端（平台 {name or 'wechat_agent'}）。")
                return True
        return False

    async def _async_init(self):
        try:
            # 注意：AstrBot 4.x 的 get_kv_data(key, default) 中 default 是必填位置参数。
            # 热重载后仍需能主动发消息，群会话映射继续走 KV。
            self.groups = (await self.get_kv_data(KV_GROUPS, {})) or {}
        except Exception as e:
            logger.warning(f"[群管] 读取 KV 失败：{e}")
            self.groups = {}
        await self._migrate_kv_to_config()
        self._load_state_from_config()
        self._try_capture_client()
        self._loop_task = asyncio.create_task(self._loop())
        logger.info(
            f"[群管] 已启动（wechat_agent）。监控群 {len(self.monitored)} 个，"
            f"定时艾特 {len(self.schedules)} 个（数据源=配置面板），"
            f"退群轮询 {self._poll_interval()} 分钟。"
        )

    async def terminate(self):
        """重载/卸载插件时由 AstrBot 调用，停掉后台循环，避免定时任务重复触发。"""
        t = self._loop_task
        if t is not None and not t.done():
            t.cancel()
            try:
                await t
            except (asyncio.CancelledError, Exception):
                pass
        self._pending.clear()
        try:
            await self.put_kv_data(KV_GROUPS, self.groups)
        except Exception as e:
            logger.warning(f"[群管] 卸载时保存状态失败：{e}")
        logger.info("[群管] 已停止后台调度循环。")

    def _poll_interval(self) -> int:
        try:
            return max(1, min(int(self._opts.get("poll_interval_min", 5) or 5), 60))
        except (TypeError, ValueError):
            return 5

    async def _loop(self):
        """单一调度循环：每 20 秒检查定时任务 + 按间隔做退群轮询。无第三方依赖。"""
        while True:
            try:
                await self._tick()
            except Exception as e:
                logger.error(f"[群管] 调度循环异常：{e}")
            await asyncio.sleep(20)

    async def _tick(self):
        if self._opts.get("enable") is False:
            return  # 插件总开关关闭：所有后台动作停止
        if self.client is None:
            # 守护进程晚于插件就绪时自动重试捕获（每轮 20s 一次，开销可忽略）
            self._try_capture_client()
        now = datetime.now()
        minute_key = now.strftime("%Y-%m-%d %H:%M")
        hhmm = now.strftime("%H:%M")
        weekday = now.weekday()

        # 定时艾特：面板规则 + 聊天指令建的任务，合并执行，各自独立去重
        for task in self._all_tasks():
            try:
                if f"{int(task['hour']):02d}:{int(task['minute']):02d}" != hhmm:
                    continue
                if weekday not in _parse_dow(task.get("day_of_week")):
                    continue
                fire_key = f"at_{task.get('source', 'kv')}_{task.get('id')}_{minute_key}"
                if fire_key in self._fired:
                    continue
                self._fired.add(fire_key)
                await self._run_atall(task)
                if task.get("repeat") == "once":
                    await self._disable_at_rule_once(task)
            except Exception as e:
                logger.error(f"[群管] 定时任务执行失败：{e}")

        # 定时发起官方接龙引子（只发一条文本，成员点「参与接龙」即可）
        for rule in self._config_chain_starters():
            try:
                if f"{int(rule['hour']):02d}:{int(rule['minute']):02d}" != hhmm:
                    continue
                if weekday not in _parse_dow(rule.get("day_of_week")):
                    continue
                fk = f"chainstarter_{rule['id']}_{minute_key}"
                if fk in self._fired:
                    continue
                self._fired.add(fk)
                await self._send_chain_starter(
                    rule["group_id"], rule["topic"], rule.get("first_item", "")
                )
                if rule.get("repeat") == "once":
                    await self._disable_chain_rule_once(rule)
            except Exception as e:
                logger.error(f"[群管] 定时发起接龙失败：{e}")

        if self.monitored and time.time() - self._last_poll >= self._poll_interval() * 60:
            self._last_poll = time.time()
            await self._poll_once()

        if len(self._fired) > 500:
            self._fired.clear()

        if self._pending:
            ttl, ts = self._confirm_ttl(), time.time()
            for k in [k for k, v in self._pending.items() if ts - v["ts"] > ttl]:
                self._pending.pop(k, None)

    # ===================================================================
    # 抓取适配器客户端（群消息 + 私聊都抓，尽早拿到 client）
    # ===================================================================
    @filter.event_message_type(EventMessageType.GROUP_MESSAGE)
    async def _capture_group(self, event: AstrMessageEvent):
        await self._capture(event)

    @filter.event_message_type(EventMessageType.PRIVATE_MESSAGE)
    async def _capture_private(self, event: AstrMessageEvent):
        await self._capture(event)

    async def _capture(self, event: AstrMessageEvent):
        plat = getattr(event, "platform", None)
        has_client = plat is not None and (
            hasattr(plat, "get_client") or hasattr(plat, "client")
        )
        if event.get_platform_name() not in PLATFORM_NAMES and not has_client:
            return
        if plat is not None:
            try:
                getter = getattr(plat, "get_client", None)
                client = getter() if getter else getattr(plat, "client", None)
            except Exception:
                client = None
            if client is not None:
                self.adapter, self.client = plat, client
        elif getattr(event, "client", None) is not None:
            self.client = event.client

        gid = event.get_group_id()
        if gid:
            info = self.groups.setdefault(
                gid, {"umo": None, "thread_id": _normalize_chatroom(gid), "name": ""}
            )
            umo, tid = event.unified_msg_origin, _normalize_chatroom(gid)
            changed = info.get("umo") != umo or info.get("thread_id") != tid
            info["umo"], info["thread_id"] = umo, tid
            if changed:
                await self.put_kv_data(KV_GROUPS, self.groups)
            await self._register_group_option(umo)

    # ===================================================================
    # 定时任务：面板规则 + 聊天指令规则统一调度
    # ===================================================================
    def _cfg_list(self, key: str) -> List[dict]:
        """读配置面板的 template_list；每次现读，保存后无需重启即可生效。"""
        v = self._opts.get(key) or []
        return [x for x in v if isinstance(x, dict)] if isinstance(v, list) else []

    _WD_KEYS = ("wd_mon", "wd_tue", "wd_wed", "wd_thu", "wd_fri", "wd_sat", "wd_sun")

    @classmethod
    def _config_dow(cls, r: dict) -> Tuple[bool, Optional[str]]:
        """面板「每天/每周 + 勾选星期」→ (是否生成任务, 星期表达式)。

        返回 None 表示每天；返回 False 表示一周一天都没勾，整条规则不生成。
        老配置没有 wd_* 键时返回 None，交给 time 里原有的 mon-fri 表达式处理。
        """
        if str(r.get("repeat") or "daily").lower() != "weekly":
            return True, None
        if not any(k in r for k in cls._WD_KEYS):
            return True, None
        picked = [str(i) for i, k in enumerate(cls._WD_KEYS) if r.get(k) is True]
        if not picked:
            return False, None
        return True, (None if len(picked) == 7 else ",".join(picked))

    def _config_at_tasks(self) -> List[Dict[str, Any]]:
        """把配置面板的 at_schedules 展开成标准任务（一条规则可含多个时间点）。"""
        out: List[Dict[str, Any]] = []
        for i, r in enumerate(self._cfg_list("at_schedules")):
            if r.get("enabled") is False:
                continue
            gid = self._normalize_gid(r.get("group_id"))
            if not gid:
                continue
            times = self._expand_times(str(r.get("time") or ""))
            if not times:
                continue
            gen, dow_expr = self._config_dow(r)
            if not gen:
                logger.debug(f"[群管] 面板规则 #{i + 1} 未勾选任何星期，已跳过")
                continue
            members = [m.strip() for m in str(r.get("members") or "").split(",") if m.strip()]
            for j, (h, m, dow) in enumerate(times):
                out.append({
                    "id": f"{i}_{j}", "source": "cfg", "group_id": gid,
                    # time 里自带星期表达式（旧写法）优先，否则用面板勾选
                    "hour": h, "minute": m, "day_of_week": dow or dow_expr,
                    "repeat": str(r.get("repeat") or "daily").lower(),
                    "target": "members" if r.get("target") == "members" else "all",
                    "members": members,
                    "content": str(r.get("content") or ""),
                })
        return out

    def _all_tasks(self) -> List[Dict[str, Any]]:
        """self.schedules 已是配置面板 at_schedules 的展开镜像，不再二次叠加。"""
        return [dict(t) for t in list(self.schedules) if isinstance(t, dict)]

    def _config_chain_starters(self) -> List[Dict[str, Any]]:
        """展开面板的「自动发起接龙」规则。time 留空 = 只手动发起。"""
        out: List[Dict[str, Any]] = []
        for i, r in enumerate(self._cfg_list("chain_starters")):
            if r.get("enabled") is False:
                continue
            gid = self._normalize_gid(r.get("group_id"))
            topic = str(r.get("topic") or "").strip()
            time_str = str(r.get("time") or "").strip()
            if not gid or not topic or not time_str:
                continue
            gen, dow_expr = self._config_dow(r)
            if not gen:
                continue
            for j, (h, m, dow) in enumerate(self._expand_times(time_str)):
                out.append({
                    "id": f"{i}_{j}", "group_id": gid, "topic": topic,
                    "first_item": str(r.get("first_item") or "").strip(),
                    "hour": h, "minute": m, "day_of_week": dow or dow_expr,
                    "repeat": str(r.get("repeat") or "daily").lower(),
                })
        return out

    async def _disable_at_rule_once(self, task: Dict[str, Any]):
        """一次性定时@触发后，把来源面板规则置为停用并持久化，避免重复触发。"""
        try:
            i = int(str(task.get("id", "")).split("_")[0])
            rules = self._opts.get("at_schedules") or []
            if not (0 <= i < len(rules)):
                return
            rules[i]["enabled"] = False
            self._opts["at_schedules"] = rules
            self._load_state_from_config()   # 重建内存镜像（自动排除已停用规则）
            await self._save_config()
            logger.info(f"[群管] 一次性定时任务 #{i + 1} 已触发并自动停用")
        except Exception as e:
            logger.error(f"[群管] 停用一次性定时任务失败：{e}")

    async def _disable_chain_rule_once(self, rule: Dict[str, Any]):
        """一次性接龙引子触发后，停用来源面板规则并持久化。"""
        try:
            i = int(str(rule.get("id", "")).split("_")[0])
            rules = self._opts.get("chain_starters") or []
            if not (0 <= i < len(rules)):
                return
            rules[i]["enabled"] = False
            self._opts["chain_starters"] = rules
            await self._save_config()
            logger.info(f"[群管] 一次性接龙任务 #{i + 1} 已触发并自动停用")
        except Exception as e:
            logger.error(f"[群管] 停用一次性接龙任务失败：{e}")

    @staticmethod
    def _chain_starter_text(topic: str, first_item: str = "") -> str:
        """微信客户端识别「参与接龙」的文本格式（实测）。

        稳定触发格式（2026-11-07 实测矩阵）：
          标题行：📋 接龙功能测试：
          0. 行：自定义标题内容（如 双十接龙）
          1. 行：第一个接龙项（如 太华红豆糕）
        - 标题必须是白名单词「接龙功能测试：」，自定义标题（双十接龙等）放 0. 行，
          放标题行一律不触发（已逐条验证）。
        - 必须 LF 换行、末尾不换行（CRLF 不触发）。
        - 以 #接龙 开头不会触发（实测 type=1 普通文本）。
        """
        title = str(topic or "").strip() or "接龙"
        first = str(first_item or "").strip() or "报名"
        return f"📋 接龙功能测试：\n0. {title}\n1. {first}"

    async def _send_chain_starter(self, gid: str, topic: str,
                                  first_item: str = "") -> bool:
        """只发出接龙引子文本，不监听、不统计、不参与接龙。"""
        gid = self._normalize_gid(gid)
        if not gid:
            return False
        text = self._chain_starter_text(topic, first_item)
        ok = await self._send_plain(gid, text)
        if ok:
            logger.info(f"[群管] 已发起接龙引子 -> 群 {gid}：{topic}")
        return ok

    async def _send_plain(self, gid: str, text: str) -> bool:
        """发单条纯文本；绕过 notify_group 转发，避免接龙引子被复制多份。"""
        mc = MessageChain(chain=[Plain(text)])
        tid = (self.groups.get(gid) or {}).get("thread_id") or _normalize_chatroom(gid)
        if self.adapter is not None:
            try:
                await self.adapter.send_chain(tid, mc)
                return True
            except Exception as e:
                logger.warning(f"[群管] 直发接龙引子失败，回退标准接口：{e}")
                self._last_send_error = (
                    f"{datetime.now().strftime('%m-%d %H:%M')} 群 {gid} 直发失败：{e}"
                )
        info = self.groups.get(gid) or {}
        umo = info.get("umo")
        if not umo:
            logger.warning(f"[群管] 群 {gid} 无会话来源(umo)，无法发起接龙；请在该群发一条消息。")
            return False
        try:
            await self.context.send_message(umo, mc)
            return True
        except Exception as e:
            self._last_send_error = (
                f"{datetime.now().strftime('%m-%d %H:%M')} 群 {gid}：{e}"
            )
            logger.error(f"[群管] 发起接龙引子失败(群 {gid})：{e}")
            return False

    async def _run_atall(self, task: Dict[str, Any]):
        gid = task.get("group_id")
        if not gid:
            return
        chain, label = await self._build_target_chain(gid, task)
        content = self._fmt(str(task.get("content", "")), group=gid, **_time_vars())
        chain.append(Plain(content))
        await self._send_to_group(gid, chain)
        logger.info(f"[群管] 定时提醒 -> 群 {gid} / {label}")

    async def _build_target_chain(self, gid: str, task: Dict[str, Any]) -> Tuple[List[Any], str]:
        """按任务目标构造 @ 组件：@全体 或 @指定成员。"""
        if task.get("target") != "members":
            return [AtAll()], "@全体"
        raw = [str(m).strip() for m in task.get("members", []) if str(m).strip()]
        ids = await self._resolve_member_ids(gid, raw)
        if not ids:
            logger.warning("[群管] 指定成员任务没有有效目标，降级为 @全体")
            return [AtAll()], "@全体(目标为空)"
        return [At(qq=m) for m in ids], "@成员(" + ",".join(ids) + ")"

    async def _resolve_member_ids(self, gid: str, members: List[str]) -> List[str]:
        """把用户填的 wxid / 群昵称解析成守护进程认识的成员 id。"""
        if self.client is None or not members:
            return members
        thread_id = (self.groups.get(gid) or {}).get("thread_id") or _normalize_chatroom(gid)
        curr, _, _ = await self._fetch_members(thread_id)
        if not curr:
            return members
        out: List[str] = []
        for m in members:
            if m in curr:
                out.append(m)
                continue
            hit = next((k for k, v in curr.items() if v == m or m in v), None)
            out.append(hit or m)
        return out

    # ===================================================================
    # 退群 / 入群监控（轮询差比）
    # ===================================================================
    async def _fetch_members(self, thread_id: str):
        """返回 (成员字典, 微信昵称字典, 使用的接口名)。group_lookup 更可靠，优先用。"""
        fetchers = []
        if self.client is not None:
            for name in ("group_lookup", "group_members"):
                fn = getattr(self.client, name, None)
                if fn:
                    fetchers.append((name, fn))
        for name, fn in fetchers:
            try:
                items = await fn(thread_id)
            except Exception as e:
                logger.debug(f"[群管] {name} 拉取失败({thread_id})：{e}")
                continue
            members: Dict[str, str] = {}
            wxnames: Dict[str, str] = {}
            for m in items or []:
                if not isinstance(m, dict):
                    continue
                mid = m.get("id") or m.get("userId") or m.get("username")
                if not mid:
                    continue
                nm = (m.get("roomDisplayName") or m.get("displayName")
                      or m.get("mentionName") or m.get("nickname") or mid)
                members[str(mid)] = str(nm)
                wxnames[str(mid)] = str(m.get("nickname") or m.get("displayName") or nm)
            if members:
                return members, wxnames, name
        return {}, {}, ""

    async def _poll_once(self):
        if self.client is None:
            if not self._warned_no_client:
                logger.warning("[群管] 尚未捕获 wechat_agent 客户端，退群监控暂不可用（请先在群里发一条消息）。")
                self._warned_no_client = True
            return
        self._warned_no_client = False

        leave_tpl = str(self._opts.get("leave_template") or DEFAULT_LEAVE_TEMPLATE)
        join_tpl = str(self._opts.get("join_template") or DEFAULT_JOIN_TEMPLATE)

        for gid in list(self.monitored):
            info = self.groups.get(gid) or {}
            thread_id = info.get("thread_id") or _normalize_chatroom(gid)
            curr, wxnames, source = await self._fetch_members(thread_id)
            if not curr:
                logger.warning(f"[群管] 群 {gid} 成员列表为空，本轮跳过（避免误报全员退群）。")
                continue

            prev = self.snapshots.get(gid)
            prev_wx = self.snapshots_wx.get(gid) or {}
            prev_source = self.snapshot_source.get(gid)
            rebuild = prev is None
            if not rebuild and len(curr) < len(prev) * 0.7:
                # 防线1：名单远小于基线 → 多半是接口截断。整轮跳过：不播报、不更新基线、不动候选。
                logger.warning(
                    f"[群管] 群 {gid} 本轮成员数 {len(curr)} 远少于基线 {len(prev)}，"
                    "疑似接口截断，跳过本轮（不播报不更新基线）。"
                )
                continue
            if not rebuild and prev_source and source and prev_source != source:
                # 修正：守护进程会在 group_lookup / group_members 之间来回切换。
                # 旧逻辑一换来源就重建基线，导致成员变动被吞掉、监控永不报警。
                # 只有两份名单几乎完全不同（接口口径变了）才重建，否则正常差比。
                a, b = set(prev), set(curr)
                overlap = len(a & b) / max(1, len(a | b))
                rebuild = overlap < 0.5
                if not rebuild:
                    logger.debug(
                        f"[群管] 群 {gid} 成员接口由 {prev_source} 切到 {source}，"
                        f"重叠 {overlap:.0%}，按正常差比处理"
                    )
            if rebuild:
                self.snapshots[gid] = curr
                self.snapshots_wx[gid] = wxnames
                self.snapshot_source[gid] = source
                self._pending_diff.pop(gid, None)
                logger.info(f"[群管] 群 {gid} 建立成员基线：{len(curr)} 人（来源 {source}）")
                continue

            left = {w for w in prev if w not in curr}
            joined = {w for w in curr if w not in prev}

            if not left and not joined:
                self._pending_diff.pop(gid, None)
                self.snapshots[gid] = curr
                self.snapshots_wx[gid] = wxnames
                self.snapshot_source[gid] = source
                continue

            pend = self._pending_diff.get(gid) or {}
            confirm_left = set(pend.get("left") or ()) & left
            confirm_joined = set(pend.get("joined") or ()) & joined

            # 防线3：单轮大规模变动（≥30%）不可信（接口口径漂移/截断），拦截不播报；
            # 连续 3 轮仍如此才接受现实、重建基线。
            cap = max(1, int(len(prev) * 0.3))
            if len(confirm_left) >= cap or len(confirm_joined) >= cap:
                hits = int(pend.get("hits") or 0) + 1
                self._pending_diff[gid] = {"left": left, "joined": joined, "hits": hits}
                if hits >= 3:
                    self.snapshots[gid] = curr
                    self.snapshot_source[gid] = source
                    self._pending_diff.pop(gid, None)
                    logger.warning(
                        f"[群管] 群 {gid} 连续 {hits} 轮大规模成员变动"
                        f"（缺 {len(left)}/增 {len(joined)}），接受现实并重建基线 {len(curr)} 人。"
                    )
                else:
                    logger.warning(
                        f"[群管] 群 {gid} 疑似异常差比（缺 {len(left)}/增 {len(joined)}，"
                        f"基线 {len(prev)}），已拦截不播报，待下轮确认。"
                    )
                    self._record_event(
                        gid, info.get("name") or gid, "blocked",
                        f"疑似误报已拦截（缺{len(left)}/增{len(joined)}）", "",
                    )
                continue

            if not confirm_left and not confirm_joined:
                # 防线2：首次发现差比 → 只记候选，下一轮仍缺/仍在才播报（防接口抖动误报）。
                self._pending_diff[gid] = {"left": left, "joined": joined, "hits": 1}
                logger.debug(
                    f"[群管] 群 {gid} 成员变动候选（缺 {len(left)}/增 {len(joined)}），待下轮确认。"
                )
                continue

            gname = info.get("name") or gid
            tvars = _time_vars()
            for w in sorted(confirm_left):
                nick = prev.get(w, w)
                text = self._fmt(leave_tpl, nickname=nick, wxid=w, group=gname,
                                 wxname=prev_wx.get(w, ""), **tvars)
                await self._send_to_group(gid, [Plain(text)])
                logger.info(f"[群管] 退群 -> 群 {gid} / {nick}({w})")
                self._record_event(gid, gname, "leave", nick, w)
            for w in sorted(confirm_joined):
                nick = curr.get(w, w)
                text = self._fmt(join_tpl, nickname=nick, wxid=w, group=gname,
                                 wxname=wxnames.get(w, ""), **tvars)
                await self._send_to_group(gid, [Plain(text)])
                logger.info(f"[群管] 入群 -> 群 {gid} / {nick}({w})")
                self._record_event(gid, gname, "join", nick, w)

            self.snapshots[gid] = curr
            self.snapshots_wx[gid] = wxnames
            self.snapshot_source[gid] = source
            self._pending_diff.pop(gid, None)

    # ===================================================================
    # WebUI 管理页面（views/dashboard）后端 API
    # ===================================================================
    _WEB_API_PREFIX = "/astrbot_plugin_wechat_group_admin"
    # 面板可写配置白名单：type + int 范围（与 _conf_schema.json 保持一致）
    _WEB_SAVE_KEYS = {
        "at_schedules": {"type": "list"},
        "chain_starters": {"type": "list"},
        "monitored_groups": {"type": "list"},
        "leave_template": {"type": "str"},
        "join_template": {"type": "str"},
        "notify_group": {"type": "str"},
        "enable": {"type": "bool"},
        "require_confirm": {"type": "bool"},
        "poll_interval_min": {"type": "int", "min": 1, "max": 60},
        "confirm_ttl_sec": {"type": "int", "min": 10, "max": 600},
        "mutation_wait_sec": {"type": "int", "min": 3, "max": 120},
    }

    def _record_event(self, gid: str, gname: str, etype: str, nick: str, wxid: str):
        """记录退群/入群/拦截事件，供管理页「事件记录」展示。"""
        self._events.append({
            "time": datetime.now().strftime("%Y-%m-%d %H:%M:%S"),
            "group": gname or gid,
            "gid": gid,
            "type": etype,
            "nickname": nick,
            "wxid": wxid,
        })

    def _register_web_apis(self):
        """给 views/dashboard 管理页注册后端 API（前端经 bridge apiGet/apiPost 调用）。"""
        p = self._WEB_API_PREFIX
        try:
            self.context.register_web_api(f"{p}/overview", self.web_overview, ["GET"], "群管-面板总览")
            self.context.register_web_api(f"{p}/events", self.web_events, ["GET"], "群管-事件记录")
            self.context.register_web_api(f"{p}/save", self.web_save, ["POST"], "群管-保存配置")
            self.context.register_web_api(f"{p}/rebuild", self.web_rebuild, ["POST"], "群管-重建成员基线")
            self.context.register_web_api(f"{p}/refresh_groups", self.web_refresh_groups, ["POST"], "群管-从微信刷新群列表")
        except Exception as e:
            logger.warning(f"[群管] 注册 Web API 失败（不影响其它功能）：{e}")

    @staticmethod
    def _ensure_tpl_key(key: str, rule: dict) -> dict:
        """保证 template_list 规则带 __template_key，否则 WebUI 配置面板不识别。"""
        if key == "at_schedules":
            rule.setdefault("__template_key", "at_schedule")
        elif key == "chain_starters":
            rule.setdefault("__template_key", "chain_starter")
        return rule

    async def _refresh_group_names(self) -> int:
        """从守护进程拉真实群列表，把群名写进 self.groups 并持久化（面板下拉用）。"""
        ok, data = await self._read("groups", {"limit": 200})
        if not ok:
            return 0
        n = 0
        for g in self._items(data):
            gid = self._normalize_gid(g.get("id") or g.get("threadId") or "")
            if not gid:
                continue
            name = str(g.get("displayName") or g.get("name") or "").strip()
            info = self.groups.setdefault(
                gid, {"umo": None, "thread_id": _normalize_chatroom(gid), "name": ""}
            )
            if name:
                info["name"] = name
            n += 1
        self._last_groups_fetch = time.time()
        if n:
            try:
                await self.put_kv_data(KV_GROUPS, self.groups)
            except Exception:
                pass
        return n

    async def web_overview(self):
        """GET 面板总览：状态 + 配置列表 + 监控快照概况。"""
        if self.client is not None and time.time() - self._last_groups_fetch > 300:
            try:
                await self._refresh_group_names()   # 面板打开时自动补群名（5 分钟节流）
            except Exception as e:
                logger.debug(f"[群管] 自动刷新群列表失败：{e}")
        monitor = []
        for g in self._monitored_from_config():
            snap = self.snapshots.get(g) or {}
            monitor.append({
                "gid": g,
                "name": (self.groups.get(g) or {}).get("name") or "",
                "baseline": len(snap),
                "source": self.snapshot_source.get(g, ""),
            })
        return json_response({
            "client_ready": self.client is not None,
            "poll_interval_min": self._poll_interval(),
            "notify_group": self._opts.get("notify_group") or "",
            "leave_template": str(self._opts.get("leave_template") or ""),
            "join_template": str(self._opts.get("join_template") or ""),
            "enable": self._opts.get("enable", True) is not False,
            "require_confirm": self._opts.get("require_confirm", True) is not False,
            "confirm_ttl_sec": self._opts.get("confirm_ttl_sec", 60),
            "mutation_wait_sec": self._opts.get("mutation_wait_sec", 30),
            "at_schedules": self._rules(),
            "chain_starters": [dict(x) for x in self._cfg_list("chain_starters")],
            "monitored": monitor,
            "group_options": [str(x) for x in (self._opts.get("group_options") or [])],
            "groups": [
                {"gid": k, "name": (v or {}).get("name") or ""}
                for k, v in self.groups.items()
            ],
            "last_send_error": self._last_send_error,
            "event_count": len(self._events),
        })

    async def web_events(self):
        """GET ?limit=N 最近事件记录（内存环形缓冲，重启清空）。"""
        try:
            limit = max(1, min(int(web_request.query.get("limit", 200) or 200), 500))
        except (TypeError, ValueError):
            limit = 200
        items = list(self._events)[-limit:]
        items.reverse()
        return json_response({"items": items, "total": len(self._events)})

    async def web_save(self):
        """POST {key, value} 白名单配置保存；列表保存后立即重建内存镜像。"""
        body = await web_request.json(default={}) or {}
        key = str(body.get("key") or "")
        spec = self._WEB_SAVE_KEYS.get(key)
        if not spec:
            return json_response({"error": f"不支持的配置键：{key}"}, status_code=400)
        value = body.get("value")
        t = spec["type"]
        if t == "list":
            if not isinstance(value, list):
                return json_response({"error": "value 应为列表"}, status_code=400)
            if key == "monitored_groups":
                self._opts[key] = [str(v).strip() for v in value if str(v or "").strip()]
            else:
                self._opts[key] = [
                    self._ensure_tpl_key(key, dict(x))
                    for x in value if isinstance(x, dict)
                ]
        elif t == "int":
            try:
                value = int(value)
            except (TypeError, ValueError):
                return json_response({"error": "value 应为整数"}, status_code=400)
            self._opts[key] = max(spec.get("min", 1), min(value, spec.get("max", 60)))
        elif t == "bool":
            self._opts[key] = bool(value)
        else:
            self._opts[key] = str(value or "")
        ok = await self._save_config()
        self._load_state_from_config()
        return json_response({"ok": ok, "key": key})

    async def web_rebuild(self):
        """POST {group} 清空指定群成员基线，下一轮轮询重建（修复误报后用）。"""
        body = await web_request.json(default={}) or {}
        gid = self._normalize_gid(body.get("group") or "")
        if not gid:
            return json_response({"error": "缺少 group"}, status_code=400)
        self.snapshots.pop(gid, None)
        self.snapshots_wx.pop(gid, None)
        self.snapshot_source.pop(gid, None)
        self._pending_diff.pop(gid, None)
        logger.info(f"[群管] 已清除群 {gid} 的成员基线，下一轮轮询重建。")
        return json_response({"ok": True, "group": gid})

    async def web_refresh_groups(self):
        """POST 从微信（守护进程）拉群列表，更新群名供面板下拉显示。"""
        if self.client is None:
            return json_response({"error": "客户端未连接"}, status_code=400)
        n = await self._refresh_group_names()
        return json_response({
            "ok": bool(n),
            "count": n,
            "groups": [{"gid": k, "name": (v or {}).get("name") or ""}
                       for k, v in self.groups.items()],
        })

    # ===================================================================
    # 发送
    # ===================================================================
    async def _send_to_group(self, gid: str, chain: List[Any]):
        mc = MessageChain(chain=chain)
        thread_id = (self.groups.get(gid) or {}).get("thread_id") or _normalize_chatroom(gid)
        if self.adapter is not None:
            try:
                await self.adapter.send_chain(thread_id, mc)
            except Exception as e:
                logger.warning(f"[群管] 适配器直发失败，回退标准接口：{e}")
                self._last_send_error = (
                    f"{datetime.now().strftime('%m-%d %H:%M')} 群 {gid} 直发失败：{e}"
                )
                await self._send_via_context(gid, mc)
        else:
            await self._send_via_context(gid, mc)

        if self.notify_group and self.notify_group != gid:
            nth = (self.groups.get(self.notify_group) or {}).get("thread_id") \
                  or _normalize_chatroom(self.notify_group)
            try:
                if self.adapter is not None:
                    await self.adapter.send_chain(nth, mc)
                else:
                    await self._send_via_context(self.notify_group, mc)
            except Exception as e:
                logger.error(f"[群管] 通知群发送失败：{e}")

    async def _send_via_context(self, gid: str, mc: MessageChain):
        info = self.groups.get(gid) or {}
        umo = info.get("umo")
        if not umo:
            logger.warning(f"[群管] 群 {gid} 无会话来源(umo)，无法主动发送；请在该群发一条消息。")
            return
        try:
            await self.context.send_message(umo, mc)
        except Exception as e:
            # 403 mention_all_forbidden 等权限错误以前只写日志，用户以为「没生效」。
            # 记下来，/群管状态 可见。
            self._last_send_error = (
                f"{datetime.now().strftime('%m-%d %H:%M')} 群 {gid}：{e}"
            )
            logger.error(f"[群管] 标准接口发送失败(群 {gid})：{e}")

    @staticmethod
    def _fmt(template: str, **kwargs) -> str:
        def repl(m):
            v = kwargs.get(m.group(1))
            return str(v) if v is not None else m.group(0)
        return re.sub(r"\{(\w+)\}", repl, template or "")

    # ===================================================================
    # 指令
    # ===================================================================
    @filter.command("群管菜单")
    async def menu(self, event: AstrMessageEvent):
        """查看微信群管理插件所有指令"""
        yield event.plain_result(
            "🛠 微信群管理 v1.7.1（仅管理员）\n"
            "【插件管理面板 = 唯一数据源】\n"
            "· ⏰ 定时艾特规则 / 📋 自动发起接龙 / 👥 监控群 / 📇 已发现的群\n"
            "  命令添加的任务会自动回写到面板，可在面板里改/删\n"
            "· 所有 [群id] 可省略：不带=当前群，带=指定群\n"
            "【官方接龙】\n"
            "· /发起接龙 [群id] <标题内容> [| 第一个人]\n"
            "  只发「📋 接龙功能测试：\\n0. 标题内容\\n1. 第一个人」文本，微信显示「参与接龙」\n"
            "  机器人不参与、不统计；成员点按钮自行接龙\n"
            "【只读查询】\n"
            "· /群id　/群列表　/群资料 [群id]　/群成员 [群id]\n"
            "· /联系人 [关键词]　/群管能力　/群管状态\n"
            "【定时提醒】\n"
            "· /添加艾特任务 [群id] <时间> <内容> —— 定时 @全体\n"
            "· /添加艾特成员 [群id] <时间> <成员> <内容> —— 定时 @指定成员\n"
            "· /艾特任务列表 / /删除艾特任务 <序号>\n"
            "· /立即艾特 [群id] <内容> / /立即艾特成员 [群id] <成员> <内容>\n"
            "  时间：09:30 / 09:30,18:00 / mon-fri 09:00 / 1-5 20:00\n"
            "  成员：微信号或群昵称，多个用英文逗号分隔\n"
            "  内容变量：{date} {clock} {time} {weekday} {group}\n"
            "【退群/入群监控】\n"
            "· /监控退群 [群id] / /取消监控退群 [群id] / /退群监控列表\n"
            "· /设置通知群 [群id]\n"
            "【群管理增强 ⚙】\n"
            "· /建群 <成员列表> [群名]　/改群名 [群id] <新群名>\n"
            "· /拉人 [群id] <成员列表>　/踢人 [群id] <成员列表>\n"
            "· /退群 [群id]　/清群公告 [群id]\n"
            "· /改群内昵称 [群id] <昵称>\n"
            "· /置顶会话 [群id] on|off　/免打扰 [群id] on|off\n"
            "· /确认群管　/取消群管（破坏性操作二次确认）\n"
            "  成员列表用英文逗号分隔的 wxid；[] 可省略，默认当前群"
        )

    @filter.command("群id")
    async def get_group_id(self, event: AstrMessageEvent):
        """获取当前群聊的 group id"""
        gid = event.get_group_id()
        if not gid:
            yield event.plain_result("请在群聊中发送此指令。")
            return
        yield event.plain_result(f"当前群ID：{gid}\n（thread_id：{_normalize_chatroom(gid)}）")

    @filter.permission_type(PermissionType.ADMIN)
    @filter.command("发起接龙")
    async def start_official_chain(self, event: AstrMessageEvent):
        """发起官方接龙引子：/发起接龙 [群id] <标题内容> [| 第一个人]"""
        gid, toks = self._split_gid(event, self._strip_command(event, "发起接龙"))
        raw = " ".join(toks).strip()
        if not raw:
            yield event.plain_result(
                "用法：/发起接龙 [群id] <标题内容> [| 第一个人]\n"
                "例：/发起接龙 双十接龙 | 太华红豆糕\n"
                "机器人固定发「📋 接龙功能测试：\\n0. 标题内容\\n1. 第一个人」\n"
                "（标题为实测白名单词，自定义标题放 0. 行；LF 换行、末尾不换行）\n"
                "不带群id = 当前群；成员点「参与接龙」自行接龙。"
            )
            return
        if not gid:
            yield event.plain_result("请在群聊中发送，或附带群id。")
            return
        if "|" in raw:
            topic, first = raw.split("|", 1)
        else:
            topic, first = raw, ""
        topic, first = topic.strip(), first.strip()
        if not topic:
            yield event.plain_result("接龙主题不能为空。")
            return
        ok = await self._send_chain_starter(gid, topic, first)
        if ok:
            yield event.plain_result(
                f"✅ 已发起接龙引子：{topic}\n"
                f"群：{gid}\n内容：{self._chain_starter_text(topic, first)!r}\n"
                "成员在微信里点「参与接龙」即可；机器人不参与、不统计。"
            )
        else:
            yield event.plain_result(
                f"❌ 发送失败，请检查 /群管状态 的最近发送错误。\n"
                f"目标群 {gid} 需先在该群发一条消息以捕获会话。"
            )

    @filter.permission_type(PermissionType.ADMIN)
    @filter.command("群管状态")
    async def status(self, event: AstrMessageEvent):
        """查看插件运行状态"""
        tasks = self._all_tasks()
        all_cnt = sum(1 for t in tasks if t.get("target") != "members")
        mem_cnt = len(tasks) - all_cnt
        lines = [
            f"平台：{event.get_platform_name()}",
            f"客户端：{'已捕获' if self.client else '未捕获（请先在群里发条消息）'}",
            f"直发通道：{'可用' if self.adapter else '不可用'}",
            f"监控群：{len(self.monitored)} 个（面板可视化）",
            f"定时艾特：{len(self._rules())} 条规则 → {len(tasks)} 个时间点"
            f"｜@全体 {all_cnt} / @指定成员 {mem_cnt}",
            f"自动发起接龙：{len(self._config_chain_starters())} 个时间点",
            f"数据源：WebUI 配置面板（命令添加也会回写）",
            f"轮询间隔：{self._poll_interval()} 分钟",
            f"最近发送错误：{self._last_send_error or '无'}",
            f"待确认操作：{len(self._pending)} 个",
            f"二次确认：{'开启' if self._need_confirm() else '关闭'} / 超时 {self._confirm_ttl()} 秒",
            "成员基线：" + (", ".join(f"{g}={len(v)}人" for g, v in self.snapshots.items()) or "无"),
        ]
        yield event.plain_result("\n".join(lines))

    @filter.permission_type(PermissionType.ADMIN)
    @filter.command("群成员")
    async def list_members(self, event: AstrMessageEvent):
        """列出群成员 wxid 与群昵称，供 @指定成员 使用"""
        rest = self._strip_command(event, "群成员").strip()
        gid = self._normalize_gid(rest.split()[0]) \
            if rest and self._looks_like_group_id(rest.split()[0]) \
            else self._resolve_group(event)
        if not gid:
            yield event.plain_result("请在群聊中发送，或附带群id：/群成员 <群id>")
            return
        if self.client is None:
            yield event.plain_result("客户端未就绪，请先在群里发一条消息。")
            return
        thread_id = (self.groups.get(gid) or {}).get("thread_id") or _normalize_chatroom(gid)
        members, source = await self._fetch_members(thread_id)
        if not members:
            yield event.plain_result(f"未取到群 {gid} 的成员列表（守护进程接口返回空）。")
            return
        lines = [f"👥 群 {gid} 成员（{len(members)} 人，来源 {source}）："]
        for i, (mid, nick) in enumerate(members.items(), 1):
            if i > 40:
                lines.append(f"… 其余 {len(members) - 40} 人省略")
                break
            lines.append(f"{i}. {nick}  →  {mid}")
        lines.append("\n填 /添加艾特成员 时，用箭头右侧的 ID 或直接填昵称。")
        yield event.plain_result("\n".join(lines))

    @filter.permission_type(PermissionType.ADMIN)
    @filter.command("监控退群")
    async def add_monitor(self, event: AstrMessageEvent):
        """把群加入退群/入群监控，并同步到 WebUI 配置面板"""
        gid, _ = self._split_gid(event, self._strip_command(event, "监控退群"))
        if not gid:
            yield event.plain_result("请在群聊中发送，或附带群id：/监控退群 <群id>")
            return
        mons = self._monitored_from_config()
        if gid not in mons:
            mons.append(gid)
            self._opts["monitored_groups"] = mons
            ok = await self._save_config()
            self._load_state_from_config()
            if not ok:
                yield event.plain_result("⚠️ 本次运行已生效，但回写配置面板失败，重启后会丢失。")
                return
        self._ensure_group(gid)
        yield event.plain_result(
            f"✅ 已加入退群/入群监控：{gid}\n（已同步到 WebUI 配置面板，可视化管理）"
        )

    @filter.permission_type(PermissionType.ADMIN)
    @filter.command("取消监控退群")
    async def del_monitor(self, event: AstrMessageEvent):
        """取消群的退群/入群监控，并同步到 WebUI 配置面板"""
        gid, _ = self._split_gid(event, self._strip_command(event, "取消监控退群"))
        if not gid:
            yield event.plain_result("用法：/取消监控退群 <群id>")
            return
        mons = self._monitored_from_config()
        if gid in mons:
            mons.remove(gid)
            self._opts["monitored_groups"] = mons
            await self._save_config()
            self.snapshots.pop(gid, None)
            self.snapshot_source.pop(gid, None)
            self._load_state_from_config()
        yield event.plain_result(f"🗑 已取消监控：{gid}（已同步配置面板）")

    @filter.permission_type(PermissionType.ADMIN)
    @filter.command("退群监控列表")
    async def list_monitor(self, event: AstrMessageEvent):
        """查看被监控的群"""
        if not self.monitored:
            yield event.plain_result("当前没有监控任何群。")
            return
        lines = ["📋 退群/入群监控列表："]
        for i, gid in enumerate(self.monitored, 1):
            lines.append(f"{i}. {gid}（基线 {len(self.snapshots.get(gid, {}))} 人）")
        yield event.plain_result("\n".join(lines))

    @filter.permission_type(PermissionType.ADMIN)
    @filter.command("添加艾特任务")
    async def add_schedule(self, event: AstrMessageEvent):
        """定时@全体：/添加艾特任务 [群id] <时间> <内容>"""
        rest = self._strip_command(event, "添加艾特任务")
        gid, time_str, content = self._parse_schedule_args(event, rest)
        yield_msg = await self._create_tasks(gid, time_str, content, "all", [])
        yield event.plain_result(yield_msg)

    @filter.permission_type(PermissionType.ADMIN)
    @filter.command("添加艾特成员")
    async def add_member_schedule(self, event: AstrMessageEvent):
        """定时@指定成员：/添加艾特成员 [群id] <时间> <成员> <内容>"""
        rest = self._strip_command(event, "添加艾特成员")
        gid, time_str, members_str, content = self._parse_member_task_args(event, rest)
        members = [m.strip() for m in members_str.split(",") if m.strip()]
        if not members:
            yield event.plain_result(
                "格式：/添加艾特成员 [群id] <时间> <成员> <内容>\n"
                "成员填微信号或群昵称，多个用英文逗号；用 /群成员 查 ID。"
            )
            return
        msg = await self._create_tasks(gid, time_str, content, "members", members)
        yield event.plain_result(msg)

    async def _create_tasks(self, gid: Optional[str], time_str: str,
                            content: str, target: str, members: List[str]) -> str:
        if not gid:
            return "请在群聊中发送，或在指令里附带群id（用 /群id 查看）。"
        if not time_str or not content:
            return ("格式：/添加艾特任务 [群id] <时间> <内容>\n"
                    "时间例：09:30 / 09:30,18:00 / mon-fri 09:00\n"
                    "内容支持变量：{date} {clock} {time} {weekday} {group}")
        times = self._expand_times(time_str)
        if not times:
            return (f"时间格式无法识别：{time_str}\n"
                    "请用 HH:MM（09:30），多个用英文逗号；不要写成 17.18。")
        gid = self._normalize_gid(gid)
        rules = self._rules()
        made = []
        for hour, minute, dow in times:
            rules.append(self._task_to_rule({
                "group_id": gid, "hour": hour, "minute": minute,
                "day_of_week": dow, "target": target,
                "members": list(members), "content": content,
            }))
            made.append(f"{dow + ' ' if dow else ''}{hour:02d}:{minute:02d}")
        self._opts["at_schedules"] = rules
        ok = await self._save_config()
        self._load_state_from_config()
        self._ensure_group(gid)
        who = "@全体" if target == "all" else "@成员 " + ",".join(members)
        tail = "（已同步到 WebUI 配置面板）" if ok else "⚠️ 回写面板失败，重启后会丢失"
        return (f"✅ 已添加 {len(made)} 个定时任务 {tail}\n"
                f"群：{gid}\n时间：{', '.join(made)}\n目标：{who}\n内容：{content}")

    @filter.permission_type(PermissionType.ADMIN)
    @filter.command("删除艾特任务")
    async def del_schedule(self, event: AstrMessageEvent):
        """删除定时任务：/删除艾特任务 <序号>"""
        rest = self._strip_command(event, "删除艾特任务").strip()
        if not rest.isdigit():
            yield event.plain_result("用法：/删除艾特任务 <序号>（序号见 /艾特任务列表）")
            return
        idx = int(rest) - 1
        rules = self._rules()
        if idx < 0 or idx >= len(rules):
            yield event.plain_result("序号不存在。")
            return
        removed = rules.pop(idx)
        self._opts["at_schedules"] = rules
        await self._save_config()
        self._load_state_from_config()
        who = "@全体" if removed.get("target") != "members" else "@成员"
        yield event.plain_result(
            f"🗑 已删除第 {idx + 1} 条规则：群 {self._normalize_gid(removed.get('group_id'))} @ "
            f"{removed.get('time', '')} [{who}]（已同步配置面板）"
        )

    @filter.permission_type(PermissionType.ADMIN)
    @filter.command("艾特任务列表")
    async def list_schedule(self, event: AstrMessageEvent):
        """查看定时任务"""
        rules = self._rules()
        if not rules:
            yield event.plain_result("当前没有定时任务。")
            return
        lines = ["📋 定时提醒规则（与 WebUI 配置面板一一对应）："]
        wd_names = "一二三四五六日"
        for i, r in enumerate(rules, 1):
            rep = str(r.get("repeat") or "daily").lower()
            if rep == "weekly":
                picked = "".join(wd_names[j] for j, k in enumerate(self._WD_KEYS)
                                 if r.get(k) is True)
                when = f"每周({picked or '未勾选'}) {r.get('time', '')}"
            elif rep == "once":
                when = f"一次 {r.get('time', '')}"
            else:
                when = f"每天 {r.get('time', '')}"
            who = "@成员 " + str(r.get("members") or "") \
                if r.get("target") == "members" else "@全体"
            lines.append(
                f"{i}. 群 {self._normalize_gid(r.get('group_id'))} @ {when} [{who}]"
                f"{' [已停用]' if r.get('enabled') is False else ''}\n"
                f"   └ {r.get('content', '')}"
            )
        lines.append("\n删除用 /删除艾特任务 <序号>；也可直接在 WebUI 面板里改。")
        yield event.plain_result("\n".join(lines))

    @filter.permission_type(PermissionType.ADMIN)
    @filter.command("立即艾特")
    async def at_now(self, event: AstrMessageEvent):
        """立即@全体测试：/立即艾特 [群id] <内容>"""
        rest = self._strip_command(event, "立即艾特")
        gid, content = self._parse_at_now_args(event, rest)
        if not gid or not content:
            yield event.plain_result("用法：/立即艾特 [群id] <内容>")
            return
        self._ensure_group(gid)
        text = self._fmt(content, group=gid, **_time_vars())
        await self._send_to_group(gid, [AtAll(), Plain(text)])
        yield event.plain_result(f"📢 已向群 {gid} 发送 @全体。")

    @filter.permission_type(PermissionType.ADMIN)
    @filter.command("立即艾特成员")
    async def at_members_now(self, event: AstrMessageEvent):
        """立即@指定成员测试：/立即艾特成员 [群id] <成员> <内容>"""
        rest = self._strip_command(event, "立即艾特成员")
        toks = rest.split(maxsplit=2)
        gid = self._resolve_group(event)
        if toks and self._looks_like_group_id(toks[0]):
            gid = self._normalize_gid(toks[0])
            toks = toks[1:]
        members_str = toks[0] if toks else ""
        content = toks[1] if len(toks) > 1 else ""
        members = [m.strip() for m in members_str.split(",") if m.strip()]
        if not gid or not members or not content:
            yield event.plain_result("用法：/立即艾特成员 [群id] <成员> <内容>（成员逗号分隔）")
            return
        self._ensure_group(gid)
        ids = await self._resolve_member_ids(gid, members)
        text = self._fmt(content, group=gid, **_time_vars())
        await self._send_to_group(gid, [At(qq=m) for m in ids] + [Plain(text)])
        yield event.plain_result(f"📢 已向群 {gid} 发送 @成员：{', '.join(ids)}")

    @filter.permission_type(PermissionType.ADMIN)
    @filter.command("设置通知群")
    async def set_notify(self, event: AstrMessageEvent):
        """设置额外接收变动通知的群；带 off/关闭 则清空"""
        gid, toks = self._split_gid(event, self._strip_command(event, "设置通知群"))
        if toks and toks[0].lower() in ("off", "关闭", "clear", "none", "0"):
            gid = None
        self._opts["notify_group"] = self._normalize_gid(gid) or ""
        await self._save_config()
        self.notify_group = self._opts["notify_group"]
        yield event.plain_result(
            f"✅ 变动通知额外发送到：{self.notify_group}"
            if self.notify_group else "🗑 已关闭额外通知群。"
        )

    # ===================================================================
    # 只读查询：群列表 / 群资料 / 联系人 / 守护进程能力
    # ===================================================================
    @filter.permission_type(PermissionType.ADMIN)
    @filter.command("群列表")
    async def list_groups(self, event: AstrMessageEvent):
        """列出守护进程已同步的群及真实群 id"""
        ok, data = await self._read("groups", {"limit": 200})
        if not ok:
            yield event.plain_result(data)
            return
        items = self._items(data)
        if not items:
            yield event.plain_result("守护进程还没同步到任何群。先在微信里打开群聊，稍后重试。")
            return
        lines = [f"👥 已同步群聊（{len(items)} 个）："]
        for i, g in enumerate(items[:60], 1):
            lines.append(f"{i}. {g.get('displayName') or g.get('name') or '(未命名)'}  →  {g.get('id')}")
        if len(items) > 60:
            lines.append(f"… 其余 {len(items) - 60} 个省略")
        lines.append("\n用箭头右侧的 id 填 [群id]；在群聊里可省略 [群id]。")
        yield event.plain_result("\n".join(lines))

    @filter.permission_type(PermissionType.ADMIN)
    @filter.command("群资料")
    async def group_info(self, event: AstrMessageEvent):
        """查看群名称、公告、群主、成员数"""
        gid, _ = self._split_gid(event, self._strip_command(event, "群资料"))
        if not gid:
            yield event.plain_result("用法：/群资料 [群id]（在群聊里可省略群id）")
            return
        tid = _normalize_chatroom(gid)
        ok, data = await self._read(f"groups/{tid}")
        if not ok:
            yield event.plain_result(data)
            return
        g = data if isinstance(data, dict) else {}
        members, source = await self._fetch_members(tid)
        lines = [
            f"📇 群资料：{g.get('displayName') or g.get('name') or '(未命名)'}",
            f"群 id：{g.get('id') or tid}",
            f"群主：{g.get('ownerId') or '未知'}",
            f"公告：{str(g.get('announcement') or '（空）')[:200]}",
            f"成员：{len(members)} 人" + (f"（来源 {source}）" if source else "（接口返回空）"),
        ]
        yield event.plain_result("\n".join(lines))

    @filter.permission_type(PermissionType.ADMIN)
    @filter.command("联系人")
    async def list_contacts(self, event: AstrMessageEvent):
        """按关键词查已同步联系人的 wxid（建群/拉人用）"""
        kw = self._strip_command(event, "联系人").strip()
        ok, data = await self._read("contacts", {"limit": 500})
        if not ok:
            yield event.plain_result(data)
            return
        items = self._items(data)
        if kw:
            low = kw.lower()
            items = [c for c in items if low in " ".join(
                str(c.get(k) or "") for k in
                ("displayName", "nickname", "remark", "alias", "id", "username")
            ).lower()]
        if not items:
            yield event.plain_result(f"没有匹配到联系人" + (f"（关键词：{kw}）" if kw else "") + "。")
            return
        lines = [f"📒 联系人（{len(items)} 条" + (f"，关键词「{kw}」" if kw else "") + "）："]
        for i, c in enumerate(items[:40], 1):
            label = c.get("remark") or c.get("displayName") or c.get("nickname") or c.get("id")
            lines.append(f"{i}. {label}  →  {c.get('id') or c.get('username')}")
        if len(items) > 40:
            lines.append(f"… 其余 {len(items) - 40} 条省略")
        lines.append("\n注：只显示守护进程已同步的联系人；建群/拉人请填箭头右侧的 wxid。")
        yield event.plain_result("\n".join(lines))

    @filter.permission_type(PermissionType.ADMIN)
    @filter.command("群管能力")
    async def show_capabilities(self, event: AstrMessageEvent):
        """查看守护进程当前开放的群变更能力与权限范围"""
        ok, cap = await self._read("capabilities")
        if not ok:
            yield event.plain_result(cap)
            return
        c = cap if isinstance(cap, dict) else {}
        lines = [
            "🔌 agent-wechat 守护进程能力",
            f"群变更权限范围：{c.get('groupMutationScope', '未知')}（admin=仅群主/管理员）",
            f"建群最少成员：{c.get('groupCreateMinSelectedMembers', '?')} 人",
            f"单次变更最多成员：{c.get('groupMutationMaxSelectedMembers', '?')} 人",
            "支持的群变更：" + (", ".join(c.get("groupMutations") or []) or "无"),
            f"置顶权限范围：{c.get('threadPinningScope', '未知')}",
            "免打扰目标：" + (", ".join(c.get("threadNotificationTargets") or []) or "无"),
            f"原生运行时：{'是' if c.get('nativeRuntime') else '否'}",
            "\n若 scope=admin 而机器人不是群主/管理员，操作会被守护进程拒绝。",
        ]
        yield event.plain_result("\n".join(lines))

    # ===================================================================
    # 群管理增强：建群 / 改群名 / 拉人 / 踢人 / 退群 / 清公告 /
    #             改群内昵称 / 置顶 / 免打扰
    # ===================================================================
    @filter.permission_type(PermissionType.ADMIN)
    @filter.command("建群")
    async def create_group(self, event: AstrMessageEvent):
        """建群：/建群 <成员列表> [群名]（成员 2~40 个 wxid，逗号分隔）"""
        rest = self._strip_command(event, "建群").strip()
        toks = rest.split(maxsplit=1)
        members = self._parse_members([toks[0] if toks else ""])
        name = (toks[1] if len(toks) > 1 else "").strip()
        if name.startswith("群名="):
            name = name[3:].strip()
        if len(members) < 2 or len(members) > 40:
            yield event.plain_result(
                "用法：/建群 <成员列表> [群名]\n"
                "成员列表为 2~40 个 wxid，用英文逗号分隔；群名可选。\n"
                "例：/建群 wxid_a,wxid_b,wxid_c 项目讨论组\n"
                "wxid 可用 /联系人 或 /群成员 查询。"
            )
            return
        ids = await self._resolve_target_ids(members, self._resolve_group(event))
        body: Dict[str, Any] = {"members": ids}
        if name:
            body["name"] = name
        yield event.plain_result(await self._dispatch(
            event, label=f"建群（{len(ids)} 人）" + (f" → {name}" if name else ""),
            method="POST", suffix="groups", body=body, dangerous=False,
            detail="",
        ))

    @filter.permission_type(PermissionType.ADMIN)
    @filter.command("改群名")
    async def rename_group(self, event: AstrMessageEvent):
        """改群名：/改群名 [群id] <新群名>"""
        gid, toks = self._split_gid(event, self._strip_command(event, "改群名"))
        name = " ".join(toks).strip()
        if not gid or not name:
            yield event.plain_result("用法：/改群名 [群id] <新群名>（在群聊里可省略群id）")
            return
        yield event.plain_result(await self._mutate(
            "PATCH", f"groups/{_normalize_chatroom(gid)}", {"name": name},
            f"改群名 → {name}",
        ))

    @filter.permission_type(PermissionType.ADMIN)
    @filter.command("拉人")
    async def add_members(self, event: AstrMessageEvent):
        """拉人：/拉人 [群id] <成员列表>"""
        gid, toks = self._split_gid(event, self._strip_command(event, "拉人"))
        members = self._parse_members(toks)
        if not gid or not members:
            yield event.plain_result(
                "用法：/拉人 [群id] <成员列表>\n"
                "成员为 wxid，多个用英文逗号分隔；用 /联系人 查 wxid。"
            )
            return
        ids = await self._resolve_target_ids(members, gid)
        yield event.plain_result(await self._mutate(
            "POST", f"groups/{_normalize_chatroom(gid)}/members", {"members": ids},
            f"拉人（{len(ids)} 人）",
        ))

    @filter.permission_type(PermissionType.ADMIN)
    @filter.command("踢人")
    async def remove_members(self, event: AstrMessageEvent):
        """踢人：/踢人 [群id] <成员列表>（需二次确认）"""
        gid, toks = self._split_gid(event, self._strip_command(event, "踢人"))
        members = self._parse_members(toks)
        if not gid or not members:
            yield event.plain_result(
                "用法：/踢人 [群id] <成员列表>\n"
                "成员填 wxid 或群昵称，多个用英文逗号分隔；用 /群成员 查。"
            )
            return
        ids = await self._resolve_target_ids(members, gid)
        yield event.plain_result(await self._dispatch(
            event, label=f"踢人（{len(ids)} 人）",
            method="DELETE", suffix=f"groups/{_normalize_chatroom(gid)}/members",
            body={"members": ids}, dangerous=True,
            detail=f"目标群：{gid}\n将移出：{', '.join(ids)}",
        ))

    @filter.permission_type(PermissionType.ADMIN)
    @filter.command("退群")
    async def leave_group(self, event: AstrMessageEvent):
        """退群：/退群 [群id]（需二次确认）"""
        gid, _ = self._split_gid(event, self._strip_command(event, "退群"))
        if not gid:
            yield event.plain_result("用法：/退群 [群id]（在群聊里可省略群id）")
            return
        yield event.plain_result(await self._dispatch(
            event, label="退群", method="POST",
            suffix=f"groups/{_normalize_chatroom(gid)}/leave", body={}, dangerous=True,
            detail=f"目标群：{gid}\n机器人将退出该群，且无法自动加回。",
        ))

    @filter.permission_type(PermissionType.ADMIN)
    @filter.command("清群公告")
    async def clear_announcement(self, event: AstrMessageEvent):
        """清群公告：/清群公告 [群id]（需二次确认）"""
        gid, _ = self._split_gid(event, self._strip_command(event, "清群公告"))
        if not gid:
            yield event.plain_result("用法：/清群公告 [群id]（在群聊里可省略群id）")
            return
        yield event.plain_result(await self._dispatch(
            event, label="清群公告", method="DELETE",
            suffix=f"groups/{_normalize_chatroom(gid)}/announcement", body={}, dangerous=True,
            detail=f"目标群：{gid}\n群公告将被清空，且无法自动恢复。",
        ))

    @filter.permission_type(PermissionType.ADMIN)
    @filter.command("改群内昵称")
    async def set_my_name(self, event: AstrMessageEvent):
        """改我在群内的昵称：/改群内昵称 [群id] <昵称>"""
        gid, toks = self._split_gid(event, self._strip_command(event, "改群内昵称"))
        name = " ".join(toks).strip()
        if not gid or not name:
            yield event.plain_result("用法：/改群内昵称 [群id] <昵称>")
            return
        yield event.plain_result(await self._mutate(
            "PUT", f"groups/{_normalize_chatroom(gid)}/my-name",
            {"displayName": name}, f"改群内昵称 → {name}",
        ))

    @filter.permission_type(PermissionType.ADMIN)
    @filter.command("置顶会话")
    async def pin_thread(self, event: AstrMessageEvent):
        """置顶：/置顶会话 [群id] on|off"""
        gid, toks = self._split_gid(event, self._strip_command(event, "置顶会话"))
        flag = toks[-1] if toks else ""
        if not gid or not (_RE_ON.match(flag) or _RE_OFF.match(flag)):
            yield event.plain_result("用法：/置顶会话 [群id] on|off（也可用 开/关）")
            return
        pinned = bool(_RE_ON.match(flag))
        yield event.plain_result(await self._mutate(
            "PUT", f"threads/{_normalize_chatroom(gid)}/pin",
            {"pinned": pinned}, f"{'置顶' if pinned else '取消置顶'}会话",
        ))

    @filter.permission_type(PermissionType.ADMIN)
    @filter.command("免打扰")
    async def mute_thread(self, event: AstrMessageEvent):
        """免打扰：/免打扰 [群id] on|off"""
        gid, toks = self._split_gid(event, self._strip_command(event, "免打扰"))
        flag = toks[-1] if toks else ""
        if not gid or not (_RE_ON.match(flag) or _RE_OFF.match(flag)):
            yield event.plain_result("用法：/免打扰 [群id] on|off（也可用 开/关）")
            return
        muted = bool(_RE_ON.match(flag))
        yield event.plain_result(await self._mutate(
            "PUT", f"threads/{_normalize_chatroom(gid)}/notifications",
            {"muted": muted}, f"{'开启' if muted else '关闭'}免打扰",
        ))

    # ---- 二次确认 -------------------------------------------------------
    @filter.permission_type(PermissionType.ADMIN)
    @filter.command("确认群管")
    async def confirm_mutation(self, event: AstrMessageEvent):
        """确认上一条破坏性群管理指令"""
        sender = self._sender_key(event)
        p = self._pending.pop(sender, None)
        if not p:
            yield event.plain_result("当前没有待确认的群管理操作。")
            return
        if time.time() - p["ts"] > self._confirm_ttl():
            yield event.plain_result("⏰ 确认已超时，操作自动取消，请重新发送原指令。")
            return
        yield event.plain_result(await self._mutate(
            p["method"], p["suffix"], p["body"], p["label"]
        ))

    @filter.permission_type(PermissionType.ADMIN)
    @filter.command("取消群管")
    async def cancel_mutation(self, event: AstrMessageEvent):
        """撤销待确认的群管理指令"""
        had = self._pending.pop(self._sender_key(event), None)
        yield event.plain_result("🗑 已取消待确认的群管理操作。" if had else "当前没有待确认的操作。")

    # ===================================================================
    # daemon REST 封装
    # ===================================================================
    def _api(self, suffix: str) -> str:
        """拼出 v1/accounts/<id>/<suffix>；优先复用客户端自带的 _acc。"""
        if self.client is None:
            raise RuntimeError("client not ready")
        try:
            return self.client._acc(suffix)
        except Exception:
            acc = getattr(self.client, "account_id", None)
            if not acc:
                raise RuntimeError("daemon account not resolved")
            return f"v1/accounts/{acc}/{suffix.lstrip('/')}"

    async def _read(self, suffix: str, params: Optional[dict] = None):
        """只读 GET，返回 (是否成功, 数据或错误文案)。"""
        if self.client is None:
            return False, "❌ 客户端未就绪：请先在群聊里发一条消息，让插件捕获 wechat_agent 客户端。"
        try:
            return True, await self.client.request(
                "GET", self._api(suffix), params=params, timeout=15
            )
        except Exception as e:
            return False, self._explain_error(e)

    async def _mutate(self, method: str, suffix: str,
                      body: Optional[dict], label: str) -> str:
        """执行一次群变更；自动带 Idempotency-Key 并轮询 operation 到终态。"""
        if self.client is None:
            return "❌ 客户端未就绪：请先在群聊里发一条消息，让插件捕获 wechat_agent 客户端。"
        key = uuid.uuid4().hex
        try:
            resp = await self.client.request(
                method, self._api(suffix), json_body=body,
                headers={"Idempotency-Key": key}, timeout=20,
            )
        except Exception as e:
            logger.warning(f"[群管] 群变更失败 {method} {suffix}：{e}")
            return self._explain_error(e)

        op_id, state = self._extract_operation(resp)
        if not op_id:
            extra = ""
            if isinstance(resp, dict):
                rid = str(resp.get("id") or "")
                nested = resp.get("group")
                if isinstance(nested, dict) and nested.get("id"):
                    rid = str(nested["id"])
                if rid:
                    extra = f"\n返回对象ID：{rid}"
            return (f"✅ {label}：守护进程已受理（未返回操作ID）。{extra}\n"
                    f"幂等键 {key[:8]}…；请用 /群资料 或 /群成员 核对结果。")
        ok, final = await self._poll_operation(op_id, state)
        if ok is True:
            return f"✅ {label} 执行成功。{self._operation_detail(final, op_id)}"
        if ok is False:
            reason = self._operation_reason(final)
            return (f"❌ {label} 执行失败（状态 {state or '未知'}）。"
                    + (f"\n{reason}" if reason else "")
                    + f"\n操作ID：{op_id}")
        return (f"⏳ {label} 已提交，但 {int(self._mutation_wait())} 秒内未收到终态。\n"
                f"操作ID：{op_id}\n可能仍在微信端排队，稍后用 /群资料 或 /群成员 核对。")

    async def _poll_operation(self, op_id: str, state: str):
        """轮询 GET operations/{id}，返回 (True成功/False失败/None超时, 最后的 operation)。"""
        deadline = asyncio.get_event_loop().time() + self._mutation_wait()
        delay, op = 0.4, {}
        while True:
            s = str(state or "").lower()
            if s in _MUTATION_OK_STATES:
                return True, op
            if s in _MUTATION_FAIL_STATES:
                return False, op
            if asyncio.get_event_loop().time() >= deadline:
                return None, op
            await asyncio.sleep(delay)
            delay = min(delay * 1.6, 2.0)
            try:
                op = await self.client.operation(op_id)
            except Exception as e:
                logger.debug(f"[群管] 查询 operation {op_id} 失败：{e}")
                return None, op
            if not isinstance(op, dict):
                op = {}
            state = op.get("state") or op.get("status") or ""

    async def _dispatch(self, event: AstrMessageEvent, *, label: str, method: str,
                        suffix: str, body: Optional[dict],
                        dangerous: bool, detail: str) -> str:
        """破坏性操作先入待确认队列，其余直接执行。"""
        if dangerous and self._need_confirm():
            return self._queue_confirm(event, label, method, suffix, body, detail)
        return await self._mutate(method, suffix, body, label)

    def _queue_confirm(self, event: AstrMessageEvent, label: str, method: str,
                       suffix: str, body: Optional[dict], detail: str) -> str:
        self._pending[self._sender_key(event)] = {
            "ts": time.time(), "label": label, "method": method,
            "suffix": suffix, "body": body,
        }
        return ("⚠️ 待确认操作\n"
                f"操作：{label}\n"
                + (detail + "\n" if detail else "")
                + f"请在 {self._confirm_ttl()} 秒内发送 /确认群管 执行，"
                  "或 /取消群管 撤销。\n（仅本人可确认，超时自动作废）")

    async def _resolve_target_ids(self, members: List[str],
                                  gid: Optional[str]) -> List[str]:
        """群成员表 + 联系人表一起把昵称解析成 wxid；解析不到就原样保留。"""
        pool: Dict[str, str] = {}
        if gid:
            roster, _ = await self._fetch_members(_normalize_chatroom(gid))
            pool.update(roster)
        ok, data = await self._read("contacts", {"limit": 500})
        if ok:
            for c in self._items(data):
                cid = c.get("id") or c.get("username")
                if cid:
                    pool.setdefault(
                        str(cid),
                        str(c.get("remark") or c.get("displayName")
                            or c.get("nickname") or cid),
                    )
        out: List[str] = []
        for m in members:
            if m in pool:
                out.append(m)
                continue
            hit = next((k for k, v in pool.items() if v and (v == m or m in v)), None)
            out.append(hit or m)
        return out

    def _explain_error(self, e: Exception) -> str:
        code = str(getattr(e, "code", "") or "")
        status = getattr(e, "status", None)
        if not code:
            m = re.search(r"HTTP\s+\d+\s+([a-z_]+)", str(e))
            code = m.group(1) if m else ""
        hint = _MUTATION_ERROR_HINTS.get(code)
        head = (f"❌ 操作失败（HTTP {status} / {code or '未知错误'}）" if status
                else f"❌ 操作失败（{code or '未知错误'}）")
        return head + ("\n" + hint if hint else "") + f"\n原始信息：{str(e)[:160]}"

    def _need_confirm(self) -> bool:
        v = self._opts.get("require_confirm", True)
        return v is not False and str(v).lower() not in ("false", "0", "no", "off")

    def _confirm_ttl(self) -> int:
        try:
            return max(10, min(int(self._opts.get("confirm_ttl_sec", 60) or 60), 600))
        except (TypeError, ValueError):
            return 60

    def _mutation_wait(self) -> float:
        try:
            return float(max(3, min(int(self._opts.get("mutation_wait_sec", 30) or 30), 120)))
        except (TypeError, ValueError):
            return 30.0

    @staticmethod
    def _items(data) -> List[dict]:
        if isinstance(data, dict):
            return [x for x in (data.get("items") or []) if isinstance(x, dict)]
        if isinstance(data, list):
            return [x for x in data if isinstance(x, dict)]
        return []

    @staticmethod
    def _extract_operation(resp) -> Tuple[str, str]:
        """兼容 {operation:{...}} / {operationId,state} / {id,state} 三种回执形态。"""
        if not isinstance(resp, dict):
            return "", ""
        nested = resp.get("operation")
        if isinstance(nested, dict):
            return (str(nested.get("id") or resp.get("operationId") or ""),
                    str(nested.get("state") or nested.get("status")
                        or resp.get("state") or ""))
        oid = resp.get("operationId") or resp.get("operation_id") or ""
        if not oid and "id" in resp and any(k in resp for k in ("state", "status", "kind")):
            oid = resp.get("id")
        return str(oid or ""), str(resp.get("state") or resp.get("status") or "")

    @staticmethod
    def _operation_detail(op, op_id: str) -> str:
        gid = ""
        if isinstance(op, dict):
            r = op.get("result") or op.get("data") or {}
            if isinstance(r, dict):
                gid = str(r.get("groupId") or "")
                if not gid and isinstance(r.get("group"), dict):
                    gid = str(r["group"].get("id") or "")
        return (f"关联群ID：{gid}  " if gid else "") + f"操作ID：{op_id}"

    @staticmethod
    def _operation_reason(op) -> str:
        if not isinstance(op, dict):
            return ""
        err = op.get("error") or op.get("failure") or op.get("reason") or ""
        if isinstance(err, dict):
            code = str(err.get("code") or "")
            msg = str(err.get("message") or "")
            hint = _MUTATION_ERROR_HINTS.get(code, "")
            return " ".join(x for x in (code, msg, hint) if x).strip()
        return str(err)[:200]

    @staticmethod
    def _sender_key(event: AstrMessageEvent) -> str:
        for name in ("get_sender_id", "get_sender_name"):
            fn = getattr(event, name, None)
            if callable(fn):
                try:
                    v = fn()
                    if v:
                        return str(v)
                except Exception:
                    pass
        return str(getattr(event, "unified_msg_origin", "") or "unknown")

    # ===================================================================
    # 辅助
    # ===================================================================
    def _split_gid(self, event: AstrMessageEvent, rest: str) -> Tuple[Optional[str], List[str]]:
        """统一群目标解析：不带群id=当前群，带群id=指定群（支持 UMO 格式）。

        所有命令都走这里，避免出现「写了群id却只作用当前群」。
        """
        toks = rest.split()
        gid = self._resolve_group(event)
        if toks and self._looks_like_group_id(toks[0]):
            gid = self._normalize_gid(toks[0])
            toks = toks[1:]
        return self._normalize_gid(gid) or None, toks

    @staticmethod
    def _parse_members(toks: List[str]) -> List[str]:
        out: List[str] = []
        for m in re.split(r"[,，、\s]+", " ".join(toks)):
            m = m.strip()
            if m and m not in out:
                out.append(m)
        return out

    def _ensure_group(self, gid: str):
        self.groups.setdefault(gid, {"umo": None}).setdefault(
            "thread_id", _normalize_chatroom(gid)
        )

    @staticmethod
    def _strip_command(event: AstrMessageEvent, cmd: str) -> str:
        s = re.sub(r"^/+", "", (event.message_str or "").strip())
        if s.lower().startswith(cmd):
            s = s[len(cmd):]
        return s.strip()

    @classmethod
    def _resolve_group(cls, event: AstrMessageEvent) -> Optional[str]:
        return cls._normalize_gid(event.get_group_id()) or None

    @staticmethod
    def _looks_like_group_id(s: str) -> bool:
        """群 id 常见形态：xxx@chatroom / 完整 UMO / 较长的纯数字。"""
        s = str(s or "")
        return ("@" in s and (":" in s or s.endswith("@chatroom"))) \
            or (s.isdigit() and len(s) >= 5)

    def _parse_schedule_args(self, event: AstrMessageEvent, rest: str):
        """解析 [群id] <时间> <内容>。修正：'mon-fri 09:00' 不能被误当群id。"""
        toks = rest.split()
        gid = self._resolve_group(event)
        if not toks:
            return gid, "", ""
        if self._looks_like_group_id(toks[0]):
            gid = self._normalize_gid(toks[0])
            toks = toks[1:]
            if not toks:
                return gid, "", ""
        if len(toks) >= 2 and _RE_DOW_ONLY.match(toks[0]) and _RE_TIME_ONLY.match(toks[1]):
            return gid, f"{toks[0]} {toks[1]}", " ".join(toks[2:])
        return gid, toks[0], " ".join(toks[1:])

    def _parse_member_task_args(self, event: AstrMessageEvent, rest: str):
        """解析 [群id] <时间> <成员> <内容>。"""
        toks = rest.split()
        gid = self._resolve_group(event)
        if not toks:
            return gid, "", "", ""
        if self._looks_like_group_id(toks[0]):
            gid = self._normalize_gid(toks[0])
            toks = toks[1:]
            if not toks:
                return gid, "", "", ""
        if len(toks) >= 2 and _RE_DOW_ONLY.match(toks[0]) and _RE_TIME_ONLY.match(toks[1]):
            time_str = f"{toks[0]} {toks[1]}"
            toks = toks[2:]
        else:
            time_str = toks[0] if toks else ""
            toks = toks[1:]
        members = toks[0] if toks else ""
        content = " ".join(toks[1:]) if len(toks) > 1 else ""
        return gid, time_str, members, content

    def _parse_at_now_args(self, event: AstrMessageEvent, rest: str):
        toks = rest.split(maxsplit=1)
        gid = self._resolve_group(event)
        if toks and self._looks_like_group_id(toks[0]):
            gid = self._normalize_gid(toks[0])
            toks = toks[1:]
        return gid, (toks[0] if toks else "")

    @classmethod
    def _expand_times(cls, time_str: str) -> List[Tuple[int, int, Optional[str]]]:
        """支持 09:30 / 09:30,18:00 / mon-fri 09:00,18:00。"""
        parts = time_str.strip().split()
        if len(parts) >= 2 and _RE_DOW_ONLY.match(parts[0]):
            dow, time_part = parts[0], parts[1]
        else:
            dow, time_part = None, (parts[0] if parts else "")
        out: List[Tuple[int, int, Optional[str]]] = []
        for t in time_part.split(","):
            h, m, _ = cls._parse_time(t.strip())
            if h is None or not (0 <= h <= 23) or not (0 <= m <= 59):
                continue
            out.append((h, m, dow))
        return out

    @staticmethod
    def _looks_like_time(s: str) -> bool:
        return bool(_RE_TIME_ONLY.match(s) or _RE_TIME_DOW.match(s))

    @classmethod
    def _parse_time(cls, s: str):
        m = _RE_TIME_DOW.match(s.strip())
        if m:
            return int(m.group(2)), int(m.group(3)), m.group(1)
        m = _RE_TIME_ONLY.match(s.strip())
        if m:
            return int(m.group(1)), int(m.group(2)), None
        return None, None, None
