# -*- coding: utf-8 -*-
"""
消消乐（Match-3）—— Python + pygame 实现
==========================================
玩法（与市面常见消消乐一致）：
  * 交换相邻糖果，凑成 3 个及以上同色即可消除，无效交换自动换回
  * 消除后糖果下落、新糖果补充，连锁消除有连击倍数
  * 四连出条纹糖（消整行/整列），T/L 拐角出炸弹糖（3x3），五连出彩虹糖
  * 特效糖之间可组合：条纹+条纹 / 条纹+炸弹 / 炸弹+炸弹 / 彩虹+任意
  * 关卡制：限定步数内达到目标分数即过关，无解自动洗牌
操作：
  * 鼠标点选两颗相邻糖果交换，或按住糖果拖动交换
  * 底部按钮：重开本关 / 提示 / 音效开关

运行：python match3.py        （依赖：pygame，安装命令 pip install pygame）
"""

import os
import sys
import math
import json
import wave
import struct
import random
import socket
import queue
import threading
from io import BytesIO

try:
    import pygame
except ImportError:
    sys.stderr.write("缺少 pygame 库，请先安装：pip install pygame\n")
    raise

# ==================== 全局常量 ====================
COLS, ROWS = 8, 8          # 棋盘列数 / 行数
TYPES = 6                  # 元素（动物）种类
CELL = 54                  # 每格像素尺寸（格间留空隙）
TILE = 48                  # 元素显示尺寸
WIN_W, WIN_H = 480, 720    # 窗口尺寸
BOARD_X = (WIN_W - COLS * CELL) // 2
BOARD_Y = 168
FPS = 60

IMAGE_DIR = os.path.join(os.path.dirname(os.path.abspath(__file__)), "image")

# 六种元素的代表色（用于消除粒子），与动物图片主色一致：
# 熊 / 鸡 / 狐狸 / 青蛙 / 河马 / 猫头鹰
TYPE_COLORS = [
    ((214, 120,  50), (150,  72,  20)),  # 棕熊
    ((255, 221,  70), (190, 140,   0)),  # 黄鸡
    ((235,  90,  50), (160,  45,  20)),  # 红狐
    (( 90, 200,  90), ( 30, 130,  50)),  # 绿蛙
    (( 90, 200, 230), ( 30, 130, 170)),  # 蓝河马
    ((150,  90, 200), ( 90,  40, 140)),  # 紫猫头鹰
]

# ===== 柔和糖果色盘（暖色渐变基调 + 圆润轻快）=====
BG_TOP = (255, 236, 210)         # 背景渐变顶：奶油橙
BG_BOTTOM = (255, 183, 200)      # 背景渐变底：樱花粉
BOARD_BG = (255, 251, 245)       # 棋盘底：奶白
BOARD_EDGE = (233, 160, 130)     # 棋盘描边：暖棕粉
PANEL_LIGHT = (255, 255, 255)    # 浅色面板底
PANEL_SH = (225, 185, 190)       # 面板底部阴影
TEXT_DARK = (150, 80, 70)        # 主文字：暖棕红
TEXT_SOFT = (205, 150, 140)      # 次要文字
WHITE = (255, 255, 255)
RED = (255, 107, 107)            # 重开按钮 / 步数
PURPLE_BTN = (156, 126, 240)     # 主按钮
PROGRESS_RED = (255, 122, 89)    # 进度填充
PROGRESS_BG = (240, 225, 228)    # 进度槽底
SELECT_COLOR = (255, 196, 60)    # 选中框：暖黄
HINT_COLOR = (90, 200, 255)      # 提示框：天青

STATE_MENU = "menu"
STATE_PLAY = "play"
STATE_OVER = "over"
STATE_LAN = "lan"            # 局域网对战连接界面

LAN_PORT = 50007             # 局域网对战 TCP 端口
PK_DURATION = 90             # 默认对战时长（秒）
DURATION_PRESETS = (60, 90, 120, 180)   # 主机可选时长（秒）

# ---- 干扰道具 ----
MAX_ITEM_USES = 5            # 每人每局道具使用上限
ENERGY_MAX = 1000            # 能量槽上限（满一格可使用一个道具）
ENERGY_PER_GEM = 45          # 每消除一个糖果获得的能量
ENERGY_SPECIAL = 120         # 消除特效糖额外能量
FOG_MS = 3000                # 迷雾持续
PAPER_MS = 3000              # 糖纸持续
IMP_MS = 2500                # 小鬼预警时长（随后炸乱 3x3）

# (key, 名称, 主题色)，道具槽顺序
ITEM_DEFS = [("fog", "迷雾", (190, 195, 215)),
             ("jelly", "果冻", (255, 150, 90)),
             ("imp", "小鬼", (170, 90, 220)),
             ("paper", "糖纸", (255, 190, 215)),
             ("shield", "护盾", (90, 180, 255))]
ITEM_KEYS = [d[0] for d in ITEM_DEFS]
ITEM_NAMES = {k: n for k, n, _ in ITEM_DEFS}


# ==================== 缓动函数 ====================
def ease_linear(t):
    return t


def ease_in_out(t):
    return 2 * t * t if t < 0.5 else 1 - (-2 * t + 2) ** 2 / 2


def ease_out_bounce(t):
    n1, d1 = 7.5625, 2.75
    if t < 1 / d1:
        return n1 * t * t
    if t < 2 / d1:
        t -= 1.5 / d1
        return n1 * t * t + 0.75
    if t < 2.5 / d1:
        t -= 2.25 / d1
        return n1 * t * t + 0.9375
    t -= 2.625 / d1
    return n1 * t * t + 0.984375


# ==================== 补间动画 ====================
class Tween:
    """在 dur 秒内持续调用 fn(eased_t)；支持 delay 秒延迟启动。"""

    def __init__(self, dur, fn, ease=ease_linear, delay=0.0):
        self.dur = max(0.001, dur)
        self.fn = fn
        self.ease = ease
        self.delay = delay
        self.t = 0.0
        self.done = False

    def update(self, dt):
        self.t += dt
        if self.t < self.delay:
            return False
        k = min(1.0, (self.t - self.delay) / self.dur)
        self.fn(self.ease(k))
        if k >= 1.0:
            self.done = True
        return self.done


# ==================== 糖果数据 ====================
class Gem:
    __slots__ = ("type", "r", "c", "x", "y", "special", "scale", "alpha")

    def __init__(self, r, c, gtype):
        self.type = gtype
        self.r = r
        self.c = c
        self.x = cell_cx(c)
        self.y = cell_cy(r)
        self.special = None       # None / 'stripedH' / 'stripedV' / 'bomb' / 'rainbow'
        self.scale = 1.0
        self.alpha = 1.0


def cell_cx(c):
    return BOARD_X + c * CELL + CELL / 2


def cell_cy(r):
    return BOARD_Y + r * CELL + CELL / 2


def in_bounds(r, c):
    return 0 <= r < ROWS and 0 <= c < COLS


# ==================== 音效（无外部文件，实时合成） ====================
class SoundManager:
    SR = 22050

    def __init__(self):
        self.on = True
        self.ok = False
        self.cache = {}
        try:
            pygame.mixer.init(frequency=self.SR, size=-16, channels=2)
            self.ok = True
        except pygame.error:
            self.ok = False  # 没有音频设备时静默降级

    def _build(self, name, notes):
        """notes: [(频率, 起始秒, 时长秒, 波形, 音量), ...] 合成为一个 Sound。"""
        if name in self.cache:
            return self.cache[name]
        total = max(s + d for _, s, d, _, _ in notes) + 0.05
        n = int(self.SR * total)
        samples = [0.0] * n
        for freq, start, dur, kind, vol in notes:
            i0 = int(start * self.SR)
            cnt = int(dur * self.SR)
            for i in range(cnt):
                t = i / self.SR
                ph = 2 * math.pi * freq * t
                if kind == "sine":
                    v = math.sin(ph)
                elif kind == "tri":
                    v = (2 / math.pi) * math.asin(math.sin(ph))
                else:  # saw
                    v = 2 * ((freq * t) % 1) - 1
                env = math.exp(-t * (math.log(1000) / dur))  # 指数衰减
                idx = i0 + i
                if idx < n:
                    samples[idx] += v * env * vol
        data = bytearray()
        for v in samples:
            v = max(-1.0, min(1.0, v))
            data += struct.pack("<h", int(v * 32767))
        buf = BytesIO()
        wf = wave.open(buf, "wb")
        wf.setnchannels(1)
        wf.setsampwidth(2)
        wf.setframerate(self.SR)
        wf.writeframes(bytes(data))
        wf.close()
        buf.seek(0)
        snd = pygame.mixer.Sound(file=buf)
        self.cache[name] = snd
        return snd

    def play(self, name):
        if not (self.on and self.ok):
            return
        try:
            self.cache[name].play()
        except (KeyError, pygame.error):
            pass

    def swap_s(self):
        self._build("swap", [(520, 0, 0.07, "sine", 0.3),
                             (720, 0.05, 0.09, "sine", 0.22)])
        self.play("swap")

    def invalid(self):
        self._build("invalid", [(180, 0, 0.2, "saw", 0.18)])
        self.play("invalid")

    def clear_s(self, combo):
        f = 440 * (1.14 ** min(combo - 1, 6))
        name = "clear%d" % min(combo, 7)
        self._build(name, [(f, 0, 0.1, "tri", 0.3),
                           (f * 1.26, 0.06, 0.12, "tri", 0.22)])
        self.play(name)

    def special(self):
        self._build("special", [(280, 0, 0.16, "saw", 0.16),
                                (900, 0.08, 0.22, "sine", 0.24)])
        self.play("special")

    def win(self):
        notes = [(f, i * 0.13, 0.22, "sine", 0.3)
                 for i, f in enumerate((523, 659, 784, 1046))]
        self._build("win", notes)
        self.play("win")

    def lose(self):
        notes = [(f, i * 0.16, 0.25, "sine", 0.28)
                 for i, f in enumerate((420, 330, 240))]
        self._build("lose", notes)
        self.play("lose")


# ==================== 棋盘规则类 ====================
class Board:
    def __init__(self):
        self.grid = [[None] * COLS for _ in range(ROWS)]
        self._populate_until_playable()

    # ---------- 初始生成（避免先天三连，且保证存在可行步） ----------
    def _populate_until_playable(self):
        for _ in range(60):
            self._populate()
            if not self.get_matches()[2] and self.has_valid_move():
                return
        self._populate()  # 兜底（概率上不可能走到）

    def _populate(self):
        self.grid = []
        for r in range(ROWS):
            row = []
            for c in range(COLS):
                gtype = 0
                for _guard in range(50):
                    gtype = random.randrange(TYPES)
                    if c >= 2 and row[c - 1].type == gtype and row[c - 2].type == gtype:
                        continue
                    if r >= 2 and self.grid[r - 1][c].type == gtype and self.grid[r - 2][c].type == gtype:
                        continue
                    break
                g = Gem(r, c, gtype)
                g.y = cell_cy(-1 - r)   # 位于棋盘上方，等待落入动画
                row.append(g)
            self.grid.append(row)

    # ---------- 匹配检测 ----------
    def get_matches(self):
        """返回 (matched二维布尔, runs连段列表, any是否存在匹配)。"""
        matched = [[False] * COLS for _ in range(ROWS)]
        runs = []
        any_match = False

        for r in range(ROWS):      # 横向
            c = 0
            while c < COLS:
                g = self.grid[r][c]
                t = g.type if g else -1
                k = 1
                while c + k < COLS:
                    g2 = self.grid[r][c + k]
                    if g2 and g2.type == t:
                        k += 1
                    else:
                        break
                if t >= 0 and k >= 3:
                    cells = [(r, c + i) for i in range(k)]
                    for i in range(k):
                        matched[r][c + i] = True
                    runs.append({"horiz": True, "cells": cells})
                    any_match = True
                c += k

        for c in range(COLS):      # 纵向
            r = 0
            while r < ROWS:
                g = self.grid[r][c]
                t = g.type if g else -1
                k = 1
                while r + k < ROWS:
                    g2 = self.grid[r + k][c]
                    if g2 and g2.type == t:
                        k += 1
                    else:
                        break
                if t >= 0 and k >= 3:
                    cells = [(r + i, c) for i in range(k)]
                    for i in range(k):
                        matched[r + i][c] = True
                    runs.append({"horiz": False, "cells": cells})
                    any_match = True
                r += k
        return matched, runs, any_match

    # ---------- 特效糖生成规划 ----------
    @staticmethod
    def plan_spawns(runs, swap_keys):
        """
        横向4连→竖条纹(消整列)；纵向4连→横条纹(消整行)；
        5连→彩虹；横纵交叉(T/L)→炸弹。返回 [{r,c,special}, ...]
        """
        used = set()
        spawns = []
        h_map, v_map = {}, {}
        for rn in runs:
            m = h_map if rn["horiz"] else v_map
            for (r, c) in rn["cells"]:
                m[(r, c)] = rn

        def run_has_used(rn):
            return any((r, c) in used for (r, c) in rn["cells"])

        def pick_cell(rn):
            free = [p for p in rn["cells"] if p not in used]
            if not free:
                return None
            for p in free:                    # 优先在玩家交换的位置生成
                if p in swap_keys:
                    return p
            return free[(len(free) - 1) // 2]

        # 1) 交叉点 → 炸弹
        for rn in runs:
            if not rn["horiz"]:
                continue
            for (r, c) in rn["cells"]:
                if (r, c) in v_map and (r, c) not in used:
                    used.add((r, c))
                    spawns.append({"r": r, "c": c, "special": "bomb"})
        # 2) 长连 → 彩虹 / 条纹
        for rn in runs:
            if run_has_used(rn):
                continue
            p = pick_cell(rn)
            if p is None:
                continue
            if len(rn["cells"]) >= 5:
                used.add(p)
                spawns.append({"r": p[0], "c": p[1], "special": "rainbow"})
            elif len(rn["cells"]) == 4:
                used.add(p)
                sp = "stripedV" if rn["horiz"] else "stripedH"
                spawns.append({"r": p[0], "c": p[1], "special": sp})
        return spawns

    # ---------- 特效链式触发（BFS 展开） ----------
    def expand_triggers(self, start_set, exclude=None, effects=None):
        """
        把初始清除集合按特效规则展开：条纹→整行/列，炸弹→3x3。
        effects: 用来收集光束/冲击波的列表 [(kind, data), ...]
        彩虹糖不自动连锁（只能由交换主动使用）。
        """
        if exclude is None:
            exclude = set()
        out = set()
        queue = list(start_set)
        beam_seen = set()
        while queue:
            k = queue.pop(0)
            if k in out or k in exclude or not in_bounds(k[0], k[1]):
                continue
            r, c = k
            g = self.grid[r][c]
            out.add(k)
            if g is None or not g.special or g.special == "rainbow":
                continue
            if g.special == "stripedH":
                if ("h", r) not in beam_seen:
                    beam_seen.add(("h", r))
                    if effects is not None:
                        effects.append(("beam", ("h", r)))
                queue.extend((r, cc) for cc in range(COLS))
            elif g.special == "stripedV":
                if ("v", c) not in beam_seen:
                    beam_seen.add(("v", c))
                    if effects is not None:
                        effects.append(("beam", ("v", c)))
                queue.extend((rr, c) for rr in range(ROWS))
            elif g.special == "bomb":
                if effects is not None:
                    effects.append(("wave", (cell_cx(c), cell_cy(r))))
                for dr in (-1, 0, 1):
                    for dc in (-1, 0, 1):
                        if in_bounds(r + dr, c + dc):
                            queue.append((r + dr, c + dc))
        return out

    # ---------- 下落与补充（数据层） ----------
    def collapse_and_fill(self):
        """压缩每一列并生成新糖果，返回 [(gem, from_y, to_y), ...] 动画信息。"""
        moves_info = []
        for c in range(COLS):
            wp = ROWS - 1
            for r in range(ROWS - 1, -1, -1):
                g = self.grid[r][c]
                if g is not None:
                    if wp != r:
                        from_y = g.y
                        self.grid[wp][c] = g
                        self.grid[r][c] = None
                        g.r = wp
                        moves_info.append((g, from_y, cell_cy(wp)))
                    wp -= 1
            top_empty = wp
            for r in range(wp, -1, -1):
                g = Gem(r, c, random.randrange(TYPES))
                g.y = cell_cy(r - top_empty - 1)
                self.grid[r][c] = g
                moves_info.append((g, g.y, cell_cy(r)))
        return moves_info

    # ---------- 可行步判定 ----------
    def is_valid_swap(self, r1, c1, r2, c2):
        a, b = self.grid[r1][c1], self.grid[r2][c2]
        if a is None or b is None:
            return False
        if a.special == "rainbow" or b.special == "rainbow":
            return True
        if a.special and b.special:
            return True
        self.grid[r1][c1], self.grid[r2][c2] = b, a
        ok = self.get_matches()[2]
        self.grid[r1][c1], self.grid[r2][c2] = a, b
        return ok

    def has_valid_move(self):
        return self.find_hint() is not None

    def find_hint(self):
        for r in range(ROWS):
            for c in range(COLS):
                if c + 1 < COLS and self.is_valid_swap(r, c, r, c + 1):
                    return r, c, r, c + 1
                if r + 1 < ROWS and self.is_valid_swap(r, c, r + 1, c):
                    return r, c, r + 1, c
        return None

    # ---------- 无解洗牌（数据层） ----------
    def reshuffle(self):
        """重排现有糖果，保证无先天匹配且有可行步。成功返回 True。"""
        flat = []
        for r in range(ROWS):
            for c in range(COLS):
                flat.append(self.grid[r][c])
        for _attempt in range(300):
            random.shuffle(flat)
            idx = 0
            for r in range(ROWS):
                for c in range(COLS):
                    g = flat[idx]
                    idx += 1
                    g.r, g.c = r, c
                    self.grid[r][c] = g
            if not self.get_matches()[2] and self.has_valid_move():
                return True
        return False


# ==================== 特效对象 ====================
class Particle:
    __slots__ = ("x", "y", "vx", "vy", "life", "max_life", "size", "color")

    def __init__(self, x, y, color):
        ang = random.uniform(0, math.tau)
        spd = random.uniform(80, 300)
        self.x, self.y = x, y
        self.vx = math.cos(ang) * spd
        self.vy = math.sin(ang) * spd - 100
        self.max_life = random.uniform(0.45, 0.8)
        self.life = self.max_life
        self.size = random.uniform(2.0, 4.5)   # 圆形粒子半径
        self.color = color


class FloatText:
    __slots__ = ("x", "y", "life", "max_life", "text", "color", "size")

    def __init__(self, x, y, text, color, size=20):
        self.x, self.y = x, y
        self.text = text
        self.color = color
        self.size = size
        self.max_life = 1.0
        self.life = self.max_life


# ==================== 元素外观（基于 image/ 素材） ====================
class ImageArt:
    """
    平滑素材管线：
      1. 50x50 原图平滑缩放到 TILE(48)
      2. 在全尺寸图上叠加特效标记（条纹 / 炸弹）
    彩虹糖的旋转彩点在运行时动态绘制。
    """

    UP = TILE                  # 最终图尺寸 48

    def __init__(self, image_dir):
        self.dir = image_dir
        self._scale_cache = {}

        # 普通版 / 高亮表情版底图
        bases = [self._load("%d.png" % (i + 1)) for i in range(TYPES)]
        hi_bases = [self._load("0%d_hightlight.png" % (i + 1))
                    for i in range(TYPES)]

        # self._imgs[special][highlighted][type]
        self._imgs = {}
        for special in (None, "stripedH", "stripedV", "bomb"):
            self._imgs[special] = {False: [], True: []}
            for t in range(TYPES):
                self._imgs[special][False].append(
                    self._build(bases[t], special))
                self._imgs[special][True].append(
                    self._build(hi_bases[t], special))

        # 进度条木框：平滑缩放到 HUD 尺寸
        proc = self._load("process.png", alpha=True)
        self.proc_frame = pygame.transform.smoothscale(proc, (456, 54))

        # 选中框 / 提示框素材（50x50 RGBA）
        self.choose = pygame.transform.smoothscale(
            self._load("choose.png", alpha=True), (CELL - 4, CELL - 4))
        self.circle_choose = pygame.transform.smoothscale(
            self._load("circle_choose.png", alpha=True), (CELL - 4, CELL - 4))

    def _load(self, name, alpha=False):
        path = os.path.join(self.dir, name)
        if not os.path.isfile(path):
            raise FileNotFoundError(
                "找不到素材图片：%s（请确认 image 文件夹完整）" % path)
        img = pygame.image.load(path)
        return img.convert_alpha() if alpha else img.convert()

    def _build(self, base, special):
        """平滑缩放 → 画特效标记。"""
        img = pygame.transform.smoothscale(
            base, (self.UP, self.UP)).convert_alpha()
        if special in ("stripedH", "stripedV"):
            mark = pygame.Surface((self.UP, self.UP), pygame.SRCALPHA)
            if special == "stripedH":
                for yy in (8, 22, 36):
                    pygame.draw.rect(mark, (255, 255, 255, 235),
                                     (4, yy, self.UP - 8, 6),
                                     border_radius=3)
            else:
                for xx in (8, 22, 36):
                    pygame.draw.rect(mark, (255, 255, 255, 235),
                                     (xx, 4, 6, self.UP - 8),
                                     border_radius=3)
            img.blit(mark, (0, 0))
        elif special == "bomb":
            mark = pygame.Surface((self.UP, self.UP), pygame.SRCALPHA)
            cx = self.UP // 2
            pygame.draw.circle(mark, (90, 30, 110, 220), (cx, cx), 13)
            pygame.draw.line(mark, (255, 255, 255, 255),
                             (cx, cx - 8), (cx, cx + 8), 4)
            pygame.draw.line(mark, (255, 255, 255, 255),
                             (cx - 8, cx), (cx + 8, cx), 4)
            img.blit(mark, (0, 0))
        return img

    def scaled(self, gem, size, highlighted=False):
        """平滑缩放（带缓存）。"""
        ck = (gem.special, gem.type, highlighted, size)
        img = self._scale_cache.get(ck)
        if img is None:
            # 彩虹糖无静态叠加（彩点运行时动态绘制），底图同普通版
            base_key = None if gem.special == "rainbow" else gem.special
            src = self._imgs[base_key][highlighted][gem.type]
            img = pygame.transform.smoothscale(src, (size, size))
            self._scale_cache[ck] = img
        return img


# ==================== 局域网对战网络层 ====================
class LanLink:
    """
    TCP 点对点连接，JSON 行协议（每行一个 JSON 对象）。
    接收在后台线程完成并推入队列，主线程用 poll() 取用，不阻塞渲染。
    对方断开或出错时，队列会收到 {"t": "_closed"}。
    """

    def __init__(self, sock):
        self.sock = sock
        self._q = queue.Queue()
        self._send_lock = threading.Lock()
        self._closed = False
        sock.settimeout(None)
        threading.Thread(target=self._recv_loop, daemon=True).start()

    @classmethod
    def host(cls, port=LAN_PORT):
        """监听端口，返回 (server_sock, 接受后的 LanLink 由 accept() 取得)。"""
        srv = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
        srv.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEADDR, 1)
        srv.bind(("0.0.0.0", port))
        srv.listen(1)
        return srv

    @classmethod
    def accept(cls, srv):
        """阻塞等待一个客户端连接，返回 LanLink。"""
        conn, _addr = srv.accept()
        srv.close()
        return cls(conn)

    @classmethod
    def join(cls, ip, port=LAN_PORT, timeout=5.0):
        """连接主机，失败抛异常。"""
        sock = socket.create_connection((ip, port), timeout=timeout)
        return cls(sock)

    def send(self, msg):
        if self._closed:
            return
        try:
            data = (json.dumps(msg) + "\n").encode("utf-8")
            with self._send_lock:
                self.sock.sendall(data)
        except OSError:
            self._closed = True
            self._q.put({"t": "_closed"})

    def _recv_loop(self):
        buf = b""
        try:
            while True:
                chunk = self.sock.recv(4096)
                if not chunk:
                    break
                buf += chunk
                while b"\n" in buf:
                    line, buf = buf.split(b"\n", 1)
                    line = line.strip()
                    if line:
                        try:
                            self._q.put(json.loads(line.decode("utf-8")))
                        except ValueError:
                            pass
        except OSError:
            pass
        self._closed = True
        self._q.put({"t": "_closed"})

    def poll(self):
        """取出所有待处理消息（无则返回空列表）。"""
        msgs = []
        while True:
            try:
                msgs.append(self._q.get_nowait())
            except queue.Empty:
                break
        return msgs

    def close(self):
        self._closed = True
        try:
            self.sock.shutdown(socket.SHUT_RDWR)
        except OSError:
            pass
        try:
            self.sock.close()
        except OSError:
            pass


def get_lan_ip():
    """获取本机局域网 IP（用于建房时展示给对方）。"""
    try:
        s = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
        s.connect(("8.8.8.8", 80))      # 不会真的发包，只为选路由
        ip = s.getsockname()[0]
        s.close()
        return ip
    except OSError:
        try:
            return socket.gethostbyname(socket.gethostname())
        except OSError:
            return "127.0.0.1"


# ==================== 稳健中文字体加载 ====================
_FONT_CACHE = {}

def _font_candidates(bold):
    win_fonts = os.path.join(os.environ.get("WINDIR", r"C:\Windows"), "Fonts")
    if bold:
        names = ("msyhbd.ttc", "simhei.ttf", "msyh.ttc", "simsun.ttc")
    else:
        names = ("msyh.ttc", "simhei.ttf", "simsun.ttc")
    return [os.path.join(win_fonts, n) for n in names]

def load_font(size, bold=False):
    """
    直接按路径加载系统字体文件，绕过 pygame.font.SysFont 的注册表枚举。
    部分电脑字体注册表含非字符串（int）条目，SysFont 会抛
    'TypeError: expected str, bytes or os.PathLike object, not int'。
    """
    ck = (size, bold)
    f = _FONT_CACHE.get(ck)
    if f is not None:
        return f
    for path in _font_candidates(bold):
        if os.path.isfile(path):
            try:
                f = pygame.font.Font(path, size)
                _FONT_CACHE[ck] = f
                return f
            except Exception:
                continue
    # 兜底：pygame 内置字体（不支持中文但不会崩溃）
    f = pygame.font.Font(None, int(size * 1.4))
    _FONT_CACHE[ck] = f
    return f


# ==================== 主游戏类 ====================
class Game:
    BEST_FILE = os.path.join(os.path.dirname(os.path.abspath(__file__)),
                             "best.json")

    def __init__(self):
        pygame.init()
        pygame.display.set_caption("消消乐")
        self.screen = pygame.display.set_mode((WIN_W, WIN_H))
        self.clock = pygame.time.Clock()

        # 中文字体（直接从系统字体文件加载，避免 SysFont 注册表枚举崩溃）
        font = load_font
        self.f_title = font(24, True)
        self.f_stat_label = font(12)
        self.f_stat_val = font(20, True)
        self.f_btn = font(16, True)
        self.f_panel_title = font(26, True)
        self.f_panel_text = font(15)
        self.f_small = font(12)

        self.art = ImageArt(IMAGE_DIR)
        self.sound = SoundManager()
        self.sound.on = self._load_sound_pref()

        self.best = self._load_best()
        self.state = STATE_MENU
        self.result = None

        # 局域网对战
        self.pk = None              # {"link","opp","end_ms","seed"} 或 None
        self.pk_final = None        # 结算时定格的 (我方分, 对方分)
        self.after_pk = None        # 结算后保留的连接（支持再来一局）
        self.my_rematch = False     # 本方是否已请求再来一局
        self._pk_sent = -1          # 已同步给对方的分数
        self.lan_mode = None        # None / "host" / "join"
        self.lan_ip = ""            # IP 输入框内容
        self.lan_status = ""        # 状态/错误提示
        self.lan_srv = None         # 建房监听 socket
        self.lan_link = None        # 已建立、尚未开赛的连接
        self._lan_q = queue.Queue() # accept/join 异步结果
        self.pk_duration = PK_DURATION  # 本局选定的对战时长

        # 道具与受影响效果
        self.energy = 0             # 0..ENERGY_MAX
        self.items_used = 0         # 已用道具数
        self.shield_held = False    # 是否装备护盾
        self.fog_end = 0            # 迷雾结束时刻
        self.paper = None           # (结束时刻, 中心r, 中心c)
        self.imp = None             # (爆炸时刻, r, c)
        self.shuffle_q = []         # 等待空闲执行的位移动画：[(cells,)]
        self._idle_tw = []          # 空闲期 tween（道具位移）
        self.banner = None          # (文字, 结束时刻, 颜色)

        # 关卡数据
        self.level = 1
        self.score = 0
        self.level_start_score = 0
        self.moves = 20
        self.target = 1200

        self.board = Board()
        self.gen = None                 # 当前执行的流程生成器
        self.batch = []                 # 生成器等待中的 tween 列表

        self.selected = None
        self.drag = None
        self.hint = None                # (r1,c1,r2,c2,expire_ms)
        self.particles = []
        self.floats = []
        self.beams = []                 # (dir, index, life 0..1)
        self.waves = []                 # (x, y, radius, life)

        self._overlay_btn = pygame.Rect(WIN_W // 2 - 100, WIN_H // 2 + 80, 200, 48)
        self._overlay_btn2 = pygame.Rect(WIN_W // 2 - 100, WIN_H // 2 + 136,
                                         200, 44)
        self._buttons = self._build_buttons()
        self._bg_surf = self._render_background()
        # 启动落入动画（菜单界面即可看到动物落位）
        self._start_gen(self._flow_init())

    def _render_background(self):
        """暖色垂直渐变底 + 柔和半透明气泡装饰。"""
        surf = pygame.Surface((WIN_W, WIN_H))
        for y in range(WIN_H):
            k = y / WIN_H
            col = tuple(int(BG_TOP[i] + (BG_BOTTOM[i] - BG_TOP[i]) * k)
                        for i in range(3))
            pygame.draw.line(surf, col, (0, y), (WIN_W, y))
        rng = random.Random(20260920)
        bubbles = pygame.Surface((WIN_W, WIN_H), pygame.SRCALPHA)
        for _ in range(18):
            x = rng.randrange(0, WIN_W)
            y = rng.randrange(0, WIN_H)
            r = rng.randrange(8, 26)
            pygame.draw.circle(bubbles, (255, 255, 255, 26), (x, y), r)
        surf.blit(bubbles, (0, 0))
        return surf

    # ---------- 圆角绘制基础组件 ----------
    def _draw_panel(self, rect, fill=PANEL_LIGHT, radius=12):
        """圆角浅色面板：底部柔和阴影 + 白色填充。"""
        shadow = rect.move(0, 3)
        pygame.draw.rect(self.screen, PANEL_SH, shadow,
                         border_radius=radius)
        pygame.draw.rect(self.screen, fill, rect, border_radius=radius)

    def _draw_button(self, rect, fill, sh_c, radius=12):
        """圆润按钮：底部深色边（立体感）+ 填充。"""
        pygame.draw.rect(self.screen, sh_c, rect.move(0, 3),
                         border_radius=radius)
        pygame.draw.rect(self.screen, fill, rect, border_radius=radius)

    def _blit_text_outline(self, font, text, color, outline, center,
                           offset=2):
        """带描边的文字（四方向偏移描边）。"""
        base = font.render(text, True, color)
        edge = font.render(text, True, outline)
        rect = base.get_rect(center=center)
        for dx, dy in ((-offset, 0), (offset, 0), (0, -offset), (0, offset)):
            self.screen.blit(edge, rect.move(dx, dy))
        self.screen.blit(base, rect)

    # ---------- 持久化 ----------
    def _load_best(self):
        try:
            with open(self.BEST_FILE, "r", encoding="utf-8") as f:
                return int(json.load(f).get("best", 0))
        except (OSError, ValueError):
            return 0

    def _save_best(self):
        try:
            with open(self.BEST_FILE, "w", encoding="utf-8") as f:
                json.dump({"best": self.best}, f)
        except OSError:
            pass

    def _load_sound_pref(self):
        path = os.path.join(os.path.dirname(self.BEST_FILE), "sound.cfg")
        try:
            with open(path, "r", encoding="utf-8") as f:
                return f.read().strip() != "0"
        except OSError:
            return True

    def _save_sound_pref(self):
        path = os.path.join(os.path.dirname(self.BEST_FILE), "sound.cfg")
        try:
            with open(path, "w", encoding="utf-8") as f:
                f.write("1" if self.sound.on else "0")
        except OSError:
            pass

    # ---------- 按钮 ----------
    def _build_buttons(self):
        bw = (WIN_W - 24 - 16) / 3
        y = BOARD_Y + ROWS * CELL + 16
        rects = []
        x = 12
        for label, action in (("重开本关", "restart"),
                              ("提示", "hint"),
                              ("音效:开", "sound")):
            rects.append((pygame.Rect(int(x), y, int(bw), 42), label, action))
            x += bw + 8
        return rects

    # ---------- 关卡控制 ----------
    def start_level(self, inc=False, retry=False):
        if inc:
            self.level += 1
        if retry:
            self.score = self.level_start_score
        self.level_start_score = self.score
        self.moves = 20 + min(8, (self.level - 1) * 2)
        self.target = round(1200 * 1.45 ** (self.level - 1))

        self.selected = None
        self.drag = None
        self.hint = None
        self.particles = []
        self.floats = []
        self.beams = []
        self.waves = []
        self.board = Board()
        self.state = STATE_PLAY
        self._start_gen(self._flow_init())

    # ---------- 局域网对战 ----------
    def _lan_reset(self):
        """清理 LAN 界面状态（未开赛的连接/监听）。"""
        if self.lan_link is not None:
            self.lan_link.close()
            self.lan_link = None
        if self.lan_srv is not None:
            try:
                self.lan_srv.close()
            except OSError:
                pass
            self.lan_srv = None
        self.lan_mode = None
        self.lan_status = ""

    def _pk_cleanup(self, notify=True):
        """结束对战连接。"""
        if self.pk is not None:
            if notify:
                self.pk["link"].send({"t": "bye"})
            self.pk["link"].close()
            self.pk = None

    def _start_host(self):
        """建房：监听端口并后台等待对方加入。"""
        self.lan_srv = LanLink.host()
        self.lan_mode = "host"
        self.lan_status = "等待对方加入…"
        threading.Thread(target=self._accept_worker,
                         args=(self.lan_srv,), daemon=True).start()

    def _accept_worker(self, srv):
        try:
            link = LanLink.accept(srv)
            self._lan_q.put(("ok", link, srv))
        except OSError:
            self._lan_q.put(("err", "建房失败或监听已关闭", srv))

    def _join_worker(self, ip):
        try:
            link = LanLink.join(ip)
            self._lan_q.put(("ok", link, None))
        except OSError:
            self._lan_q.put(("err", "连接失败，请检查 IP 或确认对方已建房", None))

    def start_pk(self, seed, link, is_host=False, duration=None):
        """双方用同一种子建相同棋盘，duration 秒限时比分。"""
        duration = int(duration) if duration else PK_DURATION
        # 防御异常时长（网络消息可能被篡改）
        duration = max(15, min(600, duration))
        random.seed(seed)
        self.score = 0
        self.level_start_score = 0
        self.selected = None
        self.drag = None
        self.hint = None
        self.particles = []
        self.floats = []
        self.beams = []
        self.waves = []
        self.board = Board()
        self.pk = {"link": link, "opp": 0, "seed": seed,
                   "is_host": is_host, "dur": duration,
                   "opp_flash": -10 ** 9,
                   "end_ms": pygame.time.get_ticks() + duration * 1000}
        self._pk_sent = -1
        self.pk_final = None
        self.after_pk = None
        self.my_rematch = False
        # 道具状态重置
        self.energy = 0
        self.items_used = 0
        self.shield_held = False
        self.fog_end = 0
        self.paper = None
        self.imp = None
        self.shuffle_q = []
        self._idle_tw = []
        self.banner = None
        self.lan_link = None
        self.lan_srv = None
        self.state = STATE_PLAY
        self._start_gen(self._flow_init())

    def _pk_settle(self, result=None, keep_link=False):
        """
        时间到或对方离开时结算。
        keep_link=True：正常打满时间，保留连接以支持"再来一局"；
        keep_link=False：对方掉线/中途离开，只能返回菜单。
        """
        if self.pk is None:
            return
        my, opp = self.score, self.pk["opp"]
        is_host = self.pk.get("is_host", False)
        dur = self.pk.get("dur", PK_DURATION)
        if result is None:
            result = ("pk_win" if my > opp
                      else "pk_lose" if my < opp else "pk_draw")
        self.pk_final = (my, opp)
        self.result = result
        link = self.pk["link"]
        self.pk = None
        if keep_link:
            # 正常结算：发 end（带最终分数），连接保留到 after_pk
            link.send({"t": "end", "score": my})
            self.after_pk = {"link": link, "is_host": is_host,
                             "dur": dur, "opp_rematch": False}
            self.my_rematch = False
        else:
            # 对方已离开：直接关闭
            link.close()
            self.after_pk = None
        self.state = STATE_OVER
        if result == "pk_win":
            self.sound.win()
        else:
            self.sound.lose()

    def _poll_pk(self):
        """主循环每帧调用：处理对战消息、同步分数、检查时间。"""
        if self.pk is None:
            return
        for m in self.pk["link"].poll():
            t = m.get("t")
            if t == "score":
                new_s = int(m.get("score", 0))
                if new_s > self.pk["opp"]:           # 对方加分：飘字 + 高亮
                    now = pygame.time.get_ticks()
                    self.pk["opp_flash"] = now
                    self.floats.append(FloatText(
                        WIN_W * 0.75, 92,
                        "+%d" % (new_s - self.pk["opp"]),
                        (60, 150, 255), 18))
                self.pk["opp"] = new_s
            elif t == "item":
                self._receive_item(m.get("item"))
                if self.pk is None:                # 极端情况：结算中
                    return
            elif t == "end":
                new_s = int(m.get("score", 0))
                if new_s > self.pk["opp"]:
                    self.pk["opp_flash"] = pygame.time.get_ticks()
                self.pk["opp"] = new_s
                # 对方已到点，正常结算并保留连接
                self._pk_settle(keep_link=True)
                return
            elif t in ("bye", "_closed"):
                self._pk_settle("pk_win")       # 对方中途离开/掉线判胜
                return
        if self.score != self._pk_sent:
            self.pk["link"].send({"t": "score", "score": self.score})
            self._pk_sent = self.score
        if pygame.time.get_ticks() >= self.pk["end_ms"]:
            self._pk_settle(keep_link=True)    # 自己时间到，保留连接

    def _poll_lan(self):
        """LAN 界面每帧调用：处理连接结果与开赛消息。"""
        while True:
            try:
                tag, payload, srv = self._lan_q.get_nowait()
            except queue.Empty:
                break
            if srv is not None and srv is not self.lan_srv:
                continue                # 旧监听线程的迟到结果，丢弃
            if tag == "ok":
                self.lan_link = payload
                self.lan_status = ("对方已加入，可以开始！"
                                   if self.lan_mode == "host"
                                   else "已连接，等待主机开始…")
            else:
                self.lan_status = payload
        if self.lan_link is None:
            return
        for m in self.lan_link.poll():
            t = m.get("t")
            if t == "start" and self.lan_mode == "join":
                dur = int(m.get("duration", PK_DURATION))
                self.pk_duration = max(15, min(600, dur))
                self.start_pk(int(m.get("seed", 0)), self.lan_link,
                              duration=self.pk_duration)
                return
            if t in ("bye", "_closed"):
                self.lan_link.close()
                self.lan_link = None
                if self.lan_mode == "host":
                    self._start_host()          # 对方离开，重新等待
                    self.lan_status = "对方已离开，等待新玩家…"
                else:
                    self.lan_status = "与主机的连接已断开"
                return

    # ---------- 干扰道具 ----------
    def _gain_energy(self, gems, specials):
        if self.pk is None or self.energy >= ENERGY_MAX:
            return
        self.energy = min(ENERGY_MAX,
                          self.energy + gems * ENERGY_PER_GEM
                          + specials * ENERGY_SPECIAL)

    def _set_banner(self, text, color=(255, 255, 255)):
        self.banner = (text, pygame.time.get_ticks() + 1800, color)

    def _item_ready(self, key):
        if self.energy < ENERGY_MAX or self.items_used >= MAX_ITEM_USES:
            return False
        if key == "shield" and self.shield_held:
            return False
        return True

    def _use_item(self, key):
        if not self._item_ready(key):
            return
        self.energy = 0
        self.items_used += 1
        if key == "shield":
            self.shield_held = True
            self._set_banner("护盾已装备", (120, 200, 255))
            return
        self.pk["link"].send({"t": "item", "item": key})
        self._apply_item(key)
        self._set_banner("你使用了 %s" % ITEM_NAMES[key])

    def _receive_item(self, key):
        name = ITEM_NAMES.get(key)
        if name is None:
            return
        if self.shield_held:
            self.shield_held = False
            self._set_banner("护盾抵消了 %s！" % name, (120, 220, 255))
            return
        self._apply_item(key)
        self._set_banner("对方使用了 %s！" % name, (255, 120, 120))

    def _apply_item(self, key):
        now = pygame.time.get_ticks()
        if key == "fog":
            self.fog_end = now + FOG_MS
        elif key == "paper":
            rr = random.randrange(2, ROWS - 2)
            cc = random.randrange(2, COLS - 2)
            self.paper = (now + PAPER_MS, rr, cc)
        elif key == "imp":
            cells = [(r, c) for r in range(ROWS) for c in range(COLS)
                     if self.board.grid[r][c]]
            rr, cc = random.choice(cells)
            self.imp = (now + IMP_MS, rr, cc)
        elif key == "jelly":
            r = random.randrange(ROWS)
            cells = [(r, c) for c in range(COLS)
                     if self.board.grid[r][c]]
            if len(cells) >= 2:
                self.shuffle_q.append(cells)

    def _do_shuffle(self, cells):
        """把指定格内的糖果位置随机互换（不消除、不改分），播放位移动画。"""
        gems = [self.board.grid[r][c] for r, c in cells]
        order = list(range(len(gems)))
        random.shuffle(order)
        if len(order) > 1 and order == list(range(len(order))):
            order[0], order[1] = order[1], order[0]
        moves = list(zip(gems, [cells[i] for i in order]))
        for gem, (nr, nc) in moves:               # 双射重排，直接覆盖
            self.board.grid[nr][nc] = gem
            gem.r, gem.c = nr, nc
        for gem, (nr, nc) in moves:
            tx, ty = cell_cx(nc), cell_cy(nr)
            ox, oy = gem.x, gem.y
            self._idle_tw.append(Tween(
                0.3,
                lambda e, gem=gem, ox=ox, oy=oy, tx=tx, ty=ty: (
                    setattr(gem, "x", ox + (tx - ox) * e),
                    setattr(gem, "y", oy + (ty - oy) * e)),
                ease_in_out))

    def _process_item_timing(self):
        """PLAY 中每帧：执行排队位移、小鬼到时爆炸。"""
        if self.gen is None and not self._idle_tw:
            while self.shuffle_q:
                self._do_shuffle(self.shuffle_q.pop(0))
        now = pygame.time.get_ticks()
        if self.imp and now >= self.imp[0]:
            _t, rr, cc = self.imp
            self.imp = None
            cells = [(r, c)
                     for r in range(rr - 1, rr + 2)
                     for c in range(cc - 1, cc + 2)
                     if in_bounds(r, c) and self.board.grid[r][c]]
            if len(cells) >= 2:
                if self.gen is None and not self._idle_tw:
                    self._do_shuffle(cells)
                else:
                    self.shuffle_q.append(cells)

    def _update_idle_tw(self, dt):
        self._idle_tw = [t for t in self._idle_tw if not t.update(dt)]

    # ---------- 结算后的再来一局 ----------
    def _request_rematch(self):
        """请求再来一局：发送 rematch 并标记本方意愿。"""
        if self.after_pk is None or self.my_rematch:
            return
        self.my_rematch = True
        self.after_pk["link"].send({"t": "rematch"})

    def _poll_rematch(self):
        """结算页每帧调用：处理 rematch/start/bye，双方同意后由主机开新局。"""
        if self.after_pk is None:
            return
        link = self.after_pk["link"]
        for m in link.poll():
            t = m.get("t")
            if t == "rematch":
                self.after_pk["opp_rematch"] = True
            elif t == "start":
                # 主机在双方同意后发来新种子 → 直接开新局
                seed = int(m.get("seed", 0))
                dur = int(m.get("duration", PK_DURATION))
                self.after_pk = None
                self.start_pk(seed, link, duration=dur)   # 客户端 is_host=False
                return
            elif t in ("bye", "_closed"):
                # 对方选择结束：关闭连接，结算页只剩"返回菜单"
                link.close()
                self.after_pk = None
                return
        # 主机：双方都请求再来一局 → 新种子、发 start、自己开赛
        if (self.after_pk is not None
                and self.after_pk["is_host"]
                and self.my_rematch
                and self.after_pk["opp_rematch"]):
            seed = random.randrange(1, 2 ** 31)
            dur = self.after_pk["dur"]
            link.send({"t": "start", "seed": seed,
                       "duration": dur})
            self.after_pk = None
            self.start_pk(seed, link, is_host=True, duration=dur)

    def _go_menu(self):
        """结束对战/连接，回到主菜单。"""
        # 结算后保留的连接：通知对方本方结束
        if self.after_pk is not None:
            link = self.after_pk["link"]
            self.after_pk = None
            link.send({"t": "bye"})
            link.close()
        self._pk_cleanup()
        self._lan_reset()
        self.result = None
        self.pk_final = None
        self.board = Board()
        self.state = STATE_MENU
        self._start_gen(self._flow_init())

    # ---------- 生成器驱动 ----------
    def _start_gen(self, gen):
        self.gen = gen
        self.batch = []
        try:
            self.batch = next(gen) or []
        except StopIteration:
            self.gen = None

    def _update_gen(self, dt):
        if self.gen is None:
            return
        self.batch = [t for t in self.batch if not t.update(dt)]
        if not self.batch:
            try:
                self.batch = self.gen.send(None) or []
            except StopIteration:
                self.gen = None

    def _busy(self):
        return (self.state != STATE_PLAY or self.gen is not None
                or bool(self._idle_tw))

    # ---------- 初始落入动画 ----------
    def _flow_init(self):
        tw = []
        for r in range(ROWS):
            for c in range(COLS):
                g = self.board.grid[r][c]
                from_y = g.y
                tw.append(Tween(0.46,
                                lambda e, g=g, fy=from_y, ty=cell_cy(g.r):
                                    setattr(g, "y", fy + (ty - fy) * e),
                                ease_out_bounce, r * 0.05 + c * 0.012))
        yield tw

    # ---------- 交换流程 ----------
    def _flow_swap(self, r1, c1, r2, c2):
        a, b = self.board.grid[r1][c1], self.board.grid[r2][c2]
        self.sound.swap_s()
        # 数据交换
        self.board.grid[r1][c1], self.board.grid[r2][c2] = b, a
        a.r, a.c, b.r, b.c = r2, c2, r1, c1
        ax0, ay0 = cell_cx(c1), cell_cy(r1)
        bx0, by0 = cell_cx(c2), cell_cy(r2)
        yield [
            Tween(0.22, lambda e: (
                setattr(a, "x", ax0 + (bx0 - ax0) * e),
                setattr(a, "y", ay0 + (by0 - ay0) * e)), ease_in_out),
            Tween(0.22, lambda e: (
                setattr(b, "x", bx0 + (ax0 - bx0) * e),
                setattr(b, "y", by0 + (ay0 - by0) * e)), ease_in_out),
        ]

        # ----- 彩虹糖参与 -----
        if a.special == "rainbow" or b.special == "rainbow":
            rb = a if a.special == "rainbow" else b
            other = b if rb is a else a
            start_set = {(rb.r, rb.c), (other.r, other.c)}
            if other.special == "rainbow":          # 双彩虹 → 全屏
                start_set = {(r, c) for r in range(ROWS) for c in range(COLS)}
                extra_tw = []
            elif other.special:                     # 彩虹 + 条纹/炸弹
                for r in range(ROWS):
                    for c in range(COLS):
                        g = self.board.grid[r][c]
                        if g and g.type == other.type and g not in (rb, other):
                            g.special = other.special
                            start_set.add((r, c))
                extra_tw = self._spawn_pulse(start_set - {(rb.r, rb.c),
                                                          (other.r, other.c)})
            else:                                   # 彩虹 + 普通 → 全场同色
                for r in range(ROWS):
                    for c in range(COLS):
                        g = self.board.grid[r][c]
                        if g and g.type == other.type:
                            start_set.add((r, c))
                extra_tw = []
            self.moves -= 1
            yield from self._flow_resolve(initial=start_set, extra_tw=extra_tw)
            return

        # ----- 两个特效糖直接交换 -----
        if a.special and b.special:
            start_set = {(a.r, a.c), (b.r, b.c)}
            if a.special == "bomb" and b.special == "bomb":
                for (gr, gc) in ((a.r, a.c), (b.r, b.c)):   # 双炸弹 5x5x2
                    for dr in range(-2, 3):
                        for dc in range(-2, 3):
                            if in_bounds(gr + dr, gc + dc):
                                start_set.add((gr + dr, gc + dc))
            elif "bomb" in (a.special, b.special):           # 条纹+炸弹 → 三行三列
                st = a if a.special != "bomb" else b
                for i in (-1, 0, 1):
                    for cc in range(COLS):
                        if in_bounds(st.r + i, cc):
                            start_set.add((st.r + i, cc))
                    for rr in range(ROWS):
                        if in_bounds(rr, st.c + i):
                            start_set.add((rr, st.c + i))
            else:                                           # 条纹+条纹 → 双十字
                for g in (a, b):
                    for cc in range(COLS):
                        start_set.add((g.r, cc))
                    for rr in range(ROWS):
                        start_set.add((rr, g.c))
            self.moves -= 1
            yield from self._flow_resolve(initial=start_set)
            return

        # ----- 普通交换：必须产生匹配 -----
        if not self.board.get_matches()[2]:
            self.sound.invalid()
            # 换回
            self.board.grid[a.r][a.c], self.board.grid[b.r][b.c] = b, a
            a.r, a.c, b.r, b.c = r1, c1, r2, c2
            yield [
                Tween(0.22, lambda e: (
                    setattr(a, "x", bx0 + (ax0 - bx0) * e),
                    setattr(a, "y", by0 + (ay0 - by0) * e)), ease_in_out),
                Tween(0.22, lambda e: (
                    setattr(b, "x", ax0 + (bx0 - ax0) * e),
                    setattr(b, "y", ay0 + (by0 - ay0) * e)), ease_in_out),
            ]
            return

        self.moves -= 1
        swap_keys = {(r1, c1), (r2, c2)}
        yield from self._flow_resolve(swap_keys=swap_keys)

    def _spawn_pulse(self, positions):
        """让指定位置的糖果做一次"生成弹跳"（终值 scale=1）。"""
        tw = []
        for (r, c) in positions:
            g = self.board.grid[r][c]
            if g:
                tw.append(Tween(0.26,
                                lambda e, g=g:
                                    setattr(g, "scale", 0.3 + 0.7 * ease_out_bounce(e))))
        if tw:
            self.sound.special()
        return tw

    # ---------- 结算主循环（生成器：每 yield 一批 tween，驱动器等其全部完成） ----------
    def _flow_resolve(self, swap_keys=None, initial=None, extra_tw=None):
        if swap_keys is None:
            swap_keys = set()
        if extra_tw is None:
            extra_tw = []
        combo = 0
        while True:
            if initial is not None:
                # 手动触发（特效糖组合 / 彩虹），直接算第一波
                start_set = initial
                initial = None
                combo = 1
                spawn_tw = list(extra_tw)
                extra_tw = []
            else:
                matched, runs, any_match = self.board.get_matches()
                if not any_match:
                    break
                combo += 1
                spawns = self.board.plan_spawns(runs, swap_keys)
                exclude = {(s["r"], s["c"]) for s in spawns}
                for s in spawns:
                    g = self.board.grid[s["r"]][s["c"]]
                    g.special = s["special"]
                spawn_tw = self._spawn_pulse(list(exclude))
                start_set = set()
                for r in range(ROWS):
                    for c in range(COLS):
                        if matched[r][c] and (r, c) not in exclude:
                            start_set.add((r, c))
                if not start_set and exclude:
                    # 极罕见：匹配格全部成为特效糖 → 立即连锁触发，破除匹配
                    start_set = set(exclude)
                    exclude = set()
                    spawn_tw = []

            # 特效链展开 + 视觉效果收集
            fx = []
            full_set = self.board.expand_triggers(start_set, effects=fx)
            for kind, data in fx:
                if kind == "beam":
                    self.beams.append([data[0], data[1], 1.0])
                else:
                    self.waves.append([data[0], data[1], 6, 1.0])

            # 计分 + 粒子 + 消除动画
            special_n = 0
            tw = list(spawn_tw)
            centers_x, centers_y = [], []
            for (r, c) in full_set:
                g = self.board.grid[r][c]
                if g is None:
                    continue
                centers_x.append(cell_cx(c))
                centers_y.append(cell_cy(r))
                self._burst(g, g.special is not None)
                if g.special:
                    special_n += 1
                tw.append(Tween(0.23,
                                lambda e, g=g: (
                                    setattr(g, "scale", 1 - e * 0.92),
                                    setattr(g, "alpha", 1 - e)),
                                ease_in_out))
            gained = len(full_set) * 20 * combo + special_n * 40 * combo
            self.score += gained
            self._gain_energy(len(full_set), special_n)
            self.sound.clear_s(combo)
            if full_set:
                mx = sum(centers_x) / len(centers_x)
                my = sum(centers_y) / len(centers_y)
                self.floats.append(FloatText(mx, my, "+%d" % gained, (255, 255, 255)))
                if combo >= 2:
                    self.floats.append(FloatText(mx, my - 26, "连击 x%d" % combo,
                                                 (255, 225, 77), 22))
            yield tw

            # 真正从棋盘移除
            for (r, c) in full_set:
                self.board.grid[r][c] = None

            # 下落补充动画
            info = self.board.collapse_and_fill()
            drop_tw = []
            for g, from_y, to_y in info:
                dist = abs(to_y - from_y)
                dur = min(0.52, 0.2 + dist / CELL * 0.045)
                drop_tw.append(Tween(dur,
                                     lambda e, g=g, fy=from_y, ty=to_y:
                                         setattr(g, "y", fy + (ty - fy) * e),
                                     ease_out_bounce))
            yield drop_tw
            swap_keys = set()

        # 无更多匹配 → 回合结束判定
        if self.pk is None:                 # PK 模式无目标/步数限制，计时统一结算
            earned = self.score - self.level_start_score
            if earned >= self.target:
                self._game_over(True)
                return
            if self.moves <= 0:
                self._game_over(False)
                return
        if not self.board.has_valid_move():
            self.floats.append(FloatText(WIN_W / 2, BOARD_Y + ROWS * CELL / 2,
                                         "无解，自动洗牌！", (255, 255, 255), 22))
            yield from self._flow_reshuffle_then_idle()

    def _flow_reshuffle_then_idle(self):
        old = []
        for r in range(ROWS):
            for c in range(COLS):
                g = self.board.grid[r][c]
                old.append((g, g.x, g.y))
        ok = self.board.reshuffle()
        tw = []
        if ok:
            for g, ox, oy in old:
                tx, ty = cell_cx(g.c), cell_cy(g.r)
                tw.append(Tween(0.34,
                                lambda e, g=g, ox=ox, oy=oy, tx=tx, ty=ty: (
                                    setattr(g, "x", ox + (tx - ox) * e),
                                    setattr(g, "y", oy + (ty - oy) * e)),
                                ease_in_out, (g.r + g.c) * 0.01))
        else:  # 极端兜底：重建
            self.board = Board()
            for r in range(ROWS):
                for c in range(COLS):
                    g = self.board.grid[r][c]
                    fy = g.y
                    tw.append(Tween(0.46,
                                    lambda e, g=g, fy=fy:
                                        setattr(g, "y", fy + (cell_cy(g.r) - fy) * e),
                                    ease_out_bounce, r * 0.05))
        yield tw

    def _game_over(self, win):
        if self.score > self.best:
            self.best = self.score
            self._save_best()
        self.state = STATE_OVER
        self.result = "win" if win else "lose"
        if win:
            self.sound.win()
        else:
            self.sound.lose()

    # ---------- 粒子 ----------
    def _burst(self, g, big):
        n = 16 if big else 8
        color = TYPE_COLORS[g.type][0]
        for _ in range(n):
            self.particles.append(Particle(g.x, g.y, color))

    def _update_effects(self, dt):
        # 粒子
        alive = []
        for p in self.particles:
            p.life -= dt
            if p.life > 0:
                p.vy += 650 * dt
                p.x += p.vx * dt
                p.y += p.vy * dt
                alive.append(p)
        self.particles = alive

        # 飘字
        alive = []
        for t in self.floats:
            t.life -= dt
            if t.life > 0:
                t.y -= 42 * dt
                alive.append(t)
        self.floats = alive

        # 光束
        alive = []
        for d, i, life in self.beams:
            life -= dt * 3
            if life > 0:
                alive.append([d, i, life])
        self.beams = alive
        # 冲击波
        alive = []
        for w in self.waves:
            w[2] += (CELL * 1.7 - w[2]) * dt * 6
            w[3] -= dt * 2.6
            if w[3] > 0:
                alive.append(w)
        self.waves = alive

    # ==================== 输入 ====================
    def _cell_at(self, pos):
        x, y = pos
        c = int((x - BOARD_X) // CELL)
        r = int((y - BOARD_Y) // CELL)
        if in_bounds(r, c):
            return r, c
        return None

    def handle_event(self, event):
        if event.type == pygame.QUIT:
            if self.after_pk is not None:
                self.after_pk["link"].close()
                self.after_pk = None
            self._pk_cleanup()
            self._lan_reset()
            return False
        if event.type == pygame.KEYDOWN and event.key == pygame.K_ESCAPE:
            if self.pk is not None or self.state == STATE_LAN:
                self._go_menu()
                return True
            if self.after_pk is not None:
                self._go_menu()
                return True
            self._pk_cleanup()
            self._lan_reset()
            return False

        # LAN 界面：IP 键盘输入
        if (self.state == STATE_LAN and self.lan_mode == "join"
                and self.lan_link is None
                and event.type == pygame.KEYDOWN):
            if event.key == pygame.K_BACKSPACE:
                self.lan_ip = self.lan_ip[:-1]
            elif event.key in (pygame.K_RETURN, pygame.K_KP_ENTER):
                self._lan_connect()
            elif event.unicode and event.unicode in "0123456789." \
                    and len(self.lan_ip) < 15:
                self.lan_ip += event.unicode
            return True

        if event.type == pygame.MOUSEBUTTONDOWN and event.button == 1:
            # LAN 界面按钮
            if self.state == STATE_LAN:
                self._lan_click(event.pos)
                return True
            # 菜单 / 结束面板的按钮
            if self.state in (STATE_MENU, STATE_OVER):
                if self._overlay_btn.collidepoint(event.pos):
                    if self.state == STATE_MENU:
                        self.start_level()
                    elif self.result in ("pk_win", "pk_lose", "pk_draw"):
                        # 主按钮：可重连则请求再来一局，否则返回菜单
                        if self.after_pk is not None:
                            self._request_rematch()
                        else:
                            self._go_menu()
                    elif self.result == "win":
                        self.start_level(inc=True)
                    else:
                        self.start_level(retry=True)
                elif self._overlay_btn2.collidepoint(event.pos):
                    if self.state == STATE_MENU:
                        self._lan_reset()
                        self.lan_ip = ""
                        self.state = STATE_LAN
                    elif self.result in ("pk_win", "pk_lose", "pk_draw"):
                        self._go_menu()          # PK 次按钮：返回菜单
                return True
            # PK 道具槽
            if self.pk is not None:
                for i, rect in enumerate(self._item_slot_rects()):
                    if rect.collidepoint(event.pos):
                        self._use_item(ITEM_KEYS[i])
                        return True
            # 底部按钮
            for rect, _label, action in self._buttons:
                if rect.collidepoint(event.pos):
                    self._on_button(action)
                    return True
            # 棋盘：按下记录
            cell = self._cell_at(event.pos)
            if cell and not self._busy():
                self.drag = {"r": cell[0], "c": cell[1],
                             "x": event.pos[0], "y": event.pos[1], "fired": False}
        return True

    def _on_button(self, action):
        if self._busy():
            return
        if action == "restart":
            if self.pk is not None:
                return                  # 对战中不可重开
            self.start_level(retry=True)
        elif action == "hint":
            h = self.board.find_hint()
            if h:
                self.hint = (h[0], h[1], h[2], h[3],
                             pygame.time.get_ticks() + 3000)
        elif action == "sound":
            self.sound.on = not self.sound.on
            self._save_sound_pref()
            if self.sound.on:
                self.sound.swap_s()

    # ---------- LAN 界面 ----------
    def _lan_layout(self):
        panel = pygame.Rect(0, 0, 360, 380)
        panel.center = (WIN_W // 2, WIN_H // 2)
        # 主机时长选择：4 个小按钮一行
        bw = 76
        gap = (panel.w - 40 - bw * 4) / 3
        dur_btns = [pygame.Rect(panel.x + 20 + i * (bw + gap),
                                panel.y + 168, bw, 32)
                    for i in range(4)]
        return {
            "panel": panel,
            "host": pygame.Rect(panel.centerx - 100, panel.y + 120, 200, 44),
            "join": pygame.Rect(panel.centerx - 100, panel.y + 174, 200, 44),
            "back": pygame.Rect(panel.centerx - 70, panel.bottom - 54, 140, 38),
            "go": pygame.Rect(panel.centerx - 100, panel.bottom - 106, 200, 44),
            "input": pygame.Rect(panel.x + 40, panel.y + 116, panel.w - 80, 42),
            "connect": pygame.Rect(panel.centerx - 100, panel.y + 168, 200, 44),
            "dur_btns": dur_btns,
        }

    def _lan_connect(self):
        ip = self.lan_ip.strip()
        if not ip:
            self.lan_status = "请输入主机 IP"
            return
        self.lan_status = "正在连接 %s …" % ip
        threading.Thread(target=self._join_worker, args=(ip,),
                         daemon=True).start()

    def _lan_click(self, pos):
        L = self._lan_layout()
        if self.lan_mode is None:
            if L["host"].collidepoint(pos):
                try:
                    self._start_host()
                except OSError:
                    self.lan_status = "建房失败：端口可能被占用"
            elif L["join"].collidepoint(pos):
                self.lan_mode = "join"
                self.lan_status = "输入主机 IP 后点击连接"
        elif self.lan_mode == "host":
            # 时长选择（开赛前随时可改）
            for i, rect in enumerate(L["dur_btns"]):
                if rect.collidepoint(pos):
                    self.pk_duration = DURATION_PRESETS[i]
                    return
            if self.lan_link is not None and L["go"].collidepoint(pos):
                seed = random.randrange(1, 2 ** 31)
                self.lan_link.send({"t": "start", "seed": seed,
                                    "duration": self.pk_duration})
                self.start_pk(seed, self.lan_link, is_host=True,
                              duration=self.pk_duration)
                return
        elif self.lan_mode == "join":
            if self.lan_link is None and L["connect"].collidepoint(pos):
                self._lan_connect()
                return
        if L["back"].collidepoint(pos):
            self._go_menu()

    def handle_mouse(self):
        """处理拖动与点击（每帧调用）。"""
        if self.state != STATE_PLAY:
            return
        pressed = pygame.mouse.get_pressed()[0]
        pos = pygame.mouse.get_pos()

        if self.drag is not None and pressed and not self.drag["fired"]:
            dx = pos[0] - self.drag["x"]
            dy = pos[1] - self.drag["y"]
            if abs(dx) > CELL * .32 or abs(dy) > CELL * .32:
                sr, sc = self.drag["r"], self.drag["c"]
                if abs(dx) > abs(dy):
                    tr, tc = sr, sc + (1 if dx > 0 else -1)
                else:
                    tr, tc = sr + (1 if dy > 0 else -1), sc
                self.drag["fired"] = True
                if in_bounds(tr, tc) and not self._busy():
                    self.selected = None
                    self.hint = None
                    self._start_gen(self._flow_swap(sr, sc, tr, tc))

        if not pressed and self.drag is not None:
            was = self.drag
            self.drag = None
            if not was["fired"] and not self._busy():
                cell = self._cell_at(pos)
                if cell is None:
                    self.selected = None
                elif self.selected == cell:
                    self.selected = None
                elif self.selected is not None and \
                        abs(self.selected[0] - cell[0]) + abs(self.selected[1] - cell[1]) == 1:
                    sr, sc = self.selected
                    self.selected = None
                    self.hint = None
                    self._start_gen(self._flow_swap(sr, sc, cell[0], cell[1]))
                else:
                    self.selected = cell
                    self.hint = None

    # ==================== 渲染 ====================
    def _draw_background(self):
        self.screen.blit(self._bg_surf, (0, 0))

    def _draw_hud(self):
        # 标题：白色描边标题
        self._blit_text_outline(self.f_title, "消 消 乐", WHITE,
                                (222, 120, 110), (WIN_W // 2, 25))

        labels = ("关卡", "分数", "最佳", "步数")
        values = (str(self.level), str(self.score), str(self.best), str(self.moves))
        val_colors = (TEXT_DARK, TEXT_DARK, TEXT_DARK, RED)
        if self.pk is not None:
            remain = max(0, (self.pk["end_ms"] - pygame.time.get_ticks()) // 1000)
            labels = ("对战", "我方", "对方", "时间")
            status = ("领先" if self.score > self.pk["opp"]
                      else "落后" if self.score < self.pk["opp"] else "平局")
            values = (status, str(self.score), str(self.pk["opp"]),
                      str(remain))
            # 最后 10 秒红色闪烁
            flash = remain <= 10 and (pygame.time.get_ticks() // 300) % 2 == 0
            val_colors = (TEXT_DARK, TEXT_DARK, (50, 130, 200),
                          (255, 40, 60) if flash else RED)
        bw = (WIN_W - 24 - 24) / 4
        x = 12
        for i in range(4):
            rect = pygame.Rect(int(x), 48, int(bw), 46)
            self._draw_panel(rect, radius=12)
            # 对方刚加分：格子亮黄高亮 0.7 秒
            if self.pk is not None and i == 2:
                age = pygame.time.get_ticks() - self.pk["opp_flash"]
                if 0 <= age < 700:
                    hl = pygame.Surface(rect.size, pygame.SRCALPHA)
                    hl.fill((255, 210, 80, int(110 * (1 - age / 700))))
                    self.screen.blit(hl, rect.topleft)
                    pygame.draw.rect(self.screen, (255, 170, 40), rect,
                                     3, border_radius=12)
            lb = self.f_stat_label.render(labels[i], True, TEXT_SOFT)
            self.screen.blit(lb, lb.get_rect(center=(rect.centerx, 60)))
            vl = self.f_stat_val.render(values[i], True, val_colors[i])
            self.screen.blit(vl, vl.get_rect(center=(rect.centerx, 80)))
            x += bw + 8

        # 进度条（木质框素材 + 圆角内部填充；PK 模式为双人对战条）
        p_x, p_y, p_w, p_h = 12, 100, WIN_W - 24, 54
        self.screen.blit(self.art.proc_frame, (p_x, p_y))
        in_x, in_y = p_x + 13, p_y + 14
        in_w, in_h = p_w - 26, 26
        if self.pk is not None:
            my, opp = self.score, self.pk["opp"]
            top = max(my, opp, 1)
            half = (in_h - 4) // 2
            pygame.draw.rect(self.screen, PROGRESS_BG,
                             (in_x, in_y, in_w, in_h), border_radius=8)
            w1 = max(half, int(in_w * my / top)) if my else 0
            w2 = max(half, int(in_w * opp / top)) if opp else 0
            if w1:
                pygame.draw.rect(self.screen, PROGRESS_RED,
                                 (in_x, in_y, w1, half), border_radius=6)
            if w2:
                pygame.draw.rect(self.screen, (80, 170, 255),
                                 (in_x, in_y + half + 4, w2, half),
                                 border_radius=6)
            vs = self.f_small.render("%d : %d" % (my, opp), True, TEXT_DARK)
            self.screen.blit(vs, vs.get_rect(
                midright=(in_x + in_w - 10, in_y + in_h // 2)))
        else:
            pygame.draw.rect(self.screen, PROGRESS_BG,
                             (in_x, in_y, in_w, in_h), border_radius=in_h // 2)
            pct = max(0, min(1, (self.score - self.level_start_score) / self.target))
            if pct > 0:
                fw = max(in_h, int(in_w * pct))
                pygame.draw.rect(self.screen, PROGRESS_RED,
                                 (in_x, in_y, fw, in_h),
                                 border_radius=in_h // 2)
            # 目标文字：深色（浅色槽底上白字看不清），对齐到槽内右侧居中
            cur = min(self.target, self.score - self.level_start_score)
            tgt = self.f_small.render("%d / %d" % (cur, self.target),
                                      True, TEXT_DARK)
            self.screen.blit(tgt, tgt.get_rect(
                midright=(in_x + in_w - 10, in_y + in_h // 2)))

    def _draw_select_box(self, cell, phase, hint=False):
        """选中/提示框：发光底 + 素材图片 + 脉动亮色描边。"""
        r, c = cell
        cx = BOARD_X + c * CELL + CELL // 2
        cy = BOARD_Y + r * CELL + CELL // 2
        color = HINT_COLOR if hint else SELECT_COLOR
        pulse = 0.5 + 0.5 * math.sin(phase)          # 0..1 呼吸

        # 发光底：半透明色圆角方块铺满格子
        glow = pygame.Surface((CELL - 2, CELL - 2), pygame.SRCALPHA)
        glow.fill(color + (int(70 + 60 * pulse),))
        self.screen.blit(glow, glow.get_rect(center=(cx, cy)))

        # 素材框（呼吸缩放）
        img = self.art.circle_choose if hint else self.art.choose
        size = int((CELL - 4) * (1.0 + 0.08 * math.sin(phase)))
        img2 = pygame.transform.smoothscale(img, (size, size))
        self.screen.blit(img2, img2.get_rect(center=(cx, cy)))

        # 外层脉动描边（宽度 3~5px）
        bw = 3 + int(2 * pulse)
        rect = pygame.Rect(0, 0, CELL - 2, CELL - 2)
        rect.center = (cx, cy)
        pygame.draw.rect(self.screen, color, rect, bw, border_radius=10)

    def _draw_board(self, now_ms):
        # 棋盘：圆角奶白底板 + 柔和外圈
        bg = pygame.Rect(BOARD_X, BOARD_Y, COLS * CELL, ROWS * CELL)
        pygame.draw.rect(self.screen, BOARD_EDGE, bg.inflate(10, 10),
                         border_radius=16)
        pygame.draw.rect(self.screen, BOARD_BG, bg.inflate(4, 4),
                         border_radius=12)
        # 每格圆角小方块底
        for r in range(ROWS):
            for c in range(COLS):
                pygame.draw.rect(self.screen, (247, 236, 232),
                                 (BOARD_X + c * CELL + 2,
                                  BOARD_Y + r * CELL + 2,
                                  CELL - 4, CELL - 4), border_radius=8)

        hint_on = bool(self.hint and now_ms < self.hint[4])
        if self.hint and now_ms >= self.hint[4]:
            self.hint = None
        hint_cells = set()
        if hint_on:
            hint_cells = {(self.hint[0], self.hint[1]),
                          (self.hint[2], self.hint[3])}

        # 元素（平滑缩放；选中的糖果呼吸放大，更醒目）
        for r in range(ROWS):
            for c in range(COLS):
                g = self.board.grid[r][c]
                if g is None or g.alpha <= 0.02:
                    continue
                is_sel = self.selected == (r, c)
                size = max(1, int(TILE * g.scale))
                if is_sel:
                    size = int(size * (1.10 + 0.08 * math.sin(now_ms / 110)))
                highlighted = is_sel or ((r, c) in hint_cells)
                img = self.art.scaled(g, size, highlighted)
                img.set_alpha(int(255 * g.alpha))
                self.screen.blit(img, img.get_rect(center=(int(g.x), int(g.y))))
                # 彩虹糖：六颗彩色圆点绕圈 + 白色中心圆点
                if g.special == "rainbow":
                    dot = max(3, size // 12)
                    for i in range(6):
                        ang = now_ms / 500 + i * math.pi / 3
                        px = g.x + math.cos(ang) * size * 0.30
                        py = g.y + math.sin(ang) * size * 0.30
                        pygame.draw.circle(self.screen, TYPE_COLORS[i][0],
                                           (int(px), int(py)), dot)
                    pygame.draw.circle(self.screen, WHITE,
                                       (int(g.x), int(g.y)),
                                       int(dot * 1.2))

        # 光束（直角白色矩形）
        for d, i, life in self.beams:
            alpha = int(170 * life)
            if d == "h":
                s = pygame.Surface((COLS * CELL, 16), pygame.SRCALPHA)
                s.fill((255, 255, 255, alpha))
                self.screen.blit(s, (BOARD_X, BOARD_Y + i * CELL + CELL // 2 - 8))
            else:
                s = pygame.Surface((16, ROWS * CELL), pygame.SRCALPHA)
                s.fill((255, 255, 255, alpha))
                self.screen.blit(s, (BOARD_X + i * CELL + CELL // 2 - 8, BOARD_Y))

        # 冲击波 → 圆形扩散环
        for x, y, rad, life in self.waves:
            s = pygame.Surface((int(rad) * 2 + 8, int(rad) * 2 + 8),
                               pygame.SRCALPHA)
            pygame.draw.circle(s, (255, 255, 255, int(200 * life)),
                               (s.get_width() // 2, s.get_height() // 2),
                               int(rad), 4)
            self.screen.blit(s, (int(x) - s.get_width() // 2,
                                 int(y) - s.get_height() // 2))

        # 粒子 → 圆形（生命末期逐渐变暗）
        for p in self.particles:
            k = max(0, p.life / p.max_life)
            col = tuple(int(ch * k + 40 * (1 - k)) for ch in p.color)
            pygame.draw.circle(self.screen, col,
                               (int(p.x), int(p.y)), max(1, int(p.size)))

        # 选中 / 提示框（画在元素上层）
        if self.selected:
            self._draw_select_box(self.selected, now_ms / 140)
        if hint_on:
            for cell in hint_cells:
                self._draw_select_box(cell, now_ms / 160, hint=True)

        # 飘字（描边文字）
        for ft in self.floats:
            a = max(0, min(255, int(255 * min(1, ft.life * 1.6))))
            fnt = self.f_stat_val if ft.size <= 20 else self.f_panel_title
            img = fnt.render(ft.text, True, ft.color)
            outline = fnt.render(ft.text, True, (150, 80, 70))
            img.set_alpha(a)
            outline.set_alpha(a)
            rect = img.get_rect(center=(int(ft.x), int(ft.y)))
            for dx, dy in ((-2, 0), (2, 0), (0, -2), (0, 2)):
                self.screen.blit(outline, rect.move(dx, dy))
            self.screen.blit(img, rect)

        # 定时小鬼（画在棋盘最上层）
        if self.imp:
            boom_t, rr, cc = self.imp
            remain = max(0, (boom_t - now_ms) / IMP_MS)
            x, y = cell_cx(cc), cell_cy(rr)
            pulse = 1.0 + 0.12 * math.sin(now_ms / 70)
            r = int(14 * pulse)
            body = pygame.Surface((r * 4, r * 4), pygame.SRCALPHA)
            pygame.draw.circle(body, (120, 40, 180, 235), (r * 2, r * 2), r)
            # 眼睛
            for sx in (-6, 6):
                pygame.draw.circle(body, (255, 255, 255),
                                   (r * 2 + sx, r * 2 - 3), 4)
                pygame.draw.circle(body, (40, 0, 60),
                                   (r * 2 + sx, r * 2 - 2), 2)
            self.screen.blit(body, body.get_rect(center=(int(x), int(y))))
            # 倒计时圆环（越来越红、越细）
            rr2 = CELL // 2 - 4
            col = (255, int(60 + 120 * (1 - remain)), 60)
            ring = pygame.Surface((rr2 * 2 + 6, rr2 * 2 + 6),
                                  pygame.SRCALPHA)
            pygame.draw.circle(ring, col + (255,), (rr2 + 3, rr2 + 3), rr2,
                               max(2, int(2 + 3 * remain)))
            self.screen.blit(ring, ring.get_rect(center=(int(x), int(y))))

    # ---------- 道具 UI ----------
    ITEM_BAR_Y = BOARD_Y + ROWS * CELL + 64
    ITEM_BAR_H = 34

    def _item_slot_rects(self):
        gap = 6
        w = (WIN_W - 16 - gap * 4) / 5
        return [pygame.Rect(int(8 + i * (w + gap)), self.ITEM_BAR_Y,
                            int(w), self.ITEM_BAR_H) for i in range(5)]

    def _draw_energy_bar(self):
        if self.pk is None:
            return
        x, y = BOARD_X, BOARD_Y - 8
        w, h = COLS * CELL, 6
        pygame.draw.rect(self.screen, (120, 90, 110),
                         (x - 1, y - 1, w + 2, h + 2), border_radius=4)
        full = self.energy >= ENERGY_MAX
        if self.energy > 0:
            col = (255, 205, 70) if full else (255, 140, 110)
            fw = int(w * self.energy / ENERGY_MAX)
            pygame.draw.rect(self.screen, col, (x, y, fw, h),
                             border_radius=3)
        if full:
            lb = self.f_small.render("能量已满，点道具释放", True,
                                     (255, 205, 70))
            self.screen.blit(lb, lb.get_rect(midright=(x + w, y - 8)))

    def _draw_item_bar(self):
        for i, (key, name, theme) in enumerate(ITEM_DEFS):
            rect = self._item_slot_rects()[i]
            ready = self._item_ready(key)
            if key == "shield" and self.shield_held:
                fill, edge = (90, 180, 255), (255, 255, 255)
            elif ready:
                fill = theme
                edge = (255, 230, 120)
            else:
                fill = (160, 155, 170)
                edge = None
            pygame.draw.rect(self.screen, fill, rect, border_radius=8)
            if edge and (pygame.time.get_ticks() // 250) % 2 == 0:
                pygame.draw.rect(self.screen, edge, rect, 2, border_radius=8)
            sub = name if not (key == "shield" and self.shield_held) \
                else "已装备"
            t = self.f_small.render(sub, True,
                                    WHITE if ready or self.shield_held
                                    else (230, 230, 235))
            self.screen.blit(t, t.get_rect(center=rect.center))

    def _draw_item_fx(self, now_ms):
        """迷雾 / 糖纸遮罩（在元素与按钮之后绘制）。"""
        if self.fog_end and now_ms < self.fog_end:
            fog = pygame.Surface((COLS * CELL, ROWS * CELL), pygame.SRCALPHA)
            fog.fill((212, 216, 232, 150))
            for x, y, r in ((60, 80, 26), (280, 200, 32), (150, 330, 22),
                            (360, 90, 18)):
                pygame.draw.circle(fog, (255, 255, 255, 40), (x, y), r)
            self.screen.blit(fog, (BOARD_X, BOARD_Y))
        if self.paper and now_ms < self.paper[0]:
            _t, rr, cc = self.paper
            x = BOARD_X + (cc - 1) * CELL
            y = BOARD_Y + (rr - 1) * CELL
            box = pygame.Rect(x, y, CELL * 3, CELL * 3)
            pygame.draw.rect(self.screen, (255, 235, 245), box,
                             border_radius=10)
            pygame.draw.rect(self.screen, (235, 150, 175), box, 4,
                             border_radius=10)
            for k in range(-3, 4):
                p1 = (box.x + max(0, k * 24),
                      box.bottom - max(0, -k * 24))
                p2 = (box.x + min(box.w, box.w + k * 24),
                      box.y + max(0, k * 24))
                pygame.draw.line(self.screen, (250, 200, 215), p1, p2, 2)
            t = self.f_panel_title.render("糖", True, (220, 120, 150))
            self.screen.blit(t, t.get_rect(center=box.center))

        # 横幅
        if self.banner and now_ms < self.banner[1]:
            text, _t, col = self.banner
            ts = self.f_btn.render(text, True, WHITE)
            w, h = ts.get_width() + 40, 40
            panel = pygame.Surface((w, h), pygame.SRCALPHA)
            panel.fill((60, 40, 90, 210))
            self.screen.blit(panel, panel.get_rect(
                center=(WIN_W // 2, BOARD_Y + 26)))
            self.screen.blit(ts, ts.get_rect(
                center=(WIN_W // 2, BOARD_Y + 26)))

    def _draw_buttons(self):
        for rect, label, action in self._buttons:
            if action == "restart":
                self._draw_button(rect, RED, (200, 70, 75))
            else:
                self._draw_button(rect, PURPLE_BTN, (110, 88, 190))
                if action == "sound":
                    label = ("音效:开" if self.sound.on else "音效:关")
            txt = self.f_btn.render(label, True, WHITE)
            self.screen.blit(txt, txt.get_rect(center=rect.center))
        if self.pk is not None:
            # PK：道具条下方显示剩余次数与操作提示
            left = MAX_ITEM_USES - self.items_used
            t1 = self.f_small.render("道具剩余 %d 次" % left, True, WHITE)
            self.screen.blit(t1, t1.get_rect(midleft=(12, WIN_H - 16)))
            t2 = self.f_small.render("能量满后点道具释放，护盾自动抵挡",
                                     True, (255, 245, 220))
            self.screen.blit(t2, t2.get_rect(midright=(WIN_W - 12,
                                                        WIN_H - 16)))
        else:
            tip = self.f_small.render(
                "点选两颗相邻糖果交换，也可按住拖动交换",
                True, (255, 255, 255))
            self.screen.blit(tip, tip.get_rect(center=(WIN_W / 2,
                                                        WIN_H - 18)))

    def _draw_overlay(self):
        layer = pygame.Surface((WIN_W, WIN_H), pygame.SRCALPHA)
        layer.fill((120, 60, 80, 150))
        self.screen.blit(layer, (0, 0))

        is_menu = self.state == STATE_MENU
        is_pk = self.result in ("pk_win", "pk_lose", "pk_draw")
        # 菜单 / PK 且可再来一局：面板加高放两个按钮
        pk_two_btns = is_pk and self.after_pk is not None
        h = 340 if (is_menu or pk_two_btns) else 300
        panel = pygame.Rect(0, 0, 320, h)
        panel.center = (WIN_W // 2, WIN_H // 2)
        self._draw_panel(panel, radius=18)

        btn2_label = None
        if is_menu:
            title, lines, btn_label = "欢迎来玩消消乐", [
                "交换相邻糖果，凑成三个或更多",
                "同色即可消除",
                "四连出条纹糖，五连出彩虹糖",
                "拐角出炸弹糖！"], "开始游戏"
            btn2_label = "局域网对战"
        elif is_pk:
            title = {"pk_win": "你赢了！", "pk_lose": "惜败…",
                     "pk_draw": "平局！"}[self.result]
            my, opp = self.pk_final or (self.score, 0)
            lines = ["我方 %d 分" % my, "对方 %d 分" % opp]
            if pk_two_btns:
                btn_label, btn2_label = "再来一局", "返回菜单"
                myr, opr = self.my_rematch, self.after_pk["opp_rematch"]
                if myr and opr:
                    lines.append("双方同意，正在开始…")
                elif myr:
                    lines.append("已请求，等待对方确认…")
                elif opr:
                    lines.append("对方想再来一局！")
            else:
                # 对方掉线/离开，无连接，只能返回
                btn_label = "返回菜单"
        else:
            earned = self.score - self.level_start_score
            if self.result == "win":
                title, btn_label = "恭喜过关！", "下一关"
                lines = ["本关得分 %d" % earned,
                         "累计总分 %d" % self.score]
            else:
                title, btn_label = "步数用完啦", "再试一次"
                lines = ["本关得分 %d" % earned,
                         "目标 %d，再试一次吧" % self.target]

        tt = self.f_panel_title.render(title, True, TEXT_DARK)
        self.screen.blit(tt, tt.get_rect(center=(panel.centerx, panel.y + 52)))
        for i, line in enumerate(lines):
            lt = self.f_panel_text.render(line, True, TEXT_SOFT)
            self.screen.blit(lt, lt.get_rect(center=(panel.centerx,
                                                     panel.y + 108 + i * 30)))
        btn_y = panel.bottom - (116 if btn2_label else 70)
        self._overlay_btn.update(panel.centerx - 100, btn_y, 200, 48)
        # PK 结算主按钮"再来一局"用红色强调；其余场景主按钮紫色
        if is_pk:
            main_fill, main_sh = RED, (200, 70, 75)
        else:
            main_fill, main_sh = PURPLE_BTN, (110, 88, 190)
        self._draw_button(self._overlay_btn, main_fill, main_sh)
        bt = self.f_btn.render(btn_label, True, WHITE)
        self.screen.blit(bt, bt.get_rect(center=self._overlay_btn.center))
        if btn2_label:
            self._overlay_btn2.update(panel.centerx - 100, panel.bottom - 60,
                                      200, 44)
            # PK 次按钮"返回菜单"用紫色；菜单次按钮红色
            if is_pk:
                sub_fill, sub_sh = PURPLE_BTN, (110, 88, 190)
            else:
                sub_fill, sub_sh = RED, (200, 70, 75)
            self._draw_button(self._overlay_btn2, sub_fill, sub_sh)
            bt2 = self.f_btn.render(btn2_label, True, WHITE)
            self.screen.blit(bt2, bt2.get_rect(center=self._overlay_btn2.center))

    def _draw_lan(self, now_ms):
        """LAN 连接界面：建房 / 加入 / 等待 / IP 输入。"""
        layer = pygame.Surface((WIN_W, WIN_H), pygame.SRCALPHA)
        layer.fill((120, 60, 80, 150))
        self.screen.blit(layer, (0, 0))
        L = self._lan_layout()
        panel = L["panel"]
        self._draw_panel(panel, radius=18)

        tt = self.f_panel_title.render("局域网对战", True, TEXT_DARK)
        self.screen.blit(tt, tt.get_rect(center=(panel.centerx, panel.y + 42)))
        if self.lan_mode == "join":
            sub_text = "双方同棋盘，对局时长由主机设置"
        else:
            shown_dur = (self.pk_duration if self.lan_mode == "host"
                         else PK_DURATION)
            sub_text = "双方同棋盘，%d 秒内得分高者胜" % shown_dur
        sub = self.f_small.render(sub_text, True, TEXT_SOFT)
        self.screen.blit(sub, sub.get_rect(center=(panel.centerx, panel.y + 74)))

        if self.lan_mode is None:
            for key, label in (("host", "创建房间"), ("join", "加入房间")):
                self._draw_button(L[key], PURPLE_BTN, (110, 88, 190))
                bt = self.f_btn.render(label, True, WHITE)
                self.screen.blit(bt, bt.get_rect(center=L[key].center))
        elif self.lan_mode == "host":
            ip = self.f_panel_text.render("本机 IP：%s（告诉对方）"
                                          % get_lan_ip(), True, TEXT_DARK)
            self.screen.blit(ip, ip.get_rect(center=(panel.centerx,
                                                     panel.y + 118)))
            # 时长选择
            dl = self.f_small.render("对局时长", True, TEXT_DARK)
            self.screen.blit(dl, dl.get_rect(center=(panel.centerx,
                                                     panel.y + 148)))
            for i, rect in enumerate(L["dur_btns"]):
                sel = DURATION_PRESETS[i] == self.pk_duration
                if sel:
                    fill, sh = RED, (200, 70, 75)
                else:
                    fill, sh = PURPLE_BTN, (110, 88, 190)
                self._draw_button(rect, fill, sh, radius=8)
                bt = self.f_small.render(
                    "%d 秒" % DURATION_PRESETS[i], True, WHITE)
                self.screen.blit(bt, bt.get_rect(center=rect.center))
            if self.lan_link is not None:
                self._draw_button(L["go"], RED, (200, 70, 75))
                bt = self.f_btn.render("开始对战", True, WHITE)
                self.screen.blit(bt, bt.get_rect(center=L["go"].center))
        else:  # join
            box = L["input"]
            pygame.draw.rect(self.screen, (250, 244, 246), box,
                             border_radius=8)
            pygame.draw.rect(self.screen, TEXT_SOFT, box, 2, border_radius=8)
            text = self.lan_ip
            if self.lan_link is None and (now_ms // 500) % 2 == 0:
                text += "|"
            it = self.f_panel_text.render(text, True, TEXT_DARK)
            self.screen.blit(it, it.get_rect(midleft=(box.x + 12,
                                                      box.centery)))
            if self.lan_link is None:
                self._draw_button(L["connect"], PURPLE_BTN, (110, 88, 190))
                bt = self.f_btn.render("连接", True, WHITE)
                self.screen.blit(bt, bt.get_rect(center=L["connect"].center))

        # 状态提示（错误用红色）
        if self.lan_status:
            err = any(k in self.lan_status for k in ("失败", "断开", "离开"))
            st = self.f_panel_text.render(self.lan_status, True,
                                          RED if err else TEXT_SOFT)
            self.screen.blit(st, st.get_rect(center=(panel.centerx,
                                                     panel.bottom - 132)))

        self._draw_button(L["back"], (200, 180, 190), (170, 145, 155))
        bt = self.f_small.render("返回菜单", True, WHITE)
        self.screen.blit(bt, bt.get_rect(center=L["back"].center))

    def draw(self, now_ms):
        self._draw_background()
        if self.state == STATE_LAN:
            self._draw_board(now_ms)
            self._draw_lan(now_ms)
        else:
            self._draw_hud()
            self._draw_energy_bar()
            self._draw_board(now_ms)
            self._draw_buttons()
            if self.pk is not None:
                self._draw_item_bar()
            self._draw_item_fx(now_ms)
            if self.state in (STATE_MENU, STATE_OVER):
                self._draw_overlay()
        pygame.display.flip()

    # ==================== 主循环 ====================
    def run(self):
        while True:
            dt = self.clock.tick(FPS) / 1000.0
            for event in pygame.event.get():
                if self.handle_event(event) is False:
                    pygame.quit()
                    return
            self.handle_mouse()
            if self.state == STATE_LAN:
                self._poll_lan()
            elif self.state == STATE_OVER:
                self._poll_rematch()
            self._poll_pk()
            if self.state == STATE_PLAY:
                self._process_item_timing()
                self._update_idle_tw(dt)
            self._update_gen(dt)
            self._update_effects(dt)
            self.draw(pygame.time.get_ticks())


def main():
    Game().run()


if __name__ == "__main__":
    main()
