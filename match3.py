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


# ==================== 主游戏类 ====================
class Game:
    BEST_FILE = os.path.join(os.path.dirname(os.path.abspath(__file__)),
                             "best.json")

    def __init__(self):
        pygame.init()
        pygame.display.set_caption("消消乐")
        self.screen = pygame.display.set_mode((WIN_W, WIN_H))
        self.clock = pygame.time.Clock()

        # 中文字体（Windows 自带微软雅黑）
        def font(size, bold=False):
            f = pygame.font.SysFont("microsoftyahei,simhei", size)
            f.set_bold(bold)
            return f
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
        return self.state != STATE_PLAY or self.gen is not None

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
            return False
        if event.type == pygame.KEYDOWN and event.key == pygame.K_ESCAPE:
            return False

        if event.type == pygame.MOUSEBUTTONDOWN and event.button == 1:
            # 菜单 / 结束面板的按钮
            if self.state in (STATE_MENU, STATE_OVER):
                if self._overlay_btn.collidepoint(event.pos):
                    if self.state == STATE_MENU:
                        self.start_level()
                    elif self.result == "win":
                        self.start_level(inc=True)
                    else:
                        self.start_level(retry=True)
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
        bw = (WIN_W - 24 - 24) / 4
        x = 12
        for i in range(4):
            rect = pygame.Rect(int(x), 48, int(bw), 46)
            self._draw_panel(rect, radius=12)
            lb = self.f_stat_label.render(labels[i], True, TEXT_SOFT)
            self.screen.blit(lb, lb.get_rect(center=(rect.centerx, 60)))
            vl = self.f_stat_val.render(values[i], True, val_colors[i])
            self.screen.blit(vl, vl.get_rect(center=(rect.centerx, 80)))
            x += bw + 8

        # 进度条（木质框素材 + 圆角内部填充）
        p_x, p_y, p_w, p_h = 12, 100, WIN_W - 24, 54
        self.screen.blit(self.art.proc_frame, (p_x, p_y))
        in_x, in_y = p_x + 13, p_y + 14
        in_w, in_h = p_w - 26, 26
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
        """选中/提示框：素材图片 + 呼吸缩放脉动。"""
        r, c = cell
        img = self.art.circle_choose if hint else self.art.choose
        k = 1.0 + 0.06 * math.sin(phase)
        size = int((CELL - 4) * k)
        img2 = pygame.transform.smoothscale(img, (size, size))
        self.screen.blit(img2, img2.get_rect(
            center=(BOARD_X + c * CELL + CELL // 2,
                    BOARD_Y + r * CELL + CELL // 2)))

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

        # 元素（最近邻缩放，硬边像素感）
        for r in range(ROWS):
            for c in range(COLS):
                g = self.board.grid[r][c]
                if g is None or g.alpha <= 0.02:
                    continue
                is_sel = self.selected == (r, c)
                size = max(1, int(TILE * g.scale))
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
        tip = self.f_small.render("点选两颗相邻糖果交换，也可按住拖动交换",
                                  True, (255, 255, 255))
        self.screen.blit(tip, tip.get_rect(center=(WIN_W / 2, WIN_H - 18)))

    def _draw_overlay(self):
        layer = pygame.Surface((WIN_W, WIN_H), pygame.SRCALPHA)
        layer.fill((120, 60, 80, 150))
        self.screen.blit(layer, (0, 0))

        panel = pygame.Rect(0, 0, 320, 300)
        panel.center = (WIN_W // 2, WIN_H // 2)
        self._draw_panel(panel, radius=18)

        if self.state == STATE_MENU:
            title, lines, btn_label = "欢迎来玩消消乐", [
                "交换相邻糖果，凑成三个或更多",
                "同色即可消除",
                "四连出条纹糖，五连出彩虹糖",
                "拐角出炸弹糖！"], "开始游戏"
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
        self._overlay_btn.update(panel.centerx - 100, panel.bottom - 70, 200, 48)
        self._draw_button(self._overlay_btn, PURPLE_BTN, (110, 88, 190))
        bt = self.f_btn.render(btn_label, True, WHITE)
        self.screen.blit(bt, bt.get_rect(center=self._overlay_btn.center))

    def draw(self, now_ms):
        self._draw_background()
        self._draw_hud()
        self._draw_board(now_ms)
        self._draw_buttons()
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
            self._update_gen(dt)
            self._update_effects(dt)
            self.draw(pygame.time.get_ticks())


def main():
    Game().run()


if __name__ == "__main__":
    main()
