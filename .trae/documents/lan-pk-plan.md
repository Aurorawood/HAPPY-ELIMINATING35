# 局域网双人 PK 实现计划

## Context
用户希望消消乐（`d:\小游戏\消消乐\match3.py`，pygame 单文件游戏）支持局域网双人 PK：两台电脑同一局域网对战，**90 秒限时比分数，得分高者胜，双方使用相同初始棋盘（同随机种子）保证公平**。无需公网服务器，一台做主机即可。

## 总体设计
- **网络**：TCP socket，主机监听端口 `50007`；加入方输入主机 IP 连接。协议为 JSON 行（每行一个 JSON 对象）。
- **线程**：网络收发放后台线程，收到消息推入 `queue.Queue`；pygame 主循环每帧 `poll` 队列处理，绝不阻塞渲染线程。
- **状态机**：新增 `STATE_LAN`（连接/等待界面）；对战中复用 `STATE_PLAY` + `self.pk` 上下文对象；结算复用 `STATE_OVER` 的 overlay，新增 `result = "pk_win"/"pk_lose"/"pk_draw"`。
- **公平性**：主机生成随机种子发给双方，双方 `random.seed(seed)` 后各自 `Board()`，初始棋盘一致；之后各自独立操作。

## 协议消息（JSON 行）
| 方向 | 消息 | 说明 |
|---|---|---|
| 客→主 | `{"t":"join"}` | 连接建立后发送 |
| 主→客 | `{"t":"start","seed":N,"duration":90}` | 主机点击"开始对战"后广播 |
| 双向 | `{"t":"score","score":N}` | 每次得分变化时发送（消除流程结束后） |
| 双向 | `{"t":"bye"}` | 主动退出/返回菜单 |
| 底层 | TCP 断开 | 判对方掉线，直接获胜 |

## 实现步骤（全部改在 match3.py）

### 1. 网络模块（文件内新增，约 120 行）
- `class LanLink`：封装 socket + 后台接收线程 + 收发队列
  - `host(port=50007)` / `join(ip, port)` 类方法
  - `send(dict)`：JSON + `\n` 写入（发送加锁）
  - `poll()`：从队列取所有待处理消息返回列表
  - `close()`：关闭
  - 接收线程按 `\n` 分包解 JSON，异常/断开推 `{"t":"_closed"}` 到队列

### 2. PK 上下文与状态
- 常量：`STATE_LAN = "lan"`、`LAN_PORT = 50007`、`PK_DURATION = 90`
- `Game.__init__` 增加：`self.pk = None`（对战上下文：link、对方分数、结束时刻、种子）、LAN 界面输入框状态（`lan_mode` None/"host"/"join"、`lan_ip` 字符串、`lan_status` 提示文字）
- `start_pk(seed, link)`：重置分数为 0、`random.seed(seed)`、新建 Board、`self.pk = {...}`、记录 `pk_end_ms = now + 90000`、`state = STATE_PLAY`、走 `_flow_init()` 落入动画

### 3. LAN 界面（菜单入口 + 连接流程）
- 菜单 overlay 面板加高，在"开始游戏"下加第二个按钮"局域网对战"→ 进入 `STATE_LAN`
- `STATE_LAN` 界面（复用 `_draw_panel`/`_draw_button` 圆角组件）：
  - 初始：两个按钮"创建房间"/"加入房间" + "返回菜单"
  - 创建房间：显示本机内网 IP（`socket.gethostbyname(gethostname())`，失败则遍历接口）+"等待对方加入…"，对方 join 后出现"开始对战"按钮
  - 加入房间：IP 输入框（KEYDOWN 处理数字/点/退格/回车）+ "连接"按钮；连上后显示"等待主机开始…"
  - 错误提示：连接失败/对方离开显示红色状态文字

### 4. 对战中改动
- HUD：PK 模式下"步数"格显示**剩余秒数**（红色，最后 10 秒闪烁）；进度条改为**双人对战条**：上半自己（PROGRESS_RED）/下半对方（青色），中间显示比分 `我:对方`
- 每次消除流程结束（`_flow_swap`/`_flow_resolve` 末尾）若 `self.pk` 存在且分数变化 → `link.send({"t":"score",...})`
- 主循环每帧 `pk.poll()` 处理消息：更新对方分数 / 对方离开 → 立即结算获胜
- 每帧检查 `now >= pk_end_ms` → 结算：`pk_win`/`pk_lose`/`pk_draw`，关闭 link

### 5. 结算与退出
- `_draw_overlay` 增加 PK 结算文案：胜"你赢了！"/负"惜败…"/平局，显示双方比分，按钮"返回菜单"
- 返回菜单/窗口关闭/ESC 时：若 `self.pk`，发送 `bye` 并 `close()`
- `_busy()` 等逻辑不受影响（仍是 STATE_PLAY）

## 验证
1. **协议单测**（dummy 驱动 + socketpair）：模拟两条 LanLink 互发 join/start/score，断言双方收到且解析正确
2. **本机双开联测**：开两个进程，一个建房一个连 `127.0.0.1`，验证：连接→开始→双方同棋盘（对比首屏 grid 哈希）→分数实时互显→90 秒结算→断线判负
3. 无界面冒烟回归（既有 20 种子测试）确认单人模式不受影响
4. 真机两台电脑实测（用户手动）

## 注意
- Windows 防火墙首次会弹"允许访问网络"提示，需允许
- 不加公网/账号/加密，仅局域网可信环境
- 保持单文件、不新增依赖（socket/queue/threading/json 均标准库）
