# 标准库的远景和路线

`docs/std.md` 定规矩：什么能进来、接口和名字怎么写、怎么测。这份文档定方向：最终要提供哪些能力，按什么顺序做。
新能力进来时仍按 std.md 的“八、新加或修改一个函数的清单”走；这里提到的分层、稳定性都指 std.md 第三节的分法。

## 目标

Lark 主要用来写三类程序，标准库按这三类配齐：

| 场景 | 典型程序 | 已经验证过的 |
| --- | --- | --- |
| 网络服务 | HTTP 服务和客户端、缓存、键值库、代理 | lhttp、lcache、lredis |
| 命令行工具和脚本 | grep、git、编辑器、构建工具、格式化工具 | lgrep、lgit、ledit、tools/ |
| 系统程序 | 解释器、守护进程、读写二进制格式的工具；更远一步是不依赖操作系统的嵌入式代码 | llua、lgit 的对象存储 |

范围按 std.md 第二节，向 Go 靠，什么都带。衡量的标准是一句话：**用标准库写 lhttp、lgrep 这样的程序，不需要第三方代码，也不需要自己再实现一遍协议或算法。**

## 能力地图

每一项标出状态：
- **有**：已经满足这类程序的需要；
- **补**：模块已经有，缺一部分；
- **新**：还没有这个模块；
- **不做**：明确不进标准库。

新模块按 std.md 第三节放进一层；稳定性一律从“协议和格式”那一档开始，有两个程序用过以后再考虑升到核心档。

### 计算层

| 能力 | 状态 | 要做的 |
| --- | --- | --- |
| 字符串、UTF-8、格式化、容器 | 有 | 公开类型都有 `show`（阶段 0 做完） |
| 排序、迭代器 | 做完（2026-10） | sort 的 `binary_search` / `lower_bound` / `upper_bound` / `dedup` 做完（2026-10）；iter 合并成一套（2026-10）：适配器去掉 `lazy_` 前缀，按第一个参数重载、列表直接当来源 |
| 字节和二进制编码 | 有 | `std/bytes`：按大端 / 小端读写 u16、u32，大端的 u64（换掉了 zlib、digest、lgit 各自写的版本）。可增长的缓冲就是 `[u8]`，不另外做 `Buffer`；变长整数（varint）、小端的 u64 等有程序要用时再加 |
| 大整数、十进制 | 不做（暂定） | Go 有 math/big；等有程序要用再说 |

### 系统层

| 能力 | 状态 | 要做的 |
| --- | --- | --- |
| 文件、目录、路径 | 有 | 阶段 1 加了权限位（`FileInfo.mode`、`chmod`）和符号链接（`lstat`、`symlink`、`read_link`），lgit 用它记录、恢复可执行权限；lgit 还不支持把符号链接存进仓库 |
| 子进程 | 做完（2026-10） | `proc.run_opts` 加了环境变量（设置、覆盖、去掉）和超时（连同它启动的进程一起结束）；标准错误本来就单独收在 `o.err` 里 |
| 信号 | 有 | `std/signal`：`notify(sigs)` 先登记，`wait()` 在任务里等（Go 的 signal.Notify；先做成函数，一个任务等就够用，有了 timer 以后再看要不要能放进 select）。lredis、lhttp、lcache 收到 SIGINT / SIGTERM 写日志退出；还不会等进行中的连接做完 |
| 定时器 | 有 | `std/timer`：`deadline(ms)`（几次等待共用一个截止时间，`after d.left_ms()`）、`every(ms)`（按开始的时刻对齐的间隔，`after t.next_ms()` 或 `t.wait()`）。没有做成 `Chan`：`select` 已经有 `after`，缺的只是这两种算法；lcache 的清理任务在用 |
| 取消、读写锁、原子计数 | 补 | `std/sync` 有了 `Cancel`（`new_cancel`、`cancel`、`is_cancelled`、`watch() -> Chan[bool]` 给 select 用、`wait`），lcache 用它让清理的任务退出。读写锁、原子整数、Once 等有程序要用时再加：现在用 `Mutex` 就够 |
| TCP | 有 | net |
| UDP、Unix 域套接字、DNS | 有 | 阶段 2 加了 `listen_unix` / `connect_unix`、`listen_udp`（`send_to`、`recv_from`，收的时候任务挂起）、`lookup(host) -> [str]!`。还没有：组播、广播、`connect` 带超时（现在连接时占着系统线程） |
| 时区数据库 | 不做 | 维持 std.md 第二节 |

### 格式和协议层

| 能力 | 状态 | 要做的 |
| --- | --- | --- |
| JSON、CSV、base64 | 有 | 解码返回 `T!`、错误信息带位置（阶段 0 做完） |
| 正则 | 有 | 阶段 1 换成了 Pike VM（线性时间，乱测不再要截短模式），加了分组（`captures`、`captures_at`）、`{m,n}`、非贪心、`replace_all` 里的 `$1`。不支持反向引用（Go 的 regexp 也不支持）和 `\b`；匹配取靠前的选项（Go 的做法），不是 grep -E 的最长匹配 |
| 压缩、摘要 | 做完（2026-10） | digest 有了 sha512、HMAC（sha1 / sha256 / sha512）和常数时间的 `equal`，签名 Cookie、校验 Webhook 都够用 |
| 命令行参数 | 有 | 阶段 1 加了子命令（`add_command`、`a.command`）和 `parse_or_exit`，构建工具 lark 已经改用。2026-10 加了 `a.dash`（`--` 后面的参数从 `rest` 的哪里开始），lgit 已经改用 flag（每个命令一个子命令，`checkout -- 路径`、`diff 版本 -- 路径` 靠 `a.dash` 分开） |
| HTTP 客户端 | 有 | `http.Client`：复用连接（每个客户端最多 4 条空闲的）、空闲连接被关掉时自动重发可以重发的方法、跟随重定向（`set_max_redirects`，0 表示不跟随）、读写超时（`set_timeout_ms`）。还没有：连接本身的超时（`net.connect` 等的时候占着系统线程）、几个任务共用一个连接池 |
| HTTP 服务 | 有 | `http.serve(l, h)`（每个连接一个任务，keep-alive、流水线、空闲 30 秒关掉）和路由 `new_router` / `handle("GET /items/{id}", h)` / `route` / `param`（Go 1.22 的 ServeMux：取最具体的，405 带 Allow）。lhttp、lcache 已经改用 serve，删掉了各自的连接循环。优雅退出用 `serve_until(l, h, stop)`（lproxy 在用）。还没有：空闲时间可调、限制同时的连接数 |
| TLS / https | 暂缓（2026-10 定） | 先不做，维持 std.md 第二节“不进标准库”；要 https 时在前面放一个系统的 TLS 终结代理（nginx、caddy 等），lproxy 只跟它说 http |
| 配置格式（TOML、YAML） | 不做 | 维持 std.md 第二节 |
| WebSocket、HTTP/2 | 不做（暂定） | Go 也放在 golang.org/x 里 |

### 不依赖操作系统（2026-11 做完）

计算层，加上不 import 系统层的格式模块（json、csv、base64、digest、zlib、re、diff），合起来就是能在嵌入式环境里用的部分。std.md 第三节“只能往下 import”的规矩，现在就保证了这部分不会碰操作系统。

要真正跑在没有操作系统的环境里，要做的四件事（编译器和运行时的工作）都做了：
1. 运行时分成核心和可选的部分（`runtime/lark_rt.h` 开头有说明）。程序没有 import 系统层的模块、也没有用到任务、通道、锁和系统的内置函数时，编译器在生成的 C 开头定义 `LK_CORE`：不带调度器、事件循环、栈溢出保护，也不用 pthread。编译 C 时 `-DLK_FULL` 强制带上全部。
2. 内存分配可以替换：包含运行时之前定义 `LK_MALLOC` / `LK_REALLOC` / `LK_FREE`（比如换成固定大小的内存池）。`tests/alloc/tagged.h` 检查每次申请和释放都经过它们。
3. 定宽整数 `u16`、`u32`、`i32`，规则和 `u8` 一样：只存不算（比较、`& | ^ !`、打印），算术先 `.to_int()`。

4. 没有操作系统（`LK_BARE`）：核心只通过五个 `lark_plat_*` 函数输出、退出、读时间、取随机数，由使用者提供；只用 C 库里不碰系统的部分（内存和字符串函数、`snprintf`、`strtod`、数学函数）。`examples/bare` 是例子：`plat.c` 模拟一块板子（固定大小的内存池），`run.sh` 用 `nm` 检查程序的目标文件不引用 stdio、exit、时钟、系统调用、malloc、pthread（`make check` 里的 `tests/pkg/bare`）。

还没有做的：交叉编译到真的板子上（比如 ARM Cortex-M 加 newlib-nano）还没试过；浮点数的格式化靠 `snprintf`，C 库很小的环境里可能要换掉。

## 已定和待定：要改 std.md 的决定

std.md 第二节把下面两样列在“不进标准库”里。要做网络服务，这两条得重新考虑：

1. **HTTP 服务的入口和路由**（2026-10 定：进标准库，std.md 第二节已改）：
   - 现状：lhttp、lcache、lredis 各写了一遍 accept 循环和请求分发。
   - 建议：加 `http.serve(addr, handler)`，以及按“方法 + 路径模式”分发（Go 1.22 的 ServeMux 那样，`GET /items/{id}`）。中间件、模板仍然不做。
   - std.md 要改的地方：把“HTTP 服务器框架（路由、中间件）”改成“中间件、模板”。
2. **TLS**（2026-10 定：暂缓，阶段 3 往后放，std.md 不改）：
   - 自己实现（Go 的做法）：要先有 AES-GCM、ChaCha20、X25519、证书验证，工作量最大，安全上的责任也最大。
   - 用系统的库（macOS 的 Security.framework、Linux 的 OpenSSL）：做起来快，但打破了“只依赖 libc”。
   - 建议：先用系统的库做 `std/tls`，标明“需要系统里有 OpenSSL”；接口设计成以后可以换成自己的实现。
   - 定下以后，std.md 第二节的“TLS / https”和“加密算法”两条要一起改。

另外两件不急、但迟早要定的：
- **Windows**：暂不支持；接口上不写死 `/` 和 POSIX 特有的东西，路径一律用 os 的函数。
- **包仓库**：`lark.pkg` 已经能从 git 拉依赖；标准库越全，中心仓库越不急。

## 标准

std.md 第七节的测试要求照旧。另外加三条，要改工具：

1. **分层自动检查**：`tools/apicov.lark` 读每个 std 模块的 import，往上层 import 或者成环就失败，进 `make check`。现在这条规矩只写在 std.md 里，靠人看。
2. **热点有基准**：解析、压缩、正则、容器、HTTP 在 `bench/` 里有基准，并且和 C 或 Go 的同类实现比过一次，差距写进 README。现在只有通道和 lredis 有。
3. **两个平台**：macOS 和 Linux 都跑 `make check`（std.md 第十节，等仓库上了 GitHub）。

## 路线

每个阶段都用一个只用标准库写的验收程序收尾，写的过程中发现缺什么当场补。lgrep、lhttp、lredis 就是这样把标准库推出来的。

| 阶段 | 内容 | 验收程序 |
| --- | --- | --- |
| 0 清账（做完） | 公开类型的 `show`；解析错误统一成“格式 位置：原因”；base64、十六进制解码返回 `T!`；去掉 `sha1_hex` / `sha256_hex`；分层自动检查 | 无（`make check` 通过） |
| 1 补基础（做完） | bytes；正则换实现、加分组；os 的权限和符号链接；signal；flag 的子命令 | `apps/ltar`：读写 tar 和 tar.gz（ustar 头、权限位、符号链接、gzip），和系统的 tar 互相解开对方打的包。写的时候补了 flag 的 `-zf 包` 写法；2026-10 加了 os 的 `set_mtime`、`hard_link`，ltar 解包时恢复修改时间、解开硬链接（打包时还不认硬链接：os 的 stat 没有 inode）；还缺边读边写的流式接口（现在整个包读进内存） |
| 2 服务（做完，2026-10） | sync、timer；net 的 UDP、Unix 套接字、lookup；HTTP 客户端的连接复用和超时；http.serve 和路由 | `apps/lproxy`：反向代理，按路径前缀转发、502 / 504、SIGTERM 时优雅退出；lhttp、lcache 已经改用 http.serve，删掉了各自的 accept 循环。写的时候补了 `serve_until`、`net.is_timeout`、`Listener.set_timeout_ms`（运行时的超时错误统一成“：超时”） |
| 3 TLS（暂缓） | 等重新考虑“待定”第 2 条时再做 `std/tls` 和 https 客户端 | `lproxy` 支持 https 上游 |
| 4 不依赖操作系统（做完，2026-11） | 运行时拆成核心和可选部分（`LK_CORE`，编译器自动判断）、可替换的内存分配、定宽整数 u16 / u32 / i32、没有操作系统时的平台函数（`LK_BARE`） | 19 个计算层和格式层的单元测试只带运行时的核心编译、通过（`tools/test.lark` 的 `is_core_unit` 检查）；`examples/bare` 的目标文件不引用 stdio 和系统调用 |

阶段 0 到 2 只动标准库，加少量运行时（信号、定时器、UDP），不改语言；阶段 3、4 先要有“待定”里的决定。
