# 标准库设计指南

`std/` 下的模块都用 Lark 自己写，底下只用运行时里的内置函数和 libc（必要时运行时里加几个 C 函数，用 `extern "c"` 调用）。
这份文档定的是：标准库按什么原则取舍，接口长什么样，名字怎么起，怎么测，怎么改。新加或修改模块、函数之前先看这里；
评审时也按这里来，不靠“感觉合适”。标准库最终要提供哪些能力、按什么顺序做，见 `docs/std-roadmap.md`。

结构：第一节是七条原则，后面每一节的规则都是从原则推出来的，规则后面的括号里写依据。
两条规则冲突、或者遇到这里没写的情况，按原则的先后决定；决定以后把它补成一条规则写进来。
最后一节“现在和规则对不上的地方”是待办清单，改完一项删一项。

## 一、原则

按先后排列，冲突时前面的优先。

1. **正确先于方便。** 外部输入怎么坏都不 panic，只返回错误；不用 -1、`""` 这类特殊值表示“没有”；能出错的函数返回 `T!`，编译器逼着调用者处理。
2. **一件事只有一种做法。** 不收别名、不收两个做同一件事的函数、不收给内置函数换个名字的包装。用户不用比较“哪个更好”，评审也只需要看一处。
3. **照抄成熟的设计。** 名字和语义先找 Rust、Go、Python、Zig、Elixir、Gleam 里的同类接口。和别的语言同名，语义就要一样；对不上就换名字。
4. **读调用处就懂。** 函数名说清做什么、单位是什么；调用处没有看不出意思的 `true`、`0`。读代码的人比写代码的人多。
5. **代价看得见。** 复制、拿走、原地修改都写在调用处（`.copy()`、`take`、`&`）；不是 O(1) 的操作在注释里写明复杂度；函数不偷偷做 I/O。
6. **小而完整。** 每个模块有明确的边界（见“二、范围”），边界里的接口要完整、成对（有 encode 就有 decode），边界外的一个也不收。
7. **能自动验证。** 每个公开函数都有测试调用；有规范或系统工具的逐字对照；解析外部输入的经得起乱输入（见“七、测试”）。

## 二、范围：有边界的“电池齐全”

Lark 还没有包仓库，标准库缺什么，用户就得自己写一遍（lgit 自己写过 zlib，lgrep 自己写过正则）。
所以范围比 Rust 宽，向 Go 靠：有公开规范、只依赖 libc 的东西可以进来；框架、取舍很多的东西不进来（原则 6）。

**模块进标准库**，满足下面一条就够：

1. 编译器、构建工具、测试运行器自己要用（os、str、sort、fmt、time）。
2. 至少两个程序各自写过一遍，或者正在用（re、zlib、http、digest、log）。
3. 有公开的规范或者系统里的工具可以逐字对照（RFC 8259 的 json、RFC 4180 的 csv、RFC 4648 的 base64、gzip、diff -u）。
4. 基础容器和算法：几乎每种通用语言都带、自己写容易写错（map、set、deque、heap、treemap、sort、math、rand、iter）。范围以 Go 和 Rust 标准库里的同类模块为上限。

另外还要：只依赖 libc；能写出不碰网络、不要真终端的自动测试（原则 7）。

**函数进模块**，满足下面一条：

1. 有调用者：标准库自己、`tools/`、`apps/` 里除了测试以外的代码；
2. 是有调用者的那个函数的另一半（decode 对 encode、gunzip 对 gzip、pop_front 对 push_back、parse 对 format、leave 对 enter）；
3. 是规范要求的完整接口里的一部分（base64 的 URL 安全写法、csv 的别的分隔符）。

教学用的（判断质数、按字符倒过来）、给内置函数换个名字的（`float_pow`、`time.sleep`）、两个函数做同一件事的，都不收（原则 2）。
`make apicov U=1` 列出只有测试和示例在用的函数，新加函数以后对着这三条审一遍。

**不进标准库**（以后放到包里）：TLS / https；HTTP 的中间件和模板（入口 `http.serve` 和按“方法 + 路径”分发进标准库，2026-10 定）；数据库驱动、SQL；YAML、TOML 之类的配置格式；GUI；
加密算法（摘要除外：digest 只给校验和与 git 兼容用）；时区数据库（只支持系统时区和给定的时差）。

## 三、分层和依赖

模块按两个方向分：**依赖**决定谁能 import 谁，**稳定性**决定接口能不能改。

**依赖分三层**，只能往下 import，不能往上，也不能成环：

| 层 | 模块 | 特点 |
| --- | --- | --- |
| 计算 | str、utf8、math、fmt、sort、iter、map、set、deque、heap、treemap、rand、bytes、semver | 只做计算：不读写文件、不碰网络、不看环境变量和时钟。结果只取决于参数 |
| 系统 | os、io、time、net、proc、term、signal、timer、sync | 和操作系统打交道 |
| 格式和协议 | json、csv、base64、url、digest、zlib、re、diff、flag、log、http | 建在前两层上 |

同一层里可以互相 import，但不能成环；`make apicov` 会检查这两条（`tools/apicov.lark` 的 `layer_of` 和下表一致，新模块两处都要登记）。现在的依赖：set → map，fmt → utf8，os → sort、str、fmt，term → os，net → io，re → str，zlib → digest、bytes，digest → bytes，
log → json、time、str，http → str、time、os、net、sync，timer → time，semver → str。

- 计算层不碰系统，这样它们在任何地方都能用、测试结果可复现（原则 5、7）。`rand.from_time()` 是唯一的例外：它只读时钟当种子，`rand.new(seed)` 是确定的。
- 一个模块只 import 它真正用到的；为了省一行代码去 import 一个大模块不值得（log 用 json 是为了 JSON 格式的日志，这是功能本身）。

**稳定性分两档**：

| 档 | 模块 | 规则 |
| --- | --- | --- |
| 核心 | str、utf8、fmt、math、sort、map、set、deque、heap、iter、os、io、time、flag、json、rand | 尽量不改。要改时：在 README 的“接口改名”里写明，调用处一起改掉 |
| 协议和格式 | net、http、re、digest、base64、zlib、csv、diff、log、proc、term、bytes、signal、timer、sync | 还可以再调整几轮；新模块都先放在这一档 |

现在没有外部用户，改名时不留旧名字（原则 2）。有外部用户以后改成：旧名字保留一个版本，调用时给警告，下个版本删掉。

## 四、接口的形状

### 函数和方法

- **第一个参数是“主语”**：被操作的那个值放在第一个，这样可以写成方法调用：`m.insert(k, v)`、`s.trim()`、`r.range(0, 10)`。
- **重载只按第一个参数的类型区分**（编译器的规则）。同一个类型既要按键取、又要按下标取时，按下标的叫 `at`：`json.get(j, "k")`、`json.at(j, 0)`。
- **能写成泛型就不写重复的版本**：`sort.sort[T: Ord]` 而不是 `sort_ints`、`sort_strs`。
- **回调用 `fn(…)` 类型的参数**：调用处可以传闭包，也可以直接写函数名（`sort.sort_by(&xs, by_len)`）。
- **协议函数**（`show`、`eq`、`hash`、`cmp`、`iter_len`、`iter_at`、`next`、`index`、`set_index`、`drop`、`from`）会被语言隐式调用。名字和签名固定，不能挪作他用。

### 参数怎么传

- **默认只读借用**：大多数参数都是这种，不复制也不拿走。
- **`take`：函数要留着这个值**。比如存进容器（`m.insert(take k, take v)`），或者用掉它（`heap.into_sorted(take h)`）。调用处要么交出去，要么写 `.copy()`，代价在调用处看得见（原则 5）。
- **`inout`：函数要原地修改它**。比如容器的增删、`Rng` 的状态、`Reader` 的缓冲。不用 `inout` 当“输出参数”：要返回几个值就返回元组。
- **原地改和返回新值成对时，用动词和过去分词区分**（Python 的 `sort` / `sorted`）：`sort.sort(&xs)` 原地排序，`sort.sorted(xs)` 返回新的。

### 没有值、出错、panic

按下面的顺序判断该用哪种：

| 情况 | 写法 | 例子 |
| --- | --- | --- |
| 结果可能本来就没有，这不算错 | `T?` | `str.find`、`m.get`、`os.env`、`d.pop_front` |
| 会失败，要告诉用户为什么 | `T!`（错误是 str） | `os.read`、`json.parse`、`zlib.decompress`、`net.connect` |
| 调用者要按失败的种类走不同的路 | 返回值里带上种类 | `http.parse_request` 返回状态码；需要时用 `T!E` 的自定义错误类型 |
| 调用者写错了代码，违反了前提 | panic | `fmt.radix(n, 99)`、`rand.range(5, 5)`、`m[k]` 没有这个键 |

- **外部输入从不 panic**：文件内容、网络数据、命令行参数、环境变量都算外部输入。乱输入测试会检查这一条（原则 1）。
- **错误信息是一句给人看的完整中文**：
  - 系统操作写“动作 对象：原因”，比如 `无法打开 a.txt：No such file or directory`。
  - 解析写“格式 位置：原因”：文本按行列或行（`JSON 第 1 行第 4 列：意外的结尾，需要一个值`、`CSV 第 2 行：引号没有结束`），
    编码和二进制按第几个字符、第几个字节（`base64 第 3 个字符：不在字母表里（字节 32）`、`zlib 第 9 个字节：校验和不对，数据坏了`），都从 1 数。
    和整段有关、说不出位置的写“格式：原因”（`zlib：数据太短`）。
- **调用者不应该去解析错误信息的文字**：信息的措辞可以改。现在所有调用处都没有这样做；真需要区分时，按上表第三行，把种类放进返回值。
- **panic 的信息写“模块.函数：原因”**，比如 `rand.range：区间 [5, 5) 是空的`。
- **不另外提供会 panic 的版本**：比如不提供“出错就 panic 的 parse”。调用处要 panic 就写 `?? panic("…")`。内置函数的 `try_` 前缀是另一回事：不带前缀的内置函数出错时 panic。

### 类型

- **字段**：
  - 没有约束的数据，字段直接 `pub`：`proc.Output`、`time.Date`、`os.FileInfo`。
  - 字段之间有约束的（`Map` 的槽和键要对得上），只给 `pub` 读、不给改，修改只能经过模块的函数。
- **公开类型都写 `show`**：插值、调试、测试失败时的输出都要用到它，相当于 Rust 的 `Debug`。容器显示成 `{k: v, …}` 或 `[a, b]`，句柄类显示成 `Conn(fd 3)`。
  - 写法：容器 `{"a": 1}`、`{"a"}`、`[a, b]`（Heap 从小到大）；字段都是 pub 的数据写成构造它的样子，`FileInfo(is_file: true, …)`；句柄 `Conn(fd 3)`；有自己通用写法的用它（`Date` 是 `2026-10-26 07:52:00.123`，`Request` 是请求行）。
  - 泛型的容器写 `pub fn show[K, V](m: Map[K, V])`，插值时编译器按元素类型实例化；元素要能插值。
  - 不写 `show` 的：迭代器的状态（iter 的适配器、`utf8.Chars`）和只在模块里面用的类型（`flag.Spec`）。
- **容器写 `iter_len`**：`len(x)` 就能用。有顺序的容器再写 `iter_at`，就能 `for x in c` 借用遍历。顺序没有意义的不写 `iter_at`：`Heap` 不能 `for in`。
- **拿着系统资源的类型**（`io.Reader` / `Writer`、`net.Conn` / `Listener`）：
  - 写 `drop`，离开作用域时自动关闭；
  - 另外给 `close() -> ()!`，需要知道关闭是否成功时调用（写文件的 flush 可能在这时才失败）；
  - 不能复制。

### 数和单位

- **时长是 int 纳秒，时刻是 int 毫秒（从 1970-01-01 UTC 起）**。没有单独的 Duration 类型：用 int 加减比较最简单，单位写进函数名（`elapsed_ns`、`unix_ms`、`sleep_ms`、`set_timeout_ms`），见第五节第 6 条。
- **大小按字节**。str 的下标、长度都按字节，字符（码点）的操作在 utf8 模块里。
- **二进制数据用 `[u8]`**：digest、zlib、base64 的输入输出都是 `[u8]`。给 str 用的版本只在常用时加，名字加 `_str`：`base64.encode_str`。

### 性能

- 不是 O(1) 的操作，在注释里写复杂度：`m.remove(k)` 是 O(n)，因为要保持插入顺序；需要一次删很多的给 `retain`。
- 不在循环里每次复制大块数据：查找按下标比较，不切出子串（str 模块开头写了这一条）。
- 有更快的写法时，在注释里指过去：`find_in` / `is_match_in` 只看一段，不用把每一行切出来。

## 五、名字

先找 Rust、Go、Python、Zig、Elixir、Gleam 里同类的接口，有通用的名字就照抄；几家不一样时，选读起来最清楚、和本库其它名字最一致的那个（原则 3）。
名字都用小写加下划线。

**模块名**

- 用一个常用的单词，不和常用的变量名重名，因为 import 之后这个名字就不能当变量用：路径函数放在 `std/os` 而不是 `std/path`，摘要叫 `std/digest` 而不是 `std/hash`。
- 不同模块里可以有同名的函数（`json.format` 和 `csv.format`，`json.quote` 和 `proc.quote`），参数类型要一眼看得出区别。

**函数名**

1. **按 `x.f()` 读顺**，名字里不重复模块名：`http.format_date`，不是 `http.http_date`。
2. **容器用同一套词**（Rust 的 std::collections）：
   - 放进去：`push_*`（有顺序的）、`insert`（按键、按集合）；
   - 拿出来：`pop_*`、`remove`；
   - 查：`get`（`T?`，返回副本）、`contains` / `contains_key`；
   - 其他：`clear`、`is_empty`、`to_list`（所有元素的副本）；个数用内置的 `len(x)`。
   - `push`、`pop`、`len` 是内置函数，模块里不能再定义，所以堆是 `insert` / `pop_min`。
3. **写成文字叫 `format`，读回来叫 `parse`**，换一种写法时两边加同一个后缀（`format_iso` / `parse_iso`）。字节层面的变换用 `encode` / `decode`、`compress` / `decompress`；文字的转义用 `escape_*` / `unescape_*`（Go 的 `url.PathEscape` / `PathUnescape`）。
4. **构造**：`new`（空的）、`of(xs)`（从列表）、`from_*`（从别的值，比如 `io.from_fd(fd)`）；一个模块里有几种类型时写 `new_类型名`（`sync.new_cancel()`）。按用途起名、读起来更顺的也可以（`timer.deadline(ms)`、`timer.every(ms)`、`signal.notify(sigs)`）。
   **变体**：多一个参数时，用参数名做后缀（`parse_sep`）；传一组选项用 `_with`；传比较函数用 `_by`（`sort_by`）。
5. **判断**用 `is_`、`has_`、`contains`。
   **转换**（Rust 的 `as_` / `to_` / `into_`）：
   - `as_`：取出原来的值，类型不对时是 None（`json.as_int`）；
   - `to_`：新建一份（`to_list`、`to_unix_ms`）；
   - `into_`：拿走参数（`heap.into_sorted`）。
   - 取字段不加 `get_` 前缀。
6. **单位有歧义时写进名字**：`elapsed_ms`、`to_unix_ms`、`set_timeout_ms`。
7. **不缩写**，只保留大家都认识的：`dir`、`ext`、`cwd`、`env`、`hex`、`tty`、`len`。路径函数照 Go 的 `filepath`：`base`、`dir`、`rel`、`clean`。
8. **不用裸 bool 参数**：拆成两个函数（`enter_alt_screen` / `leave_alt_screen`），或者写进输入里（正则的 `(?i)`）。
9. **动词在前、修饰在后**，同一个库里不混用：`escape_html`、`decode_chunked`、`parse_request`，不写 `html_escape`。
10. **开头和结尾叫 start / end**，不叫 left / right：`trim_start`、`pad_start`。Rust 把 `trim_left` 改成了 `trim_start`，因为从右往左写的文字里，左边不是开头。只有讲屏幕上的位置时才说左右（`fmt.align_left`）。
11. **找东西**：`find*` 返回位置（`T?`）；`is_match`、`contains` 只回答有没有；`replace_all` 换掉全部。
12. **切开**：`split` 按字符串切，保留连续分隔符之间的空串；`words` 丢掉空的部分。Zig 的 `split` / `tokenize` 也这样分。
13. **个数**：O(1) 的叫 `len`，要数一遍的叫 `count`（`utf8.count`、`str.count`）。Elixir 也这样区分：O(1) 的叫 `size`，要数一遍的叫 `length`。
14. **和别的语言同名时语义也要一样**：`map.update(k, init, f)` 和 Elixir 的 `Map.update` 同名同参数，所以键不存在时也是直接放入 `init`，不经过 `f`。对不上又没有更好的名字时，宁可换个名字。

**例外**都要写明原因，现在有三个：
- `math.approx`：给测试里比较浮点数用，不然每个这样的测试都要自己写一遍。
- `sort.min_of` / `max_of`：不叫 `min` / `max`，因为方法调用时会和 `math.min` 混在一起。
- 模块名 `std/url`：和常用的变量名 `url` 重名（http 里的参数就叫 `url`），因为 Go、Python、Rust 都这样叫，换个名字反而找不到；import 它的文件里变量换个名字（`u`、`target`）。

## 六、文档

- **每个模块开头**有一段“用法”，列出最常用的几个调用，每行后面写返回什么；README 的“标准库”一节每个模块有一条总的说明。
- **每个公开函数上面**有一行注释，写它做什么、边界上怎么办（空输入、越界、找不到）、不是 O(1) 时的复杂度。
- **改名、改语义**写进 README 的“接口改名”清单：写旧名字、新名字，语义变了的写清楚怎么改调用处。

## 七、测试

`make check` 会跑下面这些，全部通过才算完：

1. **每个公开函数都要有测试调用过**：`make apicov`（`tools/apicov.lark`）检查 `std/*.lark` 里的每个 `pub fn` 至少在一个测试文件里被调用过（`tests/unit/*.lark`、`examples/*.lark`、`apps/*/tests.lark`）。
   实在没法自动测的写进 `tools/apicov.allow`，每行写明原因。现在只有 `term.enable_raw`、`term.read`、`term.enter_alt_screen`、`term.leave_alt_screen` 四个，都要真终端，在 ledit 里手动试。
   `make apicov A=1` 按模块列出覆盖的比例。
2. **每个模块有 `tests/unit/模块名.lark`**：除了正常的用法，还要测空输入、边界（0、1、刚好满、刚好超出）、出错的输入和出错信息的原文。
3. **能对照的就对照**：有系统工具的和系统工具逐字比较（zlib ↔ gzip、diff ↔ diff -u），有规范的用规范里的测试向量（SHA、CRC-32、base64、csv）。
4. **测试不依赖环境**：不连外网；临时文件放在 `os.temp_dir()` 下、名字带上时间，测完删掉；不假设时区、终端大小、当前目录，只检查范围或者性质。
5. **解析外部输入的函数要经得起乱输入**（`tests/unit/fuzz.lark`）：用固定的种子，在合法样本上随机改几处、截断，再加完全随机的短串。
   - 要求只返回错误、不 panic：数组越界、整数溢出、栈溢出都算 panic。
   - 能读进来的还要满足来回不变：`format(parse(s))` 再读一遍不变，`encode(decode(s)) == s`，等等。
   - 新加一个解析外部输入的函数时，在这里加一段；乱测找到的 panic 修好后，把那个输入写进“以前会 panic 的输入”。

`make apicov U=1` 不算在 `make check` 里，它只列出清单给人审（见“二、范围”的“函数进模块”）。

## 八、新加或修改一个函数的清单

1. 它属于哪个模块？符合“二、范围”的哪一条？它在哪一层，会不会让依赖往上走或者成环？
2. 别的语言里同类的函数叫什么、语义是什么（“五、名字”）？
3. 参数：主语放第一个；只读、`take`、`inout` 选对了吗？有没有裸 bool 参数？
4. 结果：没有值用 `T?`、出错用 `T!`、写错代码才 panic，选对了吗？外部输入会不会让它 panic？
5. 有没有和它成对的另一半要一起加？会不会和已有的函数做同一件事？
6. 注释、模块开头的“用法”、README 都写了吗？改名的话，“接口改名”清单也写了吗？
7. 测试：单元测试、边界、出错信息的原文；解析外部输入的，加进乱输入测试；`make check` 通过。

## 九、每个模块为什么在这里

“调用者”只算测试以外的代码；“依据”是“二、范围”里模块进标准库的第几条。

| 模块 | 层 | 依据 | 调用者 |
| --- | --- | --- | --- |
| str | 计算 | 1 | 构建工具、测试运行器、apicov、bench，7 个 app，std 里的 re、log、http、os |
| utf8 | 计算 | 3（UTF-8 编码规则）、4 | llua |
| math | 计算 | 4 | 暂时没有 |
| fmt | 计算 | 1 | bench，ledit |
| sort | 计算 | 1、4 | apicov，lgit、lhttp，std/os |
| iter | 计算 | 4 | 暂时没有 |
| map | 计算 | 4 | llua、lredis、lcache，std/set |
| set | 计算 | 4 | 暂时没有 |
| deque | 计算 | 4 | lredis |
| heap | 计算 | 4 | 暂时没有 |
| treemap | 计算 | 4 | 暂时没有 |
| semver | 计算 | 3 | 暂时没有 |
| rand | 计算 | 4 | 暂时没有（乱输入测试在用） |
| bytes | 计算 | 2 | std/zlib、std/digest，lgit（.git/index）；以前各自写了一遍大端、小端的读写 |
| os | 系统 | 1 | 构建工具、测试运行器、apicov、bench，lgrep、lgit、lhttp、llua、ledit、ltar（权限位、符号链接），std/http、std/term |
| io | 系统 | 1、2 | 7 个 app 都用，std/net |
| time | 系统 | 1、2 | bench，lgit、lhttp、llua、lredis、lcache，std/log、std/http |
| net | 系统 | 2 | lhttp、lredis、lcache、lproxy，std/http（UDP、Unix 套接字、lookup 暂时只有测试在用） |
| proc | 系统 | 1 | 只有测试用（拿系统的 diff、gzip 对照）；构建工具调 cc 时可以换成它 |
| term | 系统 | 2 | lgrep、ledit |
| signal | 系统 | 2 | lredis、lhttp、lcache（Ctrl-C、kill 时写日志退出）；以前只能靠 SHUTDOWN 或直接被杀 |
| timer | 系统 | 2 | lcache（按间隔清理过期的键）、lproxy（504 的截止时间）；`select` 的 `after` 只管一次等待，总的截止时间和对齐的间隔要自己算 |
| sync | 系统 | 2 | lcache（accept 结束时让清理的任务退出；以前靠“放掉通道副本”这个副作用）、lproxy 和 http.serve_until（收到信号以后优雅退出） |
| json | 格式 | 3 | std/log |
| csv | 格式 | 3 | 暂时没有 |
| base64 | 格式 | 3 | 暂时没有 |
| url | 格式 | 3 | lcache |
| digest | 格式 | 2、3 | lgit、std/zlib |
| zlib | 格式 | 2、3 | lgit、ltar（tar.gz） |
| re | 格式 | 2 | lgrep（来自 lgrep，和 grep -E 对照） |
| diff | 格式 | 1、3 | lgit（和 diff -u 对照） |
| flag | 格式 | 1、2 | lgrep、ledit、ltar，构建工具 lark（子命令） |
| log | 格式 | 2 | lhttp、lredis、lcache |
| http | 协议 | 2、3 | lhttp、lcache（serve），lproxy（serve_until、路由、Client） |

“暂时没有”的模块靠第 3、4 条留下：有规范可以对照，或者是基础容器。下一个用到它们的程序应该直接用，不要再自己写。

## 十、现在和规则对不上的地方

按要改的优先级排，改完一项删一项。

1. **运行时里只在 Linux 上编译的代码**（epoll、`/proc/self/exe`、proc 里挡 SIGPIPE 的写法）还没有跑过，需要 Linux 上的 CI。
