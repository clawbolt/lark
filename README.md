# Lark

Lark 是一门带所有权检查、编译成 C 的语言（按规则写的语言设计见 [DESIGN.md](DESIGN.md)）。这个仓库是它的自举过程：先用 OCaml 写引导编译器 lark0（stage0），再用 Lark 自己重写编译器（stage1，`compiler/*.lark`），由它编译自己。现在自举已经完成，新特性都加在 stage1 上；文中标“lark1 起”的是 stage0 没有的。

## 目录

- [目录结构](#目录结构)
- [构建与测试](#构建与测试)：[构建](#构建)、[测试](#测试)、[日常开发](#日常开发)（`make check`、`apps`、`bench-*`、`profile`）
- [自举路线](#自举路线)
- [语言](#语言)
  - [Lark0 子集](#lark0-子集)
  - [元组](#元组)、[模式](#模式)
  - [for 与迭代器](#for-与迭代器)
  - [泛型](#泛型)、[重载与接口](#重载与接口)（含 `dyn I`）、[闭包](#闭包)（含 `Fn`）
  - [运算符重载与下标](#运算符重载与下标)、[插值任意类型](#插值任意类型)
  - [数值与常量](#数值与常量)：整数溢出、位运算与十六进制、`float`、`const`
  - [调用 C 函数](#调用-c-函数)：`extern "c"`
  - [资源与错误](#资源与错误)：自定义错误类型、自定义析构、`defer` 和 `os.at_exit`、`shared T`
  - [模块与可见性](#模块与可见性)：`import`、`pub`、命名空间、字段的可见性
  - [并发](#并发)：`scope` / `spawn` / `Chan` / `select`
  - [尾调用](#尾调用)
- [工具与诊断](#工具与诊断)
  - [错误](#错误)、[警告](#警告)、[拼写提示](#拼写提示)、[panic 的调用栈](#panic-的调用栈)
  - [单元测试](#单元测试)（`test` 块）、[格式化](#格式化)（lark-fmt）
  - [项目与依赖](#项目与依赖)（`lark new / build / run / test / fetch`、`lark.pkg`）
- [标准库](#标准库)
- [所有权与内存](#所有权与内存)：[所有权规则](#所有权规则)、[生成代码的内存策略](#生成代码的内存策略)、[和设计文档不同的地方](#和设计文档不同的地方)

## 目录结构

```
lark/
├── stage0/            OCaml 写的引导编译器 lark0（Lark0 子集 → C）
│   └── src/           ast / lexer / parser / check（类型）/ own（所有权）/ cgtypes + codegen（C）/ main
├── compiler/          stage1：用 Lark 写的编译器 lark1（见“自举路线”）
├── seed/lark_seed.c   种子：lark1 编译自己得到的 C，没有 OCaml 也能构建 lark1
├── runtime/lark_rt.h  字符串、内存、I/O、任务和调度器、调用栈；生成的 C 只依赖它
├── std/               标准库（用 Lark 写）
├── docs/              std.md（标准库的规范）
├── tools/             test.lark（测试运行器）、fmt.lark（格式化工具）、bench.lark（基准测试）、apicov.lark（标准库的测试覆盖）；dev/ 是日常开发的脚本（见“日常开发”）
├── bench/             基准测试程序（make bench）
├── apps/              练手程序：lhttp、lcache、lgrep、ledit、lredis、llua、lgit、ltar、lproxy、ltls、llsp、lterm（每个是一个包，make apps 构建）
├── examples/          示例程序（另有 modules/、multi/ 两个多文件的例子）
├── tests/
│   ├── expected/      示例的预期输出
│   ├── err/           lark0 必须拒绝的程序；err1/ 是 lark1 的，multi/ 是多文件的
│   ├── warn/          必须编译成功、并给出预期警告的程序
│   ├── unit/          用 --test 运行的 test 块
│   ├── fmt/           格式化工具的输入和预期
│   └── mods/          错误用例 import 的模块
└── Makefile
```

## 构建与测试

### 构建

需要一个支持 GNU C 扩展的 C 编译器（clang 或 gcc）。只有构建 lark0 时才需要 OCaml ≥ 4.14、dune ≥ 3.0。

```sh
make stage1      # 种子 seed/lark_seed.c → build/lark1
make bootstrap   # lark1 → lark2 → lark3，比较生成的 C
make seed        # bootstrap 通过后，把 lark2.c 存为新的种子
```

stage0 的命令（用 lark0 编译 `examples/hello.lark`）：

```sh
make hello      # 构建 lark0，编译并运行示例
make test-err   # 确认 tests/err/ 的 5 个错误用例都被拒绝
make asan       # 用 AddressSanitizer 检查越界、重复释放和泄漏（macOS 上泄漏用 make leaks）
make tsan       # 用 ThreadSanitizer 检查数据竞争（任务、通道、Mutex 的示例）
```

### 测试

```sh
make test1                        # 跑全部示例、单元测试和错误用例，和记下的预期结果逐字比较
make expect                       # 用这次的实际结果重写预期结果，并列出改了哪些
make unit F=a.lark [T=名字]        # 编译并运行一个文件里的 test 块
make unit-compiler [T=名字]        # 运行编译器自己的 test 块
make bench                        # 基准测试：每个程序按几组 C 编译选项各跑几次，打印最短时间
```

- 示例 `examples/*.lark`（自动发现，另加 `examples/modules`、`examples/multi`）的预期输出在 `tests/expected/名字.out`：标准输出加标准错误，退出码不为 0 时最后一行是 `[退出码 N]`。
- 错误用例 `tests/err/`、`tests/err1/`、`tests/multi/` 必须编译失败，报错（文件、行列和信息）要和同目录的 `名字.expected` 一致。
- 警告用例 `tests/warn/` 必须编译成功，输出的警告要和同目录的 `名字.expected` 一致。
- 单元测试：用 `--test` 跑 `tests/unit/*.lark`，结果和同目录的 `名字.out` 比较；编译器自己的 test 块只要求全部通过（见“单元测试”）。
- 调用栈：加 `-DLK_NOTRACE` 再跑一次 `examples/trace.lark`，再用 `lark1 --release` 编译一次，两者的预期都是 `tests/expected/trace_notrace.out`。
- 格式化工具：`tests/fmt/名字.lark` 格式化后要和 `名字.expected` 一致，再格式化一次结果不变；编译器、标准库、工具和示例的源码也必须已经是格式化好的（见“格式化”）。
- 不一致时按行打印差异（像 `diff -u`：`-` 是预期，`+` 是实际），最后以失败退出。缺少预期结果也算失败。
- 新增示例或用例、或者确认某个输出的变化是对的，就运行 `make expect`，再看一遍它列出的文件。
- 测试运行器 `tools/test.lark` 是用 Lark 写的（用 `std/os` 运行编译器、C 编译器和程序，自己比较结果），`make test1` 会先用 lark1 把它编译成 `build/lark-test`。原来的 `tests/run.sh` 已经不用了，可以删掉。
- 基准测试 `make bench`：`bench/*.lark` 和“lark1 编译自己”，每个分别按默认、`-DLK_NOLINE`（只关行号）、`-DLK_NOTRACE`、`-DLK_UNCHECKED` 和后两项都关编译，各运行 5 次（`BENCH_RUNS` 可改）取最短时间，括号里是和默认相比的变化。改动生成代码或运行时的默认路径前后各跑一次。

### 日常开发

常用的命令都在 Makefile 里，背后的脚本在 `tools/dev/`（每个开头有说明），不用再复制粘贴长命令：

```sh
make check                        # 改完编译器或运行时：自举、重建 build/lark、跑全部测试、补执行权限
make strict                       # 同上，但全部重建、任何 C 警告都算错误：改了代码生成或运行时以后跑一次
make perms                        # 补上 build/ 和 apps/*/build/ 里程序的执行权限（复制或下载过文件以后会丢）
make formal                       # 所有权规则的 Lean 证明，加上和 lark1 的对拍（要装 Lean 4；改了 own.lark 以后跑，见 design/soundness.md）
make apps [A=lgrep]               # 构建全部练手程序，或者只构建 A 里列出的几个
make bench-grep                   # lgrep 对比系统 grep（1.2 亿字节的 build/bench/big.txt，每项取 3 次里最短的）
make bench-http A=lhttp [D=10]    # wrk -t4 -c50 压 lhttp 的首页；A=lcache 压一个键的 GET
make profile CMD="命令 参数" [S=3] # 用 macOS 的 sample 抓热点：自身时间最多的函数，加上锁 / kevent 的调用者
make profile-grep [P="-ci err"]    # lgrep 的热点（同一个大文件给 20 遍，跑得比采样久）
```

- 速度相关的改动：前后各跑一次对应的 `bench-*`，数字记进 `design/stage4-tasks.md` 的“结果和遗留”。
- `profile` 的命令要比采样时间跑得久（默认 3 秒），不然采样还没开始程序就结束了；lgrep 一遍只要零点几秒，用 `make profile-grep`。
- `make bench-grep` 在 macOS 上的结果（2026-10，1.16 亿字节；倍数 = lgrep 的时间 / grep 的时间，小于 1 是 lgrep 快）。左列是正则刚换成 Pike VM 时，右列是 lgrep 改用可复用的 `re.matcher` 以后。改正则、改 lgrep 以后拿来对比：

  | 模式 | Pike VM | 加 Matcher | 
  | --- | --- | --- |
  | `-c fn [a-z_]+\(` | 0.80x | 0.57x |
  | `-ci err` | 0.36x | 0.28x |
  | `-c zzzz_not_there` | 0.71x | 0.66x |
  | `-c [0-9]+\.[0-9]+` | 0.09x | 0.08x |
  | `-c ^pub fn` | 0.36x | 0.29x |
  | `-vc ^ *$` | 1.33x | 0.94x |
  | `-c TODO\|FIXME\|lk_[a-z]+_lock` | 0.37x | 0.21x |

  现在每一项都不比 grep 慢。原来最慢的 `-vc ^ *$` 是因为每行都新建一次线程表；`re.matcher` 让 lgrep 跨行复用同一张表，而且先用 `next_start` 筛掉不可能匹配的行，这些行不碰 VM。
- 压测里遗留的服务器：`pkill -x lhttp`、`pkill -x lcache`（脚本正常结束或按 Ctrl-C 时会自己关掉）。

## 自举路线

1. **stage0**：OCaml 实现，完整做类型检查和所有权检查，输出 C。
2. **stage1（`compiler/*.lark`，约 9000 行，含单元测试）**：用 Lark 重写的同一个编译器。`make stage1` 先把它拼成一个文件交给种子编译成 `lark1`；之后 `lark1 a.lark b.lark … -o out.c` 可以直接编译多个文件，命令行给出的文件共享一个顶层命名空间，报错形如 `compiler/lex.lark:12:5: 错误：…`。命令行选项：`-o 输出.c`、`-w`（不显示警告）、`--test`（见“单元测试”）、`--release`（不记调用栈，见“panic 的调用栈”）。

   **从泛型这一轮起，编译器源码自己也用 lark1 的新特性（如 `fill[T]`、`has[T: Eq]`、test 块），所以只能由种子 `seed/lark_seed.c` 编译，lark0 和旧种子都编译不了。** 更新编译器之前，先用当前源码 `make seed`；新源码通过 `make bootstrap` 后再 `make seed`。
   `make check` 里的 `seed-check` 检查种子是不是当前源码自举得到的 lark2.c：改了编译器以后先 `make seed` 再 `make check`。
   编译器有两个上限，超过时报错而不是栈溢出：括号、块最多套 256 层；一个函数体的语法树最多 1000 层（`a + b + …` 这样的长链每个运算符算一层，else if 最多连 500 个）。

   种子是旧版本的编译器，所以编译器源码要守它的规则：不遮蔽外层变量；`} else` 写在同一行；不用 `_` 反复声明，不用的值写成以 `_` 开头的名字。
3. **自举验证**：`make bootstrap` 用 `lark1` 编译自己得到 `lark2`，再用 `lark2` 编译自己；两次生成的 C 完全一致即为自举成功。

stage1 的结构：

| 文件 | 内容 |
|---|---|
| `ast.lark` | 语法树（解析后不再修改，分析结果按节点 id 存在旁表里） |
| `lex.lark` / `parse.lark` | 词法、递归下降解析 |
| `types.lark` / `check.lark` | 类型表、签名、作用域；类型检查、穷尽检查、警告 |
| `own.lark` | 所有权检查 |
| `cg_types.lark` / `cg_expr.lark` / `cg_stmt.lark` | C 代码生成 |
| `main.lark` | 命令行入口、模块载入、报错和警告的输出 |

## 语言

### Lark0 子集

Lark0 是 stage0 支持的子集，只保留写编译器必需的东西。右栏里的“命名空间”在 lark1 里已经有了（见“模块与可见性”），其余仍然没有：

| 有 | 暂时没有 |
|---|---|
| `type` 结构体、`enum`（可递归）、`match` / `match take` | 泛型类型上的约束、match 的守卫条件 |
| 参数 `x: T` / `inout x: T` / `take x: T`，调用处 `&x` | `?` 转换错误类型时，同一个源类型只能有一个目标 |
| `int` `bool` `str` `[T]`，`'a'` 字符字面量 | 监督树 |
| `for` 的三种形式、`break` / `continue` / `return` | 多子句函数、命名空间 |
| `"#{x}"` 插值、`x.f(y)` 即 `f(x, y)` | |

内置函数：`print eprint len byte_at slice from_byte int_str parse_int read_file write_file args exit panic push pop try_pop insert_at remove_at reserve copy join system replace`。`xs.pop()` 在空列表上 panic，`xs.try_pop()` 返回 `T?`；`xs.insert_at(i, x)` 把 x 放在第 i 个位置（i 可以等于长度），`xs.remove_at(i)` 拿走并返回第 i 个，后面的元素整段挪动，下标越界时 panic（见 `examples/listops.lark`）。字符串和字符的转义：`\n \t \r \0 \e`（ESC）`\xHH`（任意一个字节，正好两位十六进制）`\\ \" \' \#`。`xs.reserve(n)` 预先留出容量，之后再放 n 个元素都不用扩容（n <= 0 时什么都不做），事先知道大概要放多少个时用它，见 `examples/reserve.lark`。`replace(&x, v)` 把 `x` 换成 `v` 并返回旧值，用来从字段里取出拥有的值。大写开头、不带括号的名字（如 `EBreak`）是无字段的变体。

### 元组

```
fn divmod(a: int, b: int) -> (int, int) { (a / b, a % b) }
q, r = divmod(17, 5)          // 解构：声明新变量，_ 表示丢弃
t = min_max(xs)               // (int, int, (int, int))
print("#{t.0} #{t.2.1}")      // 按位置取元素
```

- 元组类型写作 `(A, B, …)`（至少两个元素），值写作 `(a, b)`。它就是一个匿名结构体（字段名 0、1…），所以按值存放，可以复制、`==` 比较、放进列表和 Map，也能参与泛型推断（`fn swap[A, B](take p: (A, B)) -> (B, A)`）。
- `a, b = t` 把元组拆开：左边只能是新变量名或 `_`，各自拿走对应的元素（`t` 被移走）。取单个元素用 `t.0`；和结构体字段一样，不能把非复制类型的元素单独移走，要拿走请解构。
- 暂不支持：给已有变量解构赋值（`a, b = b, a`）。`match` 里的元组模式见“模式”，`for` 里的见“for 与迭代器”。

### 模式

```
match t {
    None => "空"
    Some(Leaf(0)) => "值为 0 的叶子"          // 嵌套的变体模式、字面量
    Some(Leaf(v)) => "叶子 #{v}"
    Some(Node(Leaf(a), Leaf(b))) => "两片叶子"
    Some(Node(_, _)) => "更深的树"
}
match (n % 3, n % 5) { (0, 0) => "FizzBuzz", (0, _) => "Fizz", (_, 0) => "Buzz", _ => "#{n}" }
match cmd { "start" => 1, "stop" => 2, _ => 0 }
match n { 1 | 3 | 5 => "小奇数", _ => "别的" }     // “或”模式
```

- 模式可以任意嵌套：变体（包括 `Some` / `None` / `Ok` / `Err`）的字段可以是子模式，元组模式 `(p, q)`，整数、布尔、字符串字面量，名字和 `_`。分支从上到下尝试，第一个匹配的执行。`match` 能匹配字符串和元组。
- **穷尽检查**按模式矩阵逐列进行：`Some(Leaf(v))` 和 `Some(Node(_, _))` 合起来才算覆盖了 `Some`；整数、字符串需要一个 `_` 或名字的分支。
- **“或”模式** `p | q | …`：任一个选项匹配就走这个分支，也能嵌在字段里（`Some(1 | 2)`、`Circle(_) | Dot`）。“或”模式里不能绑定名字（要取值请分开写分支）；穷尽检查把每个选项当成一行。见 `examples/orpat.lark`。
- 借用的 `match` 里，模式中的名字都是指向被匹配值内部的只读引用，可以任意深。`match take` 只拆一层（字段写名字或 `_`），要嵌套请先拆一层再 match。
- 被匹配的是函数调用的结果这样的临时值、又要改或者交出拆出来的值时（比如 `l.accept()` 的连接要 `c.close()`），用 `match take`：拆出来的值归自己。对只读的名字写 `&x`、赋值时，报错会提示这一点。

### for 与迭代器

`for` 有三种形式：`for { … }`（无限循环）、`for 条件 { … }`、`for x in 来源 { … }`。来源可以是整数范围 `0..n`、列表、自定义迭代器或能借用遍历的类型。

```
type Countdown { n: int }      // 实际写法每个字段一行
fn next(inout cd: Countdown) -> int? {
    if cd.n == 0 { return None }
    cd.n -= 1
    Some(cd.n + 1)
}
for i in Countdown(n: 3) { print("#{i}") }     // 3 2 1
for w in words("一只 小 云雀") { kept.push(w) }  // w 归循环变量所有
for i, x in xs { … }                          // 带序号
for (name, score) in scores { … }             // 拆开元组
for (k, v) in m { … }                         // 借用遍历 Map
```

- **列表**：`for x in xs` 里 `x` 是只读借用，循环期间不能修改 `xs`。
- **自定义迭代器**：`it` 不是列表时，它的类型（结构体或枚举）要有 `fn next(inout it: T) -> E?`（也可以是泛型函数，如 std/iter 的适配器）。迭代器**归循环所有**：`it` 被移进循环（之后不能再用），循环结束、`break` 或 `return` 时释放。每轮调用一次 `next`，`Some(v)` 时 `v` 归循环变量 `x` 所有，可以直接移走；`None` 时结束。
- **借用遍历**：类型没有 `next`，但定义了 `fn iter_len(x: T) -> int` 和 `fn iter_at(x: T, i: int) -> E`（参数只读）时，`for x in v` 借用 `v`：先调用一次 `iter_len`，每轮 `x` 拥有 `iter_at(v, i)` 给的值。和遍历列表一样，循环期间 `v` 不能修改（报“正被 for 或 match 借用”），循环之后照常能用。
  - `std/map` 的 `Map` 给出 `(键, 值)`、`std/set` 的 `Set` 给出元素，都按插入顺序，不会先复制整张表。
  - 这样的类型也满足 `Iter[T]`（不满足 `Next[T]`）。见 `examples/borrowiter.lark`。
  - `len(v)` 也调用 `iter_len`：`len(m)`、`len(s)`、`len(d)` 是容器的元素个数。只定义 `iter_len`、不定义 `iter_at` 的类型（比如 `std/heap` 的 `Heap`）可以 `len`，不能 `for in`。
- **带序号**：`for i, x in xs` 同时给出从 0 开始的序号和元素，列表、自定义迭代器和 std/iter 的适配器都可以（列表里 `i` 就是下标）。
  - `i` 是 int，是循环里的一个新变量，改它不影响循环。只要序号时写 `for i, _ in xs`。
  - 整数范围不能带序号（`for i, x in 0..3` 报错）。见 `examples/forindex.lark`。
- **元组模式**：元素是元组时可以直接拆开：`for (name, score) in scores`、`for i, (a, _) in pairs`。
  - `_` 表示不要这一项，名字个数要和元组的元素个数一样。
  - 拆出来的名字和 `for x in xs` 的 `x` 一样是**只读借用**，指向元素内部，不复制（相当于 `for _e in xs { match _e { (name, score) => { … } } }`）：不能给它们赋值或移走，要修改请先 `.copy()`。见 `examples/fortuple.lark`。
- 迭代器的组合（`map`、`filter`、`zip`、链式写法）见“标准库”的 `std/iter`。
- **带标签的循环**：`名字: for …` 给循环起个名字，里面的 `break 名字`、`continue 名字` 跳出或继续那一层（只写 `break` / `continue` 照旧只管最里层）。三种 `for` 都能带标签。
  - 跳出去时沿途的值照常释放、`defer` 照常执行。标签不能和外层循环的重名，写错名字会报“外层没有叫 … 的循环”；`defer` 里的循环不能带标签，闭包里看不到外面的标签。
  - `for 条件 { … }` 的条件每轮都算，算在这个循环里：条件里只写 `break` 结束这个循环，`break 外层` 照常跳出外层。`for x in 列表`、`for i in a..b` 的列表和范围只在进循环前算一次，算在外面。
  - Lark 没有 `while` 和 `loop`：写了会提示改成 `for 条件 { … }`、`for { … }`。见 `examples/labels.lark`。

### 泛型

```
fn last[T](xs: [T]) -> T? {
    if len(xs) == 0 { return None }
    xs[len(xs) - 1].copy()
}
```

- 调用时不写类型实参，按实参类型推断：`last(nums)`、`words.last()`。参数类型里的 `T`、`[T]`、`T?`、`T!` 都能参与推断。只出现在返回类型里的类型参数（如 `map.new()`）用**期望的返回类型**补上（变量标注、函数返回类型、参数类型都算期望类型），还确定不了就报“无法推断”。
- **单态化**：每组类型实参生成一份 C 函数（如 `f_last__0`），没有装箱、没有运行时开销。实现上，实例化时从模板的 token 位置重新解析一遍函数，得到节点 id 全新的函数体，再按代换后的类型检查，所以各实例的检查结果互不干扰。
- **模板本身不检查**，像 C++ 模板一样在实例化时检查：`a + b` 对 `T = int` 成立，对 `T = [int]` 报错，报错位置指向模板里的那一行。用接口约束 `T`（`[T: Show]`）见“重载与接口”，约束在调用处就会检查。
- 实参先在没有期望类型的情况下检查，所以泛型参数的位置不会自动把 `x` 包成 `Some(x)`，也不能直接传 `[]` 或 `None`（先赋给带类型标注的变量）。

泛型类型：

```
type Pair[A, B] { a: A, b: B }
enum List[T] {
    Cons(head: T, tail: List[T])
    Nil
}
xs = Cons(1, Cons(2, Nil))      // 推断出 List[int]
empty: List[str] = Nil          // 无字段的变体靠期望类型确定
```

- 每组类型实参实例化成一个普通结构体或枚举（内部名字如 `List__0`，报错里显示成 `List[int]`），之后的布局、析构、复制都和手写的一样。模板先登记再解析字段，所以递归的 `List[T]` 不会无限展开。
- 构造时先看期望类型（变量标注、函数返回类型、参数类型）；没有的话按字段顺序推断：字段类型里的类型参数已经确定时，就带着期望类型检查这个实参，所以 `Cons(1, Nil)` 里的 `Nil` 能推断出来。单独写 `xs = Nil` 会报“无法推断”。
- 构造的实参和普通调用一样**按书写顺序求值**：`Pair(b: f(), a: g())` 先算 `f()` 再算 `g()`，然后放进各自的字段，跟字段的声明顺序无关（Rust、Swift 也这样）。
- `match` 按被匹配值的类型找变体，不同实例的同名变体互不干扰。
- 泛型函数可以接受泛型类型：`fn swap[A, B](p: Pair[A, B]) -> Pair[B, A]`，按 `Pair[...]` 的类型实参推断 `A`、`B`。

### 重载与接口

```
interface Show {
    fn show(x: Self) -> str
}
fn show(p: Point) -> str { "(#{p.x}, #{p.y})" }
fn show(n: int) -> str { "#{n}" }
fn show_all[T: Show](xs: [T]) -> str { … x.show() … }
fn index_of[T: Eq](xs: [T], x: T) -> int { … }
```

- **重载**：同名函数按第一个参数的类型区分（这正是 UFCS 下“方法”的含义），`x.show()` 和 `show(x)` 走同一套解析。第一个参数类型相同、或没有参数的同名函数会报重复定义。泛型函数也可以按第一个参数重载（如 `next[T](inout e: Each[T])` 和 `next[I: Iter[T], T](inout t: Taken[I])`）：先找类型完全相同的普通函数，再找第一个参数的模式能对上的泛型函数。
- **接口按结构匹配**：把 `Self` 换成具体类型后，存在参数模式、参数类型和返回类型都相同的函数，就算实现了接口，不需要写 `impl`。
- 约束写在类型参数上：`[T: Show]`、`[T: Show + Eq]`。内置约束：
  - `Eq`：除函数类型外都满足（结构体、枚举、列表、`T?`、`T!` 按值逐个比较）；自定义的 `fn eq` 会取代逐个比较，见“运算符重载与下标”。
  - `Ord`：int / str / float，以及定义了 `fn cmp` 的类型，可以 `<`。
  - `Iter[T]`、`Next[T]`：见“标准库”的 `std/iter`。
- 约束在**调用处**检查，报错形如 `Point 不满足接口 Show：缺少 fn show(Point) -> str`，指向调用那一行；模板本身仍然在实例化时检查。泛型类型的类型参数暂时不能带约束。

#### 接口对象 dyn I

```
shapes: [dyn Shape] = [Rect(w: 2, h: 3), Circle(r: 2), "lark"]
for s in shapes { print("#{s.name()}：#{s.area()}") }   // 运行时按具体类型分派
fn pick(big: bool) -> dyn Shape { if big { Rect(w: 10, h: 10) } else { Circle(r: 1) } }
```

- `dyn I` 是“实现了接口 I 的任意类型的值”：需要 `dyn I` 的地方（变量标注、参数、字段、列表元素、返回值）给了具体类型的值，就**自动装箱**；`x.m()` 经虚表调用对应的实现。泛型 `[T: I]` 在编译时按类型生成多份代码，`dyn` 在运行时分派，所以不同类型可以放进同一个列表。
- 值语义不变：装箱的值归 dyn 所有，复制 dyn 值会复制里面的值，离开作用域时释放。C 里是 `{ 堆上的值, 虚表 }`，虚表里是释放、复制和接口的每个方法。
- 能用作 dyn 的接口：每个方法的第一个参数是只读的 `Self`，其它参数和返回类型里不出现 `Self`（否则报“不能用作 dyn”）。
- 取回具体类型有两种写法：`match` 里的**类型模式** `名字: 类型`，名字只读地借用 dyn 里装的值（可以写 `_`，也能和 `|`、`Some(…)` 组合）；或者 `d.downcast()`，要转成的类型由标注给出，装的是这个类型时得到一份副本 `Some(…)`，否则 `None`。

```
d = match s {
    r: Rect => "矩形 #{r.w}x#{r.h}"
    _: Circle | _: Dot => "圆的"
    _ => "别的"                // dyn 可以装任何实现了接口的类型，所以一定要有 _
}
r: Rect? = s.downcast()
```

- dyn 值可以用 `==` 比较：装的类型不同就不相等，相同时比较里面的值（里面的类型不能比较时运行时 panic）。
- 暂不支持：`match take` 拆 dyn 值、把有自定义析构的值装进 dyn。

### 闭包

```
fn map[T, U](xs: [T], f: fn(T) -> U) -> [U] { … f(x) … }
k = 10
ys = nums.map(|x| x + k)        // 捕获 k
times(2, |i| { print("#{i}") })
```

- 函数类型写作 `fn(int, str) -> bool`，**只能用作函数参数**（只读）。传给这种参数的闭包是借用的：环境在栈上、存指向捕获变量的指针，没有堆分配。要存起来见下面的 `Fn`。
- 外层变量按**只读**捕获：闭包里不能移走、赋值或以 `&` 传出它们。闭包被当作“用到了它捕获的所有变量”，所以 `run(&xs, |x| len(xs))` 会报违反排他性。闭包里不能写 `return`、`break`、`continue`、`?`。
- 参数类型来自期望的函数类型，不用标注。泛型函数先用其它参数推断类型参数，再检查闭包；闭包的返回类型可以由闭包体推断（`nums.map(|x| "#{x}")` 得到 `[str]`）。
- 生成的 C：函数类型是 `{ 函数指针, 环境指针 }`；每个闭包是一个 C 函数加一个栈上的环境结构体，环境里是指向捕获变量的指针。没有堆分配、没有引用计数。

#### 存储的闭包 Fn(…) -> R

```
fn adder(n: int) -> Fn(int) -> int { |x| x + n }
fs: [Fn(int) -> int] = [adder(1), |x| x * x]
for f in fs { print("#{f(7)}") }
```

- `Fn(…) -> R` 是**拥有的**闭包：可以存进变量、字段、列表，可以返回，可以放进 Chan 交给别的任务。创建时捕获的变量被**复制**进堆上的环境（之后只读），所以闭包不依赖外面的变量，也就不会悬空。
- 复制 Fn 值只是环境的计数加一；最后一个持有者释放时释放捕获的副本。`==` 比较的是是不是同一个闭包。
- **函数名也能当值用**：在需要函数类型的地方直接写函数名，等于写闭包 `|a, b| f(a, b)`：`apply_all(xs, double)`、`fs: [Fn(int) -> int] = [double, square]`、`Rule(test: is_even)`。要求函数不是泛型、参数都是只读的，参数和返回类型与需要的一样；重载的函数按第一个参数的类型选。传给泛型函数也可以：`sort.sort_by(&xs, by_len)`、`iter.map(xs, double).collect()`，类型参数由别的参数确定以后再对函数名，返回类型可以从函数的签名推出来。其它情况（有 `take` / `inout` 参数、泛型）照常写闭包。
- Fn 值可以直接传给 `fn(…)` 参数（借用，不复制）。泛型参数是 `Fn(T) -> U` 时也可以直接传闭包。调用要通过变量：字段里的 Fn 先 `f = r.test.copy()` 再 `f(x)`。
- Fn 闭包不能捕获 `fn(…)` 类型的参数（那是借来的），也不能捕获有自定义析构的值（复制会绕过析构的唯一性）。

### 运算符重载与下标

```
// type Vec { x: int, y: int }；type Frac { n: int, d: int }（实际写法每个字段一行）
fn add(a: Vec, b: Vec) -> Vec { Vec(x: a.x + b.x, y: a.y + b.y) }
fn mul(a: Vec, k: int) -> Vec { Vec(x: a.x * k, y: a.y * k) }
fn neg(a: Vec) -> Vec { Vec(x: -a.x, y: -a.y) }

fn eq(a: Frac, b: Frac) -> bool { a.n * b.d == b.n * a.d }     // 取代逐字段比较
fn cmp(a: Frac, b: Frac) -> int { a.n * b.d - b.n * a.d }      // 负数 / 0 / 正数

c = a + b * 2          // add(a, mul(b, 2))
d = -c                 // neg(c)
s += v                 // s = add(s, v)
Frac(n: 1, d: 2) == Frac(n: 2, d: 4)   // true
```

- 左操作数是结构体或枚举时，`+ - * / %` 调用同名的 `add sub mul div rem`，一元 `-` 调用 `neg`；按第一个参数的类型重载，第二个参数可以是别的类型。int / bool / str 的运算不受影响。
- `< <= > >=` 调用 `cmp(a, b)` 再和 0 比。定义了 `cmp` 的类型满足 `Ord` 约束。
- `fn eq(a: T, b: T) -> bool` 取代编译器生成的逐字段比较：`==`、`!=`，以及列表、`T?`、`Map` 的键里的比较都用它。`eq` 和 `cmp` 的签名在定义处检查；和 `drop`、`from` 一样，它们在模块里也不加模块前缀。
- 运算符函数的参数都只能是只读的（不写 `take` / `inout`），所以 `a + b` 只是借用两侧，之后 `a`、`b` 仍然可用。
- 复合赋值 `+= -= *= /= %= &= |= ^= <<= >>= >>>=`：`x op= v` 就是 `x = x op v`，目标可以是变量、字段、列表元素（`xs[1] /= 4`）。目标是用户类型时照样按上面的规则调用 `add` / `div` 等；位运算的复合赋值只用于 int。见 `examples/compound.lark`。
- 字符串累积：`s += x` 和 `s = s + x + y …`（最左边是 s 本身）在 s 后面原地追加，摊下来每个字节只复制常数次；右边别的地方也提到 s 时（`s = s + "|" + s`）照常整段拼。`s = x + s` 往前面加，每次都整段复制，循环里这样写是平方的，要先收集到 `[str]` 再 `join`。
- `eq` 里别对同类型的值再用 `==`，那会调用它自己。

#### 下标

```
fn index(g: Grid, p: (int, int)) -> int { g.cells[p.0 * g.w + p.1] }
fn set_index(inout g: Grid, p: (int, int), take v: int) { g.cells[p.0 * g.w + p.1] = v }
g[(1, 2)] = 7
g[(1, 2)] += 1          // 先 index 再 set_index
ages["甲"] = 30          // std/map 定义了 index / set_index
```

- `x` 是结构体或枚举时，`x[i]` 调用 `fn index(x: T, i: K) -> V`，`x[i] = v` 调用 `fn set_index(inout x: T, i: K, take v: V)`，`x[i] op= v` 先读后写。下标的类型 K 随意（int、str、元组……）。泛型的 `index`（如 `map.index`）按 `x` 的类型实例化。
- `x[i]` 得到的是 `index` 返回的**新值**，不是 `x` 里面的位置：可以复制、借出、直接拿走，但不能给它的字段或元素赋值，也不能当 inout 参数（`m["a"].push(2)` 会报错）。要改就取出、修改后再 `x[i] = v` 放回。
- 只定义了 `index` 的类型是只读的。`Map` 的 `m[k]` 在键不存在时 panic，不确定时用 `m.get(k)`。

### 插值任意类型

```
fn show(p: Point) -> str { "(#{p.x}, #{p.y})" }
print("#{p}")                 // (1, 2)
print("#{[p.copy()]}")        // [(1, 2)]
print("#{[1, 2]} #{opt} #{(7, "七")}")   // [1, 2] Some(3) (7, "七")
```

- lark0 的插值只支持 int / bool / str。lark1 起其它类型调用 `fn show(x: T) -> str`（按类型重载，参数只读，类型在模块里时先找那个模块）。
- 没写 `show` 的列表、`T?`、元组按元素拼成 `[a, b]`、`Some(x)` / `None`、`(a, b)`，容器里的字符串加引号；元素又是什么类型都按同样的规则。自己写了 `show` 的类型（包括列表类型）总是用自己的。
- 结构体和枚举必须自己写 `show`，否则报“不能直接插值”。`[T: Show]` 的泛型函数里可以直接写 `"#{x}"`。
- 泛型类型可以写泛型的 `show`：`fn show[K, V](m: Map[K, V]) -> str`，插值 `Map[str, int]` 时编译器按类型实参实例化它（标准库的 Map、Set、Deque、Heap 就是这样）。

### 数值与常量

#### 整数溢出

- `int` 是 64 位有符号整数。生成的代码里 `+ - *` 和一元 `-` 都经过检查（`lk_add` 等，用的是 `__builtin_*_overflow`）：结果超出范围时 panic，退出码 101，而不是悄悄回绕。`MIN / -1` 同样 panic；`x % -1` 总是 0。
- 整数字面量超出范围、常量表达式溢出，在**编译时**报错。最小值写成 `-MAX - 1`。
- 编译生成的 C 时加 `-DLK_UNCHECKED` 可以关掉运行时检查（除以零照样检查）：这时 `+ - *` 溢出按 64 位补码回绕，和 `+% -% *%` 一样，不是 C 的未定义行为。它只是用来量检查本身的开销（`make bench` 里的一组），Makefile、`lark build` 和 `--release` 都不会加；发布时不要用，溢出会悄悄回绕成错的结果。
- 只带运行时的核心：程序没有 import 系统层的模块（os、io、time、net、proc、term、signal、timer、sync），也没有用到任务、通道、锁和系统的内置函数时，生成的 C 开头定义 `LK_CORE`，不带调度器、事件循环、栈溢出保护，也不用 pthread（栈溢出时直接段错误，不打印 Lark 的调用栈）。编译 C 时加 `-DLK_FULL` 强制带上全部。
- 换内存分配器：包含运行时之前定义 `LK_MALLOC(n)` / `LK_REALLOC(p, n)` / `LK_FREE(p)`（语义同 malloc / realloc / free），运行时和生成的代码的所有申请和释放都经过它们（`tests/alloc/tagged.h` 是检查用的例子）。
- 没有操作系统：只带核心的程序编译 C 时再定义 `LK_BARE`，运行时就只通过五个 C 函数和外界打交道，由你提供：`lark_plat_write(fd, p, n)`（print、eprint、panic 的输出）、`lark_plat_exit(code)`、`lark_plat_now_ns()`、`lark_plat_mono_ns()`、`lark_plat_random(p, n)`（哈希的密钥）。除此之外只用 C 库里不碰系统的部分（内存和字符串函数、`snprintf`、`strtod`、数学函数）；`read_file`、`write_file`、`system` 在运行时 panic，`--test` 不能用。完整的例子在 `examples/bare`：`plat.c` 模拟一块板子（写标准输出、固定大小的内存池），`run.sh` 编译、用 `nm` 检查程序的目标文件、再运行。
- panic 前会先把已经 `print` 的内容写出去，所以标准输出和标准错误合在一起看时顺序是对的。

#### 位运算、回绕运算和十六进制

- `& | ^`、一元 `!x`（对 int 是按位取反，对 bool 仍是取非）、`<<`、`>>`（左边补符号位）、`>>>`（左边补 0）。只用于 int；`<<` 移出的位丢掉，移位数不在 0..63 时 panic。
- `+% -% *%` 按 64 位补码回绕，不检查溢出，用来写哈希、随机数这类本来就要回绕的算法；`+ - *` 照旧检查。
- 优先级同 Rust：`* / % *%` 高于 `+ - +% -%`，高于移位，高于 `&`，高于 `^`，高于 `|`，高于比较。所以 `x & 1 == 0` 就是 `(x & 1) == 0`，`1 + 2 << 3` 是 24。
- 字面量 `0xFF`、`0o755`（八进制，写文件权限用）、`0b1010`，可以用 `_` 分隔（`0xcbf2_9ce4_8422_2325`），最多 64 位；第 64 位是 1 时按补码读成负数（`0xFFFF_FFFF_FFFF_FFFF` 是 -1），这样掩码和哈希常数可以照抄。
- 常量表达式里也能用（`const MASK = (1 << 20) - 1`），在编译时算好，结果和运行时一样。
- 没有 64 位的无符号整数类型：int 就是 64 个位，`>>>` 和回绕运算覆盖了无符号运算的需要（打印时仍按有符号显示）。窄一些的有定宽整数 u8、u16、u32、i32（见下面）。见 `examples/bits.lark`（FNV-1a 哈希、popcount）。
- 加 `-DLK_UNCHECKED` 时移位数不检查，只取低 6 位。

#### 字节 u8 和字节缓冲 [u8]

```
b: u8 = 'A'                    // 需要 u8 的地方，整数和字符字面量就是 u8（超出 0..255 编译报错）
mask = b & 0xDF                 // 比较、& | ^ ! 得到 u8；+ - * / % 要先 .to_int()
n = b.to_int() + 1
c = n.to_u8()                   // 超出 0..255 时 panic；n.wrap_u8() 取低 8 位；n.try_u8() 得到 u8?
bs = "云雀".to_bytes()          // [u8]，6 个字节
s = from_bytes(bs)              // 字节原样拼成 str（不检查 UTF-8）
```

- `u8` 可以隐式复制，C 里是 `uint8_t`；`[u8]` 就是字节缓冲，列表的 `push`、`reserve`、下标、`for`、`==` 都能用，元素紧挨着存放（每个 1 字节）。
- `u8` 和 `int` 不会互相隐式转换：`b == n` 两边类型不同时报错，`b == 65` 可以（字面量按 u8 读）。`match` 可以用整数模式匹配 u8。
- 完整示例见 `examples/bytes.lark`。

#### 定宽整数 u16、u32、i32

```
r: u32 = 0xFFFF_FFFF            // 字面量按期望的类型检查范围（u16 0..65535，u32 0..4294967295，i32 -2147483648..2147483647）
off: i32 = -16                  // i32 可以直接写负数字面量
hi = r & 0xFFFF_0000            // 比较、& | ^ ! 得到原来的类型；+ - * / % 要先 .to_int()
n = r.to_int() + 1
w = n.wrap_u32()                // to_u32 超出范围时 panic，wrap_u32 只取低 32 位，try_u32 得到 u32?；u16、i32 一样
```

- 规则和 `u8` 一样：只存不算，C 里是 `uint16_t`、`uint32_t`、`int32_t`，可以隐式复制、放进列表和结构体、打印、比较。它们之间、它们和 `int` 之间都不会隐式转换。
- `wrap_i32` 取低 32 位按补码解释：2147483648 换过去是 -2147483648，4294967295 是 -1。
- `extern "c"` 的参数和返回值也能写 `u16`、`u32`、`i32`。完整示例见 `examples/fixed.lark`。

#### 浮点数 float

- `float` 是 64 位浮点数（C 的 `double`）。字面量要有小数点或指数：`1.5`、`2.0`、`1e10`、`2.5e-3`、`1_000.25`；`t.0.1` 仍是元组下标，`1..5` 仍是区间。
- `+ - * /` 和 `< <= > >= == !=` 都能用，`%` 是 C 的 `fmod`（符号同被除数）。按 IEEE 754 计算：除以 0 得到 `inf` / `-inf` / `nan`，不会 panic，也没有溢出检查。
- int 和 float 不会自动转换：`to_float(n)`、`to_int(x)`（向零取整；`nan` 和超出 int 范围时 panic）。
- 插值和 `float_str(x)` 用能原样读回的最短写法：`0.1`、`2.0`（整数值也带 `.0`）、`1e+20`、`inf`、`nan`。`parse_float(s)` 失败时 panic，`try_parse_float(s) -> float!` 返回错误。
- 内置的数学函数（直接调用 C 的数学库，Linux 上编译 C 时要加 `-lm`）：`sqrt`、`floor`、`ceil`、`round`（0.5 远离 0）、`trunc`、`exp`、`ln`、`log10`、`sin`、`cos`、`tan`、`asin`、`acos`、`atan`、`atan2(y, x)`、`float_pow(x, y)`。
- `float` 满足 `Eq` 和 `Ord`（可以 `sort.sort`），可以放进结构体、列表、`T?`；不能 `match`（相等比较对浮点数不可靠，请用 `if`）。
- `const` 可以是 float，但只支持 `+ - * / %`：编译器自己没有浮点数，float 常量记成 C 的常量表达式，由 C 编译器算。
- 例子见 `examples/floats.lark`。

#### 顶层常量 const

```
const WIDTH = 8
const AREA = WIDTH * (WIDTH / 2)
const GREETING = "你好，" + name + "！"     // 可以先使用后声明
const name = "云雀"
pub const UNIT = 1                         // 模块外写 geo.UNIT
```

- 值在**编译时**算出，只能是 int / bool / str（以及上面说的 float）。值里可以写字面量、别的常量、算术（`+ - * / %`）、比较、`&& || !` 和字符串的 `+`；不能调用函数。循环引用、除以 0 在编译时报错。
- 用到常量的地方直接换成它的值（字符串是静态字面量）。名字可以大写也可以小写；局部变量优先于同名常量，但不能给常量赋值，也不能把它当 inout 参数。
- 常量和类型、函数、变体共用一个名字空间；模块里的常量和别的项一样要 `pub` 才能在外面用。

### 调用 C 函数

```
extern "c" {
    fn strlen(s: str) -> usize
    fn abs(n: c_int) -> c_int
    fn getenv(name: str) -> str              // C 返回 NULL 时得到空串
    fn strncpy(inout dst: [u8], src: str, n: usize) -> str
}

n = strlen("云雀")                         // 6
```

- 块里只写签名，调用的是 C 库里同名的函数。能写的类型：`int`、`float`、`bool`、`u8`、`u16`、`u32`、`i32`、`str`、`[u8]`（只作参数），以及 C 的整数类型 `c_int`、`c_uint`、`c_long`、`c_ulong`、`usize`、`isize`；返回类型还可以是 `()`。
- C 的整数类型在 Lark 这边都是 `int`：传过去时检查范围，超出就 panic，不会悄悄截断。
- `str` 传以 0 结尾的字节；C 返回的字符串复制一份。`[u8]` 传数据指针，写成 `inout` 时 C 可以往里写，长度要自己保证够用。其余参数都是只读的。
- 每个声明前可以单独写 `pub`：标准库可以用这种方式包装 C 函数，再对外提供安全的接口。
- 参数还可以是 `Fn() -> ()`：C 那边收到 `lk_hook`（函数指针和环境），用来把闭包交给运行时（`os.at_exit` 就是这样做的）。
- 暂不支持：可变参数函数（`printf` 这类）、别的回调、结构体和指针参数、头文件里的宏。默认只链接 C 标准库。完整示例见 `examples/ffi.lark`。

### 资源与错误

#### 默认值 `??`

```
n = m.get("a") ?? 0                  // 可复制的类型：左边可以是变量，取值时复制一份
xs = m.get("b") ?? []                // 别的类型：左边是临时的值，里面的值直接移出来
w = find(ps, 7) ?? find(ps, 1) ?? P(x: 0, y: 0)   // 右结合，从左往右找第一个有值的
```

- `a ?? b`：`a` 是 `T?` 或 `T!`，为 `None` / `Err` 时才求 `b`（`Err` 里的错误被丢掉）。
- `T` 不是 int / bool / str / float 时，`a` 是变量或字段会报错：不能复制的值不会被隐式复制。请写 `x.copy() ?? b`，或者用 `match take`。见 `examples/coalesce.lark`。
- `b` 可以是 `exit(1)`、`panic("…")` 这类不返回的调用：`port = parse_port(s) ?? exit(2)`。

#### 自定义错误类型

```
type ParseErr { pos: int, msg: str }
fn parse_num(s: str) -> int!ParseErr { … Err(ParseErr(pos: i, msg: "不是数字")) … }
```

- `T!E` 的错误可以是任意类型（不能是 `()` 或函数类型）；`T!` 是 `T!str` 的简写。`match` 里的 `Err(e)` 拿到的就是 `E`。
- 返回 `()!` 的函数走到结尾就是成功。末尾的 `if` 一边是 `()!` 的值（比如 `Err("…")`）、另一边只是语句时，只是语句的那边也算 `Ok()`，不用再补一行。`()!` 的结果匹配成功时写 `Ok` 或 `Ok(_)` 都行。
- **`T!` 的结果必须处理**：单独一行调用返回 `T!` 的函数（`os.write(p, s)`）、在 `()` 函数的末尾或循环体里调用它，结果都会被丢掉，编译器报错。处理的办法：加 `?` 交给调用者，用 `match` 处理，或者写 `_ = os.remove(p)` 表示确实不在乎。
- 没有 `else` 的 `if` 没有值，所以 `if bad { Err("…") }` 不会返回错误，编译器会报错：要提前返回请写 `if bad { return Err("…") }`。分支末尾是别的 `T!` 调用时也一样，加 `?` 交给调用者，或者写 `_ = f()` 表示确实不要。
- `?` 两边的错误类型相同时直接把错误交给调用者；不同时（比如这里是 `ParseErr`，当前函数返回 `int!CalcErr`），`?` 会调用你写的 `fn from(take e: ParseErr) -> CalcErr` 来转换，没有就报错并提示该写什么。`from` 按第一个参数重载，所以每种错误类型只能有一个转换目标；`str` 错误（`try_parse_int` 等）也一样，写 `fn from(take e: str) -> CalcErr` 即可。
- C 里错误放在 `{ ok, val, err }` 的 `err` 字段，析构、复制、`==` 都按 `E` 处理。

#### 自定义析构

```
type File { name: str, fd: int }
fn drop(inout f: File) { print("关闭 #{f.name}") }
```

- 值被销毁时自动调用：离开作用域、被新值覆盖、所在的列表 / 结构体 / 枚举被释放、`take` 参数在函数结束时。先调用 `drop`，再释放各个字段。
- 每个值只调用一次：被移走的值不会再调用。结构体被移走时按位清零，所以有析构的结构体多一个隐藏字段 `lk_live`（构造时为 1，清零后为 0）；枚举的 tag 从 1 开始，清零后是 0（在堆上的枚举是指针，清零后是 NULL），同样能判断。
- 有析构的类型，以及包含这类值的类型，都**不能复制**（否则同一个资源会被释放两次）；`drop` 不能直接调用；有析构的枚举不能 `match take` 拆开。
- 写法固定为 `fn drop(inout x: T)`，T 是结构体或枚举、没有返回值；靠按第一个参数重载，每个类型最多一个。`drop` 里不要给 `x` 整体赋值（那会再次触发析构）。

#### defer 和退出钩子

```
f = open("a.txt")
defer { close(&f) }               // 离开这个块时执行
…
os.at_exit(|| term.restore())     // 进程退出时执行
```

- `defer { … }` 在离开**所在的块**时执行：走到块尾、`return`、`?`、`break`、`continue` 都算（循环体里的 defer 每轮执行一次）。几个 defer 按逆序执行，和析构交错：defer 之后声明的值先释放，再执行 defer，然后才释放 defer 之前声明的值，所以 defer 里还能用它们。`return x` 的值在 defer 之前就算好了。
- defer 里用到的外面的变量，到块结束前**不能移走**（defer 执行时还要用它），可以重新赋值、以 `&` 传递，defer 看到的是离开时的值。defer 里不能 `return`、不能用 `?`，`break` / `continue` 只能对 defer 里面的循环；闭包里不能写 defer。`defer` 不是关键字，只有后面跟着 `{` 时才算。
- 有 defer 生效时，调用自己的 `return f(…)` 不变成跳转（不然 defer 会在递归调用之前执行）。
- **`exit` 和 `panic` 不执行 defer，也不执行析构**：它们直接结束进程。“怎么退出都要做”的清理用 `os.at_exit(f)`（`f` 是 `Fn() -> ()`）：main 正常结束、`exit`、`panic` 时按登记的逆序各执行一次；`f` 里再 `exit` 或 `panic` 时剩下的不再执行。`std/term` 进入原始模式时也登记了退出时恢复终端（panic 以后终端不会乱）。见 `examples/defer.lark`。

#### shared T

```
cfg = share(Config(name: "默认", level: 3))
a = User(name: "甲", cfg: cfg.copy())     // 计数加一，两处共用同一份
print(a.cfg.name)
```

- 引用计数的共享所有权，所有权模型的“逃生口”：一个值要被多处同时持有（共享配置、共享子树）时用。`share(x)` 拿走 x 放到堆上；`.copy()` 只是计数加一；最后一个持有者释放时才释放内容，自定义析构也只调用一次。
- 内容只读：可以读字段（`s.f` 自动解一层）、取下标、`match`；不能赋值、不能以 `&` 传出、不能 `match take`。这样不需要运行时借用检查，排他性规则也不会被绕过。
- `shared` 只作用在紧跟着的基础类型上：`shared Node?` 是“可能没有的共享节点”。
- 不会成环：shared 的内容只读，`share(x)` 时 x 已经构造好，不可能指向它自己，所以引用计数不会泄漏，也就不需要 `weak`。shared 值可以交给多个任务一起读。
- 内容里不能有 `Mutex` 和 `Chan`（直接的字段，或者列表、可选值、结构体里面的）：`lock`、`send` 会经由 shared 改掉内容，还能把 shared 自己的副本存进去成环。要在任务间共用 Mutex 或 Chan，直接传它的 `.copy()`。

### 模块与可见性

```
import "geo"                  // 载入同目录下的 geo.lark，模块名 geo
import "std/map"

a = geo.Vec2(x: 1, y: 2)      // 模块外写 geo.x
b = a.add(a)                  // 方法按 a 的类型找到 geo.add
m: map.Map[str, int] = map.new()
match geo.classify(b) { Origin => …  geo.OnAxis(n) => … }   // 模式里的模块限定可写可不写
```

- `import "路径"` 写在行首，路径不带 `.lark`：先相对于写 import 的文件所在目录找，找不到再相对于当前目录找（所以在仓库根目录下 `import "std/map"` 总能找到）。import 是递归的，同一个文件只载入一次。
- **一个文件就是一个模块**，模块名是文件名（不带 `.lark`，两个模块不能同名）。import 载入的文件里，只有标了 `pub` 的 `fn` / `type` / `enum` / `interface` / `const` 能被别的文件使用：调用函数、构造结构体或变体、在类型标注里写类型名都会检查。命令行上直接给出的文件属于根模块，仍然互相可见（编译器自己就是这样构建的）。
- **命名空间**：模块里的类型、枚举、函数在模块外写成 `geo.Vec2`、`geo.add(…)`、`map.Map[K, V]`，模块内直接写名字；名字先在本模块里找，再到根模块里找。各模块的名字互不冲突，私有名字（如 `std/map` 的 `map_slot`、`map_grow`）也不占用全局名字，`insert`、`get`、`count` 这些名字只属于 `map` 模块。
- **方法调用**按接收者的类型找：`a.add(b)` 里 a 是 `geo.Vec2`，就先找 `geo.add`。所以 `m.insert(k, v)`、`m.get(k)` 不用写模块名。在 import 的模块里找“扩展方法”的规则见“标准库”的 `std/iter`。
- 变体按所属枚举的模块找：构造时写 `geo.OnAxis(1)`，模式里写 `OnAxis(n)` 或 `geo.OnAxis(n)` 都行（总是按被匹配值的类型找）。
- **协议名字是全局的**：接口和接口方法的实现（如 `hash`）、`eq`、`cmp`、`drop`、`from`、`next`、`main` 不加模块前缀，这样模块里的泛型代码（比如 `map.put` 里调用 `hash(k)`）能找到你在根模块里为自己的类型写的实现。
- **用哪个模块就在哪个文件里 import 它**：只有写了 `import "std/os"` 的文件里，`os.x` 才是模块里的名字，`os` 也不能再用作变量名；别的文件里 `os` 是普通的名字（比如可以有叫 `index` 的变量，哪怕项目里有个 `index` 模块）。没导入就用会报“未定义的变量 os；要用模块 os，请在这个文件开头 import 它”。还没有 `import … as` 重命名，也没有只导入部分名字。

字段的可见性：

- 模块里定义的结构体，字段默认只在这个模块里可见；在字段前写 `pub` 才能在别的模块里读（`pub type Vec2 { pub x: int … }`）。和函数、类型一样是显式 `pub`。
- 没写 `pub` 的字段在模块外读也不行（“map.Map[str, int] 的字段 slots 没有 pub，只能在模块 map 里使用”）。
- 有这样的字段时，模块外也不能直接构造这个结构体，要用模块提供的函数（`map.new()`、`iter.range(0, 3)`），这样外面没法造出内部状态不对的值。所有字段都是 `pub` 的结构体照常可以在外面构造。
- 有私有字段的结构体，`pub` 字段在模块外**只读**：给字段（或字段里的元素）赋值、`+=`、以 inout 传递（包括 `m.keys.push(…)`）只能在本模块里做，要改就用模块的函数，这样外面破坏不了它的内部状态。整个值的赋值和传递照常（`m = map.new()`、`f(&m)`）。
- **字段全是 `pub` 的结构体**只是一组数据（比如 `geo.Vec2`、`time.Date`），在模块外和构造一样可以直接修改：`v.x += 1`、`flat.paths.push(p)`。
- `std/map` 的 `Map` 公开了 `keys`、`vals`（`for k in m.keys` 借用遍历键，不复制），`slots` 是私有的。枚举变体的字段不受影响，模式匹配照常能拆。根模块里的结构体不受这些限制。

### 并发

```
fn worker(take job: Job) { job.out.send(fib(job.n)) }

results: Chan[int] = chan()
scope {
    for i in 0..4 { spawn(worker, Job(n: 20 + i, out: results.copy())) }
}                                  // 块尾等所有任务结束
for {
    r = results.recv()             // int?：别人都放手、队列也空了就是 None
    match r {
        Some(v) => print("#{v}")
        None => break
    }
}
```

- **结构化并发**：`spawn(f, x)` 只能直接写在 `scope { … }` 里，创建一个**任务**运行 `f(x)`；块结束前等其中所有任务跑完，所以任务不会比创建它的代码活得更久。块里可以 `return`、`?`，也可以 `break` / `continue` 到块外：跳出去之前，先释放经过的各层局部变量（比如手里的通道副本），再等块里的任务都结束，所以等着 None 的任务不会因为你还拿着副本而一直等。见 `examples/scopejump.lark`。
- `f` 是普通函数，恰好一个 `take` 参数、没有返回值；`x` 被**移进**新任务，之后不能再用。任务之间的值要么移过去，要么用只读的 `shared`，要么放进 `Mutex[T]`（见下）。字符串、`Fn`、`shared` 的引用计数**只在有别的任务活着时**用原子操作：运行时记着 spawn 了、还没结束的任务数，为 0 时用普通加减，所以单线程的程序和 scope 之外的代码不付原子操作的代价（结构化并发保证了这样做是安全的，见 `runtime/lark_rt.h` 的 `lk_rc_inc`）。例子见 `examples/strthreads.lark`。
- **任务和调度器**：任务是有自己的栈的协程（1MB，用到的页才占内存），不是系统线程。运行时把它们放到 `LARK_PROCS` 个系统线程上运行（环境变量，默认是 CPU 核数）：
  - 第一次 spawn 时才启动调度器，不用并发的程序（比如编译器自己）什么都不创建。
  - 任务只在等待的地方让出：`recv`、`select`、scope 块尾、`sleep_ms`、等着 `lock`，`std/net` 的读、写、accept（socket 没有数据时任务挂起，由 kqueue / epoll 叫醒），以及管道和终端的读（`io.stdin()` 等：先用 poll 看有没有数据，没有就同样挂起；不改 O_NONBLOCK，因为标准输入和 shell 共用同一个打开的文件）。不抢占，一直在算的任务占着它的系统线程。
  - 写文件、管道、终端，`os.shell`，`net.connect`，`extern "c"` 函数在等待时占着一个系统线程。普通文件的读不会等（磁盘再慢也算“就绪”）；事件循环登记不了的设备退回到阻塞着等。
  - 一个任务叫醒另一个（比如往它等着的 Chan 里 send）时，被叫醒的接着在同一个系统线程上运行，交接只是一次栈切换。每个系统线程有自己的运行队列，空闲的去偷别的线程的。
  - 实测（`bench/conc/chan.lark`，作者的 Mac）：通道来回一次 189 ns（以前每个 spawn 一个线程时是 3530 ns），spawn 一个任务约 2.8 微秒（以前约 20 微秒）。lredis 16 条流水线 34 万–51 万 req/s（以前 21 万），不用流水线和真 Redis 差不多。设计和测量过程见 `design/stage4-tasks.md`。
- `Chan[T]`：无界队列。`ch: Chan[T] = chan()`，`ch.send(v)` 把 v 移进去，`ch.recv()` 返回 `T?`：队列空时等待，直到有新值，或者**除自己以外的持有者都放手**，或者通道被 **`ch.close()`** 了（这两种情况都返回 None）。`ch.copy()` 只是计数加一。
  - 发送方都是 spawn 出来的任务、接收方之外没有人留着副本时，不用 close：发送方结束、副本被释放，接收方自然收到 None。
  - **自己还留着一份副本时**（最常见的是 main 建了通道、分给生产者和消费者），只有放手是等不到的：recv 会一直等，程序不报错也不退出。这时在生产者都结束以后（比如它们所在的 scope 块之后）调用 `ch.close()`。
  - close 以后队列里剩下的值照样能取出来，取完才得到 None；可以重复 close；close 以后再 send 会 panic。例子见 `examples/chanclose.lark`。
- `Mutex[T]`：几个任务一起改的值。`m = mutex(v)` 创建，`m.copy()` 只是计数加一（同一个互斥量），可以交给多个任务。里面的值只能在 lock 块里碰：

  ```
  cache = mutex(files.new_cache())             // Mutex[Cache]
  hit = lock cache as c { files.find(&c, path) } // c 相当于 inout 参数；块尾解锁，块的值带出来
  ```

  块里 `c` 能改、能 `&c` 传下去，不能移走（带出来的只能是副本），`cache` 本身也不能被移走或重新赋值。块里 `return`、`?`、`break` / `continue` 到块外时，跳出去之前先解锁。锁着的时候可以等待（`recv`、读网络），抢不到的任务先空转一会儿再排队挂起，解锁时叫醒最早来的那个去重新抢（不保证先来先得）；同一个任务再锁同一个互斥量会报错退出。`lock` 不是关键字，只有后面紧跟一个名字时才是 lock 块。例子见 `examples/mutex.lark`。
- `select` 同时等几个 Chan（可以是不同的元素类型）：

  ```
  for {
      select {
          w <- words => print(w)       // 先有值的分支执行，w 拿到收到的值
          n <- nums => { sum += n }
          after 100 => print("100 毫秒内没有消息")
          done => break                // 所有通道都结束了
      }
  }
  ```

  `after ms` 和 `done` 都可选、各最多一个。有 `done` 分支时 select 可以有值（`x = select { v <- ch => v * 10, done => -1 }`）；没有时，所有通道结束后 select 什么也不做，所以各分支不能有值。`break` / `continue` 作用于外面的循环。另有 `sleep_ms(n)`。
- 还没有：`link` / 监督树；任务的栈用完时只是段错误退出，没有专门的报错；两个任务互相等待会死锁（运行时不检测）。

### 尾调用

```
fn sum_to(n: int, acc: int) -> int {
    if n == 0 { acc } else { sum_to(n - 1, acc + n) }   // 编译成跳回开头
}
```

- 函数在**尾部调用自己**时不再压栈：先算出新的实参，像 `return` 一样释放这一轮的局部变量，再给参数重新赋值、跳回函数开头。尾部指函数体的值、`if` / `match` 各分支的值、块的值，以及任何位置的 `return f(…)`。
- 条件：每个参数都是 `take`，或者是 `int` / `bool`。只读的 `str`、列表等参数是借来的，可能指向这一轮要释放的局部变量，所以不做（仍是普通调用）。
- 这让 Erlang 式的进程循环可以一直跑下去：状态就是参数，`counter(st)` 处理完一条消息再接着收（见 `examples/tail.lark`，一百万条消息不占栈）。
- 还不支持：互相递归的尾调用、scope 和闭包里的尾调用；有 defer 生效时也不做。

## 工具与诊断

### 错误

- 格式是 `文件:行:列: 错误：信息`，下面是那一行源码和指向出错位置的 `^`。
- 函数体里的错误报完后，lark1 跳过出错的那条语句再检查一遍，接着报下一处，所以一个函数里的几处错误能一起报出来，一次最多 10 处。每一遍都从头检查，前一处错误不会引出连带的错误：出错的语句声明了新变量（`x = …`）时，块里后面的语句不再检查（带类型标注的 `x: T = …` 照标注声明，照常往下查）；错误在跨行表达式中间的一行时，跳过整个函数体。见 `tests/err1/multi_in_fn.lark`。
- 语法错误、类型声明和函数签名里的错误只报第一处：后面的检查都依赖它们。

### 警告

编译成功后，lark1 按位置输出警告（标准错误），不影响生成的代码；加 `-w` 不显示。目前有四种：

- **变量没有用到**：声明之后从没读过、调用过或赋过值的局部变量、`for` 的循环变量、模式里绑定的名字。函数和闭包的参数属于签名，不警告。不需要的值写成 `_`（`_ = xs.pop()`、`for _ in 0..n`、`Err(_) =>`），或者用以 `_` 开头的名字（`_old = …`）。`_` 可以在同一个作用域里反复声明，但不能读取。
- **永远不会执行的代码**：块里跟在 `return`、`break`、`continue`、`panic`、`exit`（或者各分支都是这些的 `if` / `match`）后面的语句。
- **import 没有用到**：这个文件里既没写过 `m.x`，方法调用、运算符、下标也没有解析到 `m` 里的函数。
- **函数、类型没有用到**：不带 `pub` 的函数、结构体、枚举，名字在能看到它的地方（根模块是命令行给出的所有文件，import 的模块是它自己的文件）除了声明以外一次都没出现过。
  - 按名字算，所以重载里只要有一个用到了就都不警告，用到枚举的任何一个变体也算用到枚举。
  - 会被隐式调用的名字（运算符 `add` / `cmp` 等、`show`、`eq`、`next`、`iter_len` / `iter_at`、`drop`、`from`、`index`、接口方法）、test 块和以 `_` 开头的名字不警告；只在 test 块里用到也算用到。见 `tests/warn/items.lark`。

标准库（`std/` 下的文件）里的警告不输出。

### 拼写提示

```
tests/err1/typo_fn.lark:3:5: 错误：未定义的函数 pirnt；是不是想写 print？
```

- 未定义的变量、函数（含结构体和变体的构造）、未知类型、没有的字段、不存在的变体，报错时会在当前能用的名字里找最像的一个提示出来。
- “像”按编辑距离算：插入、删除、替换、交换相邻两个字母各算一次，最多允许名字长度的三分之一（至少一次）。没写模块前缀时，`dist2` 也会提示 `geo.dist2`。

### panic 的调用栈

```
panic: 年龄不能是负数：-20
  在 check_age（examples/trace.lark:5）
  在 闭包（examples/trace.lark:17）
  在 apply_all（examples/trace.lark:11）
  在 main（examples/trace.lark:17）
```

- panic 时（`panic(…)`、下标越界、整数溢出、除以零、`assert` 失败等），在 panic 信息下面从里到外打印每一层函数正在执行的 `.lark` 文件和行，最多 20 层。test 块显示成 `测试“名字”`，闭包显示成 `闭包`。
- 做法：生成的每个 C 函数开头有一个 `LK_FRAME`，记下函数名、文件和当前行，挂在本任务的链表上，函数返回时由 `__attribute__((cleanup))` 自动摘下，所以任何一个 `return` 都不会漏；语句之前更新一次行号（`LK_LINE(N);`）。行号只在这条语句 panic 或它调用的函数 panic 时才被读到，所以既不调用函数、也不会 panic 的语句（字面量和变量的赋值、基本类型的比较、`&& || !`、位运算、除以非零常数、构造结构体、`push`、只看条件的 `if` / `match` 等）不更新。每个任务有自己的调用栈。
- 行号精确到语句：一条语句里有好几处可能 panic 时，指的是这条语句开头的那一行。`exit(n)` 不是 panic，不打印调用栈。
- 栈溢出（递归太深）也按 panic 报告：`panic: 栈溢出（…）`，下面是调用栈，连着的同一处调用合成一行“…（同一处又重复了 N 层）”，退出码 101。运行时在每个线程上准备了一块处理信号用的栈，碰到栈底的保护页时在那里打印。加了 AddressSanitizer 时不装，由它自己报。
- 发布时用 `lark1 --release`（等于在生成的 C 开头写上 `#define LK_NOTRACE`），或者编译生成的 C 时加 `-DLK_NOTRACE`，都可以关掉：`LK_FRAME` 和 `LK_LINE` 什么都不做，panic 时只打印信息，省掉每次调用两次、每条语句一次的写入（比如 `make bootstrap CFLAGS="-std=gnu11 -O2 -pthread -DLK_NOTRACE"`）。和 `-DLK_UNCHECKED` 互不影响。`-DLK_NOLINE` 只关掉行号（仍然记每一层的函数，打印的是函数开头那一行），用来分开量两部分的开销。
- 开销（`make bench`）：调用很多的小函数约 22%（`calls`），哈希表约 20%（`maps`），循环里语句多、函数调用少的代码约 25%（`tokens`，几乎都是更新行号），编译器自己约 5%–13%。没有别的任务时调用栈挂在普通全局变量上，不经过线程局部变量（macOS 上访问线程局部变量要多一次函数调用）。整数溢出检查在只有加减乘的内层循环里约 10%–15%（比如 `fib`），一般的代码测不出来；`--release` 里照样保留。

### 单元测试

```
fn add(a: int, b: int) -> int { a + b }

test "加法" {
    assert(add(1, 2) == 3)
    assert_eq(add(-1, 1), 0)
}
```

- 顶层的 `test "名字" { … }` 是一个没有参数、没有返回值的测试。平常编译时会照常检查，但不会运行。用 `lark1 --test a.lark -o a.c` 编译时，生成的 `main` 会依次运行文件里的每个测试，程序自己的 `main` 不运行，也可以不写。
- `assert(条件)`：条件不成立时 panic，信息是“断言失败：文件:行:列”。`assert_eq(a, b)`：两边不相等时 panic，信息里还带上两边的值（字符串加引号）。两边要是同一类型，能用 `==` 比较、能插值（结构体和枚举要自己写 `show`）。
- 每个测试在单独的子进程里运行，panic、`exit` 和崩溃都只算这个测试失败，不影响别的测试。测试的输出先收起来，失败时才缩进 4 格打印在结果下面。最后一行是“N 项测试：…项通过，…项失败”，有失败时退出码为 1。
- 运行时的第一个参数是名字过滤：`./a 加法` 只运行名字里含有“加法”的测试。`make unit F=a.lark T=加法` 会一次完成编译和运行。
- 测试名字不能重复。只收命令行给出的文件里的测试，`import` 进来的模块里的测试只检查语法。
- 编译器自己也有单元测试：`compiler/*.lark` 末尾的 test 块测词法、解析、类型表、检查（含警告）、所有权检查的状态合并、代码生成（C 字符串和标识符、类型的 C 名字，以及把一小段源码完整编译成 C 后检查里面的关键片段）和命令行的路径处理。`make unit-compiler [T=名字里的一段]` 单独运行；`make test1` 也会跑，只要求全部通过、不记预期输出。

### 格式化

`tools/fmt.lark` 是用 Lark 写的格式化工具 lark-fmt：

```sh
make fmt-tool                    # 得到 build/lark-fmt
make fmt                         # 就地格式化编译器、标准库、工具和示例
make fmt-check                   # 只检查，列出还没格式化的文件
./build/lark-fmt --stdout a.lark # 把结果打印出来
```

- 只调整空白，不改变代码的意思，也不挪动换行（所以 `} else` 之类的写法照旧）。注释、字符串（包括跨行的字符串和 `#{ }` 插值）、字符字面量的内容原样保留。
- 缩进：每层 `{ ( [` 缩进 4 格，同一行里打开的几个括号只算一层；以 `} ) ]` 开头的行和打开它的那一行对齐。
- 续行：上一行以运算符（`+ && = => -> ??` 等）结尾，或者这一行以 `.` 开头时，比语句的第一行多缩进 4 格；续行上打开的括号按语句的第一行算，所以多行的 `if` 条件后面的块照常只缩进 4 格。
- 行内：连续的空格合成一个；`( [` 后面和 `) ] ,` 前面不留空格；`,` 后面一个空格；`{` 前后、`}` 前各一个空格（`{}` 除外）。行尾注释前面的空格原样保留，方便对齐。运算符两边的空格不动。
- 空行：去掉行尾空白和 `\r`，连续的空行合成一行，文件开头、`{` 之后和 `}` 之前的空行去掉，文件以一个换行结尾。

### 项目与依赖

`make lark-tool` 得到 `build/lark`（`tools/lark.lark`，用 Lark 自己写）。它按自己所在的位置找到 `build/lark1`、`runtime/` 和 `std/`，可以把 `build/` 加进 PATH，或者设置 `LARK_HOME`。

```
lark new hello          # 新建 hello/：lark.pkg、main.lark、.gitignore
cd hello
lark run -- 参数        # 编译并运行；lark build [--release] 只编译，得到 build/hello
lark test [名字片段]    # 编译并运行 test 块
lark fetch              # 只下载依赖，列出每个依赖在哪里
```

项目根目录下的 `.lark` 文件一起构成根模块。`lark.pkg` 一行一项（`#` 开头是注释）：

```
name = hello
version = 0.1.0
dep util = ../util                           # 本地目录，相对于这个 lark.pkg
dep json5 = github.com/someone/json5 v1.2.0  # git 仓库和标签（或分支）
c_src = native/fast.c                        # 一起编译的 C 文件，每个一行
link = sqlite3                               # 链接时加 -lsqlite3，每个一行
```

- git 依赖可以是任何 git 服务器：`host/路径` 补成 `https://host/路径`（github、gitee、gitlab、公司自己的服务器都一样），也可以写完整的 `https://…` 或 `git@…` 地址。下载用系统的 `git clone --depth 1 --branch 版本`，放在 `$LARK_CACHE`（默认 `~/.lark/pkg`）。
- 第一次下载时把提交号写进项目的 `lark.lock`；之后同一个标签指向的提交变了会报错，避免依赖被悄悄换掉。
- 依赖的根目录也要有 `lark.pkg`，`name` 和 `dep` 写的名字一致。`import "json5"` 载入它的 `json5.lark`（没有这个文件也行，只是不能这样 import），`import "json5/sub"` 载入它的 `sub.lark`。依赖包里的文件自己写的 import（例如 `import "http/request"`）相对于依赖的根目录，和在哪里编译无关；所以应用也能当依赖，只用它的模块、不用它的 `main`（`apps/lcache` 就这样用 `apps/lhttp` 的 `http/request`）。依赖的依赖也会载入；同一个名字只能指向同一个来源和版本，否则报“依赖冲突”。依赖里的 `c_src`、`link` 一起参与构建。
- 底下是 lark1 的新选项 `-p 名字=目录`：import 路径的第一段是这个名字时到那个目录里找。`std` 也是这样映射到安装目录的 `std/`，所以项目放在哪里都能 `import "std/…"`。
- C 编译器和选项来自 `$CC`、`$CFLAGS`。还没有：语义化版本的范围（`^1.2`）、发布和中心仓库、按平台区分的 C 文件。

## 标准库

`std/` 下的模块都用 Lark 自己写。在程序开头写 `import "std/map"`、`import "std/str"`、`import "std/iter"`、`import "std/set"`、`import "std/sort"`、`import "std/utf8"`、`import "std/heap"`、`import "std/bytes"`、`import "std/deque"`、`import "std/flag"`、`import "std/rand"`、`import "std/math"`、`import "std/fmt"`、`import "std/json"`、`import "std/re"`、`import "std/digest"`、`import "std/base64"`、`import "std/http"`、`import "std/os"`、`import "std/time"`、`import "std/io"`、`import "std/term"`、`import "std/proc"`、`import "std/csv"`、`import "std/log"`、`import "std/zlib"`、`import "std/diff"`、`import "std/net"`、`import "std/signal"`、`import "std/timer"`、`import "std/sync"` 即可（见“模块与可见性”）。

什么该进标准库、接口怎么写、测试要做到什么程度，见 `docs/std.md`；以后要补哪些能力，见 `docs/std-roadmap.md`。`make apicov` 检查每个公开函数都有测试调用过（`make check` 也会跑）；`make apicov U=1` 列出只有测试和示例在用的函数，给人审。

**接口改名**（按 `docs/std.md` 的“名字”统一用词，没有留旧名字）：
- 字符串：`str.split(s, sep)` 改成按字符串切（原来的 `split_str`），按字节切的那个删掉了：`str.split(path, '/')` 写成 `str.split(path, "/")`。
- 容器：`count` 删掉了，个数用内置的 `len(m)`（调用类型的 `iter_len`）；`map.put` → `insert`，`set.add` → `insert`，`set.intersect` → `intersection`，`set.items` / `deque.items` → `to_list`，`deque.at` → `get`，`heap.drain` → `into_sorted`。
- 随机数：`rand.below(n)` / `rand.int_in(lo, hi)` → `range(lo, hi)`，`bits64` → `next_int`，`chance` → `next_bool`。
- 时间：`since` → `elapsed_ns`，`dur` → `format_dur`，`iso` / `iso_at` → `format_iso` / `format_iso_at`，`utc` / `at_offset` → `date_utc` / `date_at`，`to_unix` → `to_unix_ms`；删掉了 `time.sleep`（用内置的 `sleep_ms`）和 `weekday_name`。
- 正则：`compile(p, 忽略大小写)` → `compile(p)`，忽略大小写写成 `(?i)`；`search` / `search_in` → `find_at` / `find_in`（返回 `(开始, 结束)?`），`matches_in` → `is_match_in`，`replace` → `replace_all`，`lower` → `casefold`。
- os：删掉了 `env_or`（写成 `os.env(name) ?? 默认值`）；`list` → `read_dir`，`run` / `capture` → `shell` / `shell_output`（经过 sh，和不经过 sh 的 `proc.run` / `proc.output` 分开）。
- http：`parse` → `parse_request`，`build` → `format_response`，`http_date` → `format_date`，`url_decode` / `url_encode_path` → `unescape_path` / `escape_path`，`html_escape` → `escape_html`，`mime` → `mime_type`，`dechunk` → `decode_chunked`，`send` → `request`。
- json：`size` → `count`，`keys_of` → `keys`，`obj` → `object`，`stringify` / `pretty` → `format` / `format_pretty`，`str_at` / `int_at` / `float_at` / `bool_at` → `path_str` / `path_int` / `path_float` / `path_bool`。
- csv：`col` → `find_column`，`row` / `row_sep` / `field` → `format_row` / `format_row_sep` / `format_field`。flag：`bool_flag` / `str_flag` / `int_flag` → `add_bool` / `add_str` / `add_int`，`parse_list` → `parse_from`。digest：`hex` / `unhex` → `to_hex` / `from_hex`。
- fmt：`left` / `right` / `center` → `align_left` / `align_right` / `align_center`，`group` → `thousands`，`code_width` → `char_width`，`bytes` → `byte_size`。utf8：`sub` → `slice_chars`，`codes` / `from_code` → `code_points` / `from_code_point`。math：`modulo` → `floor_mod`。diff：`lines` → `lines_with_ends`。
- io、net：`error` → `last_error`，`io.take_buffered` → `read_buffered`。term：`raw` → `enable_raw`，`alt_screen(开关)` → `enter_alt_screen()` / `leave_alt_screen()`，`resized` → `was_resized`，`color_ok` → `supports_color`，`move` → `move_to`，`strip` → `strip_ansi`。
- 第二轮（对照 Rust、Go、Zig、Elixir、Gleam 再审一遍）：`str.pad_left` / `pad_right` → `pad_start` / `pad_end`（和 `trim_start` 一致，Gleam 也这样叫）；`http.percent_decode` / `percent_encode_path` → `unescape_path` / `escape_path`（Go 的 `PathUnescape` / `PathEscape`）；`http.keep_alive` → `is_keep_alive`；`map.entries` → `to_list`；`json.set` → `insert`；`io.from_fd(fd, owns)` → `from_fd(fd)`（不关闭 fd）；`io.append` → `open_append`；`net.set_timeout` → `set_timeout_ms`；`log.line` → `format_line`。`map.update(k, init, f)` 的语义改了：键不存在时直接放入 `init`，不再是 `f(init)`，和 Elixir 的 `Map.update` 一样，计数写成 `m.update(w, 1, |n| n + 1)`。
- 阶段 0（`docs/std-roadmap.md`）：删掉 `digest.sha1_hex` / `sha256_hex`（写成 `digest.to_hex(digest.sha1(s.to_bytes()))`）；`base64.decode` / `decode_url` / `decode_str` 和 `digest.from_hex` 从 `T?` 改成 `T!`（调用处把 `Some` / `None` 换成 `Ok` / `Err`，`?? 默认值` 照旧能用）；zlib、gzip、deflate、CSV 的错误信息加上位置，写成 `zlib 第 9 个字节：…`、`CSV 第 2 行：…`。标准库的公开类型都能直接插值了（`"#{m}"` 得到 `{"a": 1}`）。
- 阶段 1：新加 `std/bytes`（二进制里的整数，换掉了 zlib、digest、lgit 各自写的版本）；`os.FileInfo` 加了 `is_symlink` 和 `mode` 两个字段（自己构造 `FileInfo` 的地方要补上），新加 `os.lstat`、`os.chmod`、`os.symlink`、`os.read_link`；`os.remove_all` 遇到符号链接不再删进它指向的目录。整数字面量可以写八进制 `0o755`。新加 `std/signal`（`notify` / `wait`），lredis、lhttp、lcache 收到 SIGINT、SIGTERM 时写一行日志退出。`std/flag` 加了子命令（`add_command`、`a.command`、`usage_of`）和 `parse_or_exit`；`Args` 多了 `command` 字段。`std/re` 换成 Pike VM，加了分组（`captures`、`captures_at`、`r.groups`）、`{m,n}` 和非贪心；行为变化：`(`、`)`、`{m,n}` 不再是普通字节（要搜它们写 `\(`），`^ $` 写在中间也是锚点，`replace_all` 的换成的文字里 `$1`、`$$` 有了意思，去掉了没人用的 `re.Atom`。lgrep、ledit 改用 `parse_or_exit`，`-h` 的用法说明改到标准输出、退出码从 2 改成 0。flag 的短开关写在一起时，要值的字母可以放在最后（`-zf 包`、`-n5`，和 getopt 一样），以前这样写是报错。验收程序 `apps/ltar`：读写 tar 和 tar.gz，和系统的 tar 互相解开对方打的包。
- 阶段 2：新加 `std/timer`（`deadline`、`every`）和 `std/sync`（`Cancel`）。lcache 的清理任务改用它们：以前靠“accept 的任务放掉通道副本、清理的任务收到 done”这个副作用退出，现在 accept 结束时 `stop.cancel()`。
- 阶段 2：`std/net` 加了 Unix 域套接字（`listen_unix`、`connect_unix`）、UDP（`listen_udp`、`UdpSocket`、`Datagram`）和 `lookup`，底下是运行时里新加的几个 C 函数（`lark_udp_*`、`lark_unix_*`、`lark_lookup`）。`std/http` 加了服务器的连接循环和路由（`serve`、`new_router`、`handle`、`route`、`param`、`reply`、`reply_error`），`Request` 多了 `params` 字段（自己构造 Request 的地方要补上）。lhttp、lcache 删掉了各自的连接循环，`files.handle`、`api.handle` 改成返回 `http.Response`、去掉了 `conn` 参数。`std/http` 加了能复用连接的客户端 `http.Client`（`new_client`、`get`、`request`、`close`）；一次性的 `http.get` / `http.request` 发的 Host 现在带上不是 80 的端口。
- 阶段 2：`http.serve_until`（优雅退出），`net.is_timeout`、`Listener.set_timeout_ms`；TCP 读、写、accept 超时的错误信息从系统的原话（如 “Resource temporarily unavailable”）改成以“：超时”结尾。验收程序 `apps/lproxy`：反向代理，按路径前缀转给上游，502 / 504，SIGTERM 时优雅退出。
- 评审修复（`docs/std-review.md`、`docs/std-cert-review.md`）：`os.walk` 和 `os.glob` 的 `**` 不再跟符号链接走（链接本身算一项，成环也能走完），查不了信息的条目是错误；`os.glob("src/**")` 现在包括下面的文件。`zlib.decompress` / `gunzip` / `inflate` 最多解出 `zlib.MAX_OUT`（256 MiB），要别的上限用新加的 `decompress_max` / `gunzip_max` / `inflate_max`。`http.parse_request` 遇到值不同的重复 `Content-Length` 回 400，`Content-Length` 只认十进制数字；`is_keep_alive` 按 token 比；`format_response` 和客户端发的头部里 `\r` `\n` 换成空格、名字不合法的头部不写，1xx 不写 `Content-Length`，`status_text` 补齐 RFC 9110 的状态码。`time.parse_iso` 认 `-0002-…`、`10000-…` 这样的年份（`format_iso` 写出来的都能读回来）。`utf8.is_valid` 改严了（过长编码、代理区、超过 U+10FFFF 都不合法），`utf8.from_code_point` 遇到代理区 panic。`csv.format_sep` / `format_row_sep` 的分隔符是 `\r` `\n` `"` 时 panic。`re.compile` 的括号最多套 1000 层，超过返回错误。`io.read_all` 读大文件不再是平方时间；`io.read_buffered` 的 max 是负数时 panic。`fmt.byte_size` 对最小的 int 返回 `"-8 EiB"`。`make apicov` 几项检查都做完再报错。
- 形式化证明标准库（`formal/Lark/Utf8.lean`）时发现：utf8 的解码会把不合法的字节当成码点。现在照 Go：不合法的地方（形状不对、被截断、过长编码、代理区、超过 U+10FFFF）每次一个字节，码点是 U+FFFD。行为变化：`code_points("\xC3A")` 从 `[193]`（A 被吞掉）变成 `[0xFFFD, 65]`，`chars` 也切成两个；`C0 80` 不再解出 NUL，`ED A0 80`、`F7 BF BF BF` 不再解出 `from_code_point` 会 panic 的码点；`fmt.width` 改用 `utf8.code_points`，不合法的字节各占一列。
- 新增 `bytes.push_uvarint` / `bytes.uvarint`（无符号 varint）。第一次先在 Lean 里写规格并证明（`formal/Lark/Varint.lean`：写出来再读回去不变；任意输入读成功时结果不超出 64 位、最多读 10 个字节），再照着写 Lark 代码。
- 新增 `std/treemap`（有序表 `TreeMap[K, V]`，AVL 树）。和 varint 一样先在 Lean 里写模型并证明（`formal/Lark/TreeMap.lean`：insert / remove 之后仍然平衡、中序按键递增，get 的结果对，at 是中序的第 i 项），再照着一一对应地写 Lark 代码。
- 新增 `std/url`（查询串的编码、解码、`parse_query` / `format_query`），先在 Lean 里证明（`formal/Lark/Url.lean`：escape 再 unescape 回到原样，escape 的结果里没有 `& = ;`，任何键值对列表 format 再 parse 回到原样）。lcache 的 `?ttl=` 改用 `url.parse_query`，现在会解码（`ttl=%36%30` 也是 60 秒）。
- 新增 `std/semver`（语义化版本的解析、写出、比较）。先在 Lean 里证明（`formal/Lark/Semver.lean`：比较是全序；合法的版本写出来再解析回到原样），规范第 11 条的排序例子在证明里和测试里都检查了。
- `map.hash(str)` 从 FNV-1a 换成带随机密钥的 SipHash-1-3，每个 `Map` 的槽位带随机种子（防哈希洪水攻击）。同一个进程里哈希值稳定，**每次运行不一样**：别把 `hash` 的结果写进文件或发给别的进程；`Map` 的遍历顺序不受影响。

- `std/map.lark`：哈希表 `Map[K, V]`（开放寻址、线性探测，槽数是 2 的幂，按插入顺序保存键）。
  - `m: map.Map[str, int] = map.new()`，`m.insert(k, v)`（已经有这个键时换掉值），`m.get(k)` 返回 `V?`（值的副本），`m[k]` / `m[k] = v`，`m.contains_key(k)`，`len(m)`，`m.remove(k)` 返回 `V?`（其余键保持插入顺序，O(n)），`m.retain(|k, v| …)`（只留下满足条件的，返回删掉几项；只重建一次，删很多项时用它），`m.update(k, init, |v| …)`（有则改成 `f(旧值)`、无则直接放 `init`，和 Elixir 的 `Map.update` 一样），`m.clear()`，`m.is_empty()`，`m.to_list()` 返回 `[(K, V)]` 副本。
  - 遍历：`for (k, v) in m`（借用遍历），`for k in m.keys` / `for v in m.vals`（同一顺序）；遍历时不能修改 m。
  - 键要满足 `Hash + Eq`，内置 int / bool / str 的 `hash`（int 是乘法散列；str 是 SipHash-1-3，密钥在进程启动后随机取，每次运行的值不一样），每个 Map 的槽位还带一个随机种子：别人造不出一批专门挤在一起的键（哈希洪水攻击），遍历照旧按插入顺序，输出每次一样。自己的类型写一个 `fn hash(p: Point) -> int` 就能当键，返回值可以是任意 int。
- `std/set.lark`：集合 `Set[T]`（底下是 `Map[T, bool]`，按插入顺序）。`set.new()`、`set.of(xs)`、`s.insert(x)`、`s.contains(x)`、`s.remove(x) -> bool`、`len(s)`、`s.is_empty()`、`s.to_list()`、`for x in s`（借用遍历），以及 `set.union / intersection / difference(a, b)`。
- `std/str.lark`：`str.split(s, ", ")`（按字符串切，和 Go 的 `strings.Split` 一样）、`str.words(s)`、`str.lines`、`str.trim` / `trim_start` / `trim_end`、`str.trim_prefix` / `trim_suffix`、`str.starts_with`、`str.ends_with`、`str.contains`、`str.find(s, sub) -> int?`、`str.find_from(s, sub, 起点)`、`str.rfind`、`str.count`（不重叠）、`str.repeat`、`str.replace_all`、`str.to_upper` / `str.to_lower`（只改 ASCII 字母）、`str.pad_start` / `str.pad_end`。 另有 `str.cut(s, "=") -> (str, str)?`（在第一个分隔处切成两半）、`str.split_n(s, ":", 2)`（最多切成几段）；`repeat` 和 `pad_start` / `pad_end` 是线性时间。
- `std/sort.lark`：稳定的归并排序。`sort.sort(&xs)` / `sort.sorted(xs)` 要求 `T: Ord`；`sort.sort_by(&xs, |a, b| …)` / `sort.sorted_by(xs, |a, b| …)` 用自定义比较（负数表示 a 在前）；另有 `reversed`、`is_sorted`、`min_of`、`max_of`（后两个返回 `T?`）。已排好的列表用 `binary_search(xs, x) -> int?` / `lower_bound` / `upper_bound` 二分查找；`dedup(&xs)` 原地去掉相邻的重复（先 `sort` 再 `dedup` 就是去重，要求 `T: Eq`）。
- `std/utf8.lark`：按字符（Unicode 码点）处理 `str`（`len`、`byte_at`、`slice` 都按字节）。`utf8.count(s)`（字符个数）、`utf8.chars(s) -> [str]`、`for ch in utf8.each(s)`（逐个字符，不先建列表）、`utf8.code_points(s) -> [int]`、`utf8.from_code_point(cp)`、`utf8.slice_chars(s, a, b)`（按字符下标取 `[a, b)`，越界时截到两端）、`utf8.is_valid`。不合法的字节按一个字节算一个字符、码点是 U+FFFD（和 Go 一样），所以不会 panic，`code_points` 给出的码点都能交给 `from_code_point`（`formal/Lark/Utf8.lean` 证过）。
- `std/heap.lark`：优先队列 `Heap[T]`（二叉堆，`T: Ord`，最小的先出来）。`heap.new()`、`heap.of(xs)`、`h.insert(x)`、`h.pop_min() -> T?`、`h.peek_min() -> T?`（副本）、`len(h)`、`h.is_empty()`、`heap.into_sorted(h)`（拿走 h，从小到大返回）。要最大的先出来，就给元素类型写一个反过来的 `cmp`。插入和取出都是 O(log n)，元素只移动不复制。
- `std/deque.lark`：双端队列 `Deque[T]`（环形缓冲区，满了时容量翻倍）。`deque.new()`、`deque.of(xs)`、`d.push_back(x)` / `d.push_front(x)`、`d.pop_back()` / `d.pop_front()`（`T?`），`d.front()` / `d.back()` / `d.get(i)`（`T?`，副本），`len(d)`、`d.is_empty()`、`d.clear()`、`d.to_list()`、`for x in d`（借用遍历，从队头到队尾）。两头的放和取都是 O(1)。
- `std/treemap.lark`：有序表 `TreeMap[K, V]`（AVL 树，`K: Ord`，照 Rust 的 BTreeMap）。`treemap.new()`、`m.insert(k, v)`（已有的键换成新值）、`m.get(k)`（`V?`，副本）、`m.contains_key(k)`、`m.remove(k)`（`V?`）、`m.first_key_value()` / `m.last_key_value()`（`(K, V)?`）、`m.at(i)`（按键排第 i 的一对，`(K, V)?`）、`len(m)`、`m.is_empty()`、`m.clear()`、`m.to_list()`、`for (k, v) in m`（借用遍历，按键从小到大）、`"#{m}"`。insert、get、remove、at 都是 O(log n)。先证明再写（`formal/Lark/TreeMap.lean`）。
- `std/semver.lark`：语义化版本（semver.org 2.0.0）。`semver.parse(s) -> Version!`（`v.major` / `v.minor` / `v.patch` / `v.pre` / `v.build`，数字不能有前导零，标识符只能用 `0-9 A-Z a-z -`）、`semver.format(v)`、`cmp(a, b)`（规范第 11 条；构建信息不参与比较；接口方法，不加模块名），`Version` 满足 `Ord`，可以 `a < b`、`sort.sort`。先证明再写（`formal/Lark/Semver.lean`）。
- `std/bytes.lark`：二进制数据里的整数，和 Go 的 `encoding/binary` 一样。`bytes.push_u32_be(&out, v)` 往 `[u8]` 末尾追加（`push_u16_be` / `push_u16_le` / `push_u32_le` / `push_u64_be`），`bytes.u32_be(d, at)` 从 `d[at]` 读（`u16_be` / `u16_le` / `u32_le` / `u64_be`）。读越界时和 `d[i]` 一样 panic，读外部数据先检查长度。变长整数：`bytes.push_uvarint(&out, v)` 写无符号 varint（LEB128，最多 10 个字节），`bytes.uvarint(d, at)` 返回 `(值, 读了几个字节)!`，数据不完整或超出 64 位时是错误（先证明再写，见 `formal/Lark/Varint.lean`）。可增长的字节缓冲就是 `[u8]`。
- `std/flag.lark`：命令行参数。`p = flag.new(程序名, 说明)`，`p.add_bool(长名, 短名, 说明)`、`p.add_str(长名, 短名, 默认值, 说明)`、`p.add_int(…)`（短名写 `""` 表示没有）；`p.parse() -> Args!` 解析 `args()`（跳过程序名），`p.parse_from(xs)` 解析给定的列表；结果用 `a.get_bool(名)`、`a.get_str`、`a.get_int` 取值，`a.rest` 是位置参数。支持 `--name=v`、`--name v`、`-n v`、`--` 之后全是位置参数（`a.dash` 是它们在 `a.rest` 里开始的下标，没写 `--` 时是 -1：`diff 版本 -- 路径` 这样的写法靠它分开两段）；未知参数、缺值、int 写错时返回 `Err`，`-h` / `--help` 返回 `Err("help")`。`p.usage()` 生成对齐的用法说明。命令行程序一般直接写 `a = p.parse_or_exit()`：`-h` 时把用法打印到标准输出、退出码 0，出错时打印“程序名：原因”和用法、退出码 2。子命令：每个命令用 `flag.new(命令名, 说明)` 建一个 Parser、加它自己的选项，再 `p.add_command(c)`；解析后 `a.command` 是选中的命令，命令前面只能写全局选项，后面全局的和命令自己的都能写；`lark build -h` 返回 `Err("help build")`，说明是 `p.usage_of("build")`（构建工具 `tools/lark.lark` 就是这样写的）。
- `std/rand.lark`：可复现的伪随机数（xoshiro256**，种子经 SplitMix64 展开；不适合密码学用途）。`rand.new(seed)`、`rand.from_time()`，`r.range(lo, hi)`（`[lo, hi)`，拒绝采样，没有取模偏差）、`r.next_int()`（64 位）、`r.next_float()`（`[0, 1)`，53 位）、`r.next_bool(p)`、`r.shuffle(&xs)`、`r.choice(xs) -> T?`、`r.sample(xs, k)`（不重复）。
- `std/time.lark`：时钟、时长和日期。`time.now()`（单调时钟的 `Instant`）、`time.elapsed_ns(t)`、`time.elapsed_ms(t)`；`time.format_dur(ns)`（`"12.3ms"`、`"2m5s"` 这样的时长）和 `time.parse_dur("1h30m") -> int!`（纳秒；单位 ns us µs ms s m h，可以带小数、连着写，和 Go 的 ParseDuration 一样）；`time.unix_ms()`、`time.unix_ns()`；`time.date_utc(ms)` 得到 `Date`（年月日、时分秒、毫秒、星期），`time.date_at(ms, 分钟)` 按固定时差换算，`time.to_unix_ms(d)` 转回去；`d.format()`、`d.format_iso()`、`time.format_iso_at(ms, 分钟)`（`"…+08:00"`）和 `time.parse_iso(s) -> int!`（也认 `+08:00` / `-0530` 这样的时差）；`time.is_leap`、`time.days_in_month`；`time.local_offset(ms)`（系统时区在这一刻的时差，分钟；底下是运行时的 `lark_tz_offset`，用 `localtime_r`）。睡一会儿用内置的 `sleep_ms`。
- `std/io.lark`：带缓冲的读写。`io.open(path)?`、`io.stdin()` 得到 `Reader`：`r.read_line() -> str?`（不含 `\n` 和行尾的 `\r`，读完或出错时 `None`，错误在 `r.last_error()`）、`r.read_all()?`、`r.close()?`；`io.create(path)?`、`io.open_append(path)?`、`io.stdout()`、`io.stderr()` 得到 `Writer`：`w.write(s)?`、`w.write_line(s)?`、`w.flush()?`、`w.close()?`。每次从系统读写 64KB；`Reader` 和 `Writer` 有析构，离开作用域时自动写出剩下的内容并关闭文件（这时的错误看不到，需要知道就调用 `close`）。
- `std/net.lark`：TCP。`net.listen(host, port)?` 得到 `Listener`（端口给 0 时由系统挑，用 `l.local_port()?` 查），`l.accept()?` 和 `net.connect(host, port)?` 得到 `Conn`：`c.write(s)?`、`c.write_line(s)?`（不缓冲，直接发出去），`c.read_line() -> str?`、`c.read(max)?`、`c.read_all()?`（带缓冲，和 `io.Reader` 一样），`c.set_timeout_ms(ms)?`、`c.last_error()`、`c.close()?`。对方关闭后再写返回错误，不会因为 SIGPIPE 退出。`Listener`、`Conn` 有析构，可以 `spawn` 到别的任务里。例子见 `examples/net.lark`（本机的回显服务器和客户端）。
  另有 Unix 域套接字 `net.listen_unix(路径)` / `net.connect_unix(路径)`（得到的也是 Listener、Conn；路径已经存在时报错，不替你删），UDP `u = net.listen_udp(host, port)?`、`u.send_to(host, port, 文字)?`、`d = u.recv_from(max)?`（`Datagram`：`d.data`、`d.host`、`d.port`；没有数据时任务挂起，长出来的丢掉；`u.set_timeout_ms`、`u.local_port`、`u.close`），和 `net.lookup(host) -> [str]!`。`Listener` 也能 `set_timeout_ms`（accept 等到点返回错误）；读、写、accept、`recv_from` 超时的错误都以“：超时”结尾，用 `net.is_timeout(e)` 判断（IPv4、IPv6 地址，按系统给的顺序）。
- `std/signal.lark`：接收信号，和 Go 的 `signal.Notify` 一样。`sigs = signal.notify([signal.INT, signal.TERM])?` 登记以后这两个信号不再直接结束程序，`sigs.wait()?` 挂起当前任务直到其中一个来，返回编号，`signal.name(n)` 是 `"SIGINT"` 这样的名字。服务在打印“准备好了”之前 notify，再在 scope 里 spawn 一个任务等（见 lredis 的 `on_signal`）。只支持 HUP、INT、QUIT、TERM；登记以后到程序结束都有效。
- `std/timer.lark`：`select` 的 `after` 只管一次等待，这里补两种要自己算的时间。`d = timer.deadline(ms)`：几次等待共用一个截止时间，`after d.left_ms() => …`（还剩几毫秒，到了是 0），`d.is_expired()`。`t = timer.every(ms)`：按开始的时刻对齐的间隔，`after t.next_ms() => …` 或 `t.wait()`，错过的不补，`t.count()` 是到现在过了几个间隔。用单调时钟，改系统时间不影响。
- `std/sync.lark`：`c = sync.new_cancel()` 一个任务说“不用做了”，其他拿着 `c.copy()` 的任务都能知道：`c.cancel()`（重复调用没关系）、`c.is_cancelled()`、`c.wait()`；在 select 里等用 `stop = c.watch()`（`Chan[bool]`，取消时收到 true），在循环外面 watch 一次。见 lcache 的清理任务。读写锁、原子整数等还没有，用内置的 `Mutex`。
- `std/term.lark`：终端。`term.is_tty(fd)`、`term.size() -> (行, 列)?`；`term.enable_raw(毫秒)?` 进入原始模式（不回显、不按行缓冲，Ctrl-C 读到字节 3，换行要写 `\r\n`；没有输入时 `term.read(max)` 最多等这么久就返回 `""`，给 0 就一直等），`term.was_resized()`（进入原始模式后有没有收到 SIGWINCH），`term.enter_alt_screen()` / `term.leave_alt_screen()`，`term.restore()?`；正常退出、`exit` 和 panic 时都会自动恢复终端。转义序列：`term.move_to(行, 列)`、`CLEAR`、`CLEAR_LINE`、`HOME`、`HIDE_CURSOR` / `SHOW_CURSOR`，`term.color(s, term.RED)`（0..15、256 色）、`term.bold`、`term.style(s, "1;4")`、`term.strip_ansi(s)`（去掉转义序列）、`term.supports_color(fd)`（是终端、没有 `NO_COLOR`、`TERM` 不是 dumb）。底下是运行时里的 `lark_term_*` 几个 C 函数（termios、`TIOCGWINSZ`、SIGWINCH），用 `extern "c"` 调用。例子是 `apps/ledit`。
- `std/proc.lark`：子进程，参数列表直接交给程序（`posix_spawnp`），不经过 sh，不用转义。`proc.run(argv) -> Output!`（等它结束：`code`、`out`、`err`，标准输入是空的），`proc.run_with(argv, 输入, 目录)`，`proc.output(argv) -> str!`（只要标准输出，退出码不为 0 时是错误，带着标准错误），`proc.status(argv) -> int!`（和当前程序共用终端）。更多选项用 `o = proc.opts()` 改字段再 `proc.run_opts(argv, o)`：`env`（"名字=值" 设置或覆盖，只写 "名字" 是去掉，其余照样继承）、`timeout_ms`（到时间连同它启动的进程一起用 SIGKILL 结束，返回"命令超时"的错误；为此子进程放在自己的进程组里，所以只有抓输出时能用）、`input`、`dir`。启动不了（找不到程序、目录不存在）才是错误；被信号终止时退出码是 128 + 信号编号。抓输出时用 poll 同时读写三个管道，输入输出再大也不会互相等死。`proc.quote(s)` / `proc.join_cmd(argv)` 拼给 sh 的命令（配合 `os.shell` / `os.shell_output`）。
- `std/csv.lark`：RFC 4180。`csv.parse(s) -> [[str]]!`、`csv.parse_sep(s, '\t')`（引号里可以有分隔符、换行和写成 `""` 的引号；`\r\n` 和 `\n` 都行；各行列数可以不同），出错时带行号；`csv.find_column(表头, 名字) -> int?`；写：`csv.format(rows)` / `format_sep`、`csv.format_row(fields)` / `format_row_sep`、`csv.format_field(s, sep)`（需要时才加引号）。
- `std/log.lark`：`lg = log.new(名字)`，`lg.debug` / `info` / `warn` / `error(msg)`，`lg.log(级别, msg, [键, 值, …])`，`lg.with(键, 值)` 返回带固定字段的新 Logger。默认级别看 `LARK_LOG`（debug / info / warn / error / off，默认 info），`LARK_LOG_FORMAT=json` 时每行一个 JSON 对象。字段都是 pub 的（`level`、`as_json`、`show_time`、`fd`、`name`、`fields`），写到标准错误，每条一次 write。文字格式：`2026-10-29T04:24:01.123Z INFO lhttp: 开始监听 port=8080`，值里有空格、`=`、引号或控制字符时按 JSON 加引号；`lg.format_line(级别, msg, kv, 毫秒)` 只拼出文字。语言里没有可写的全局变量，所以没有包级的 `log.info(…)`。
- `std/zlib.lark`：`zlib.compress` / `decompress`（zlib 格式，git 对象、PNG 用的），`zlib.gzip` / `gunzip`（.gz，几段连在一起的也能解），`zlib.deflate` / `inflate`（不带头和校验和），`zlib.adler32`。压缩是 LZ77（32KB 窗口、哈希链）加固定 Huffman 码，压不小时改用不压缩的块；没有动态 Huffman 码，所以压缩率不如 zlib 的默认级别。解压支持全部三种块，测试里和系统的 `gzip` 互相解对方的输出。来自 lgit。
- `std/diff.lark`：Myers 算法。`diff.unified(旧名, 新名, 旧, 新)` 是 `diff -u` 的格式（两边一样时是 `""`），`diff.hunks(旧, 新)` 只要 `@@` 开始的部分，`diff.hunks_with(旧, 新, diff.Opts(context: 行数, func: 要不要像 git 一样在 @@ 后面带上所在的函数))`；`diff.edits(a, b) -> [int]`（`diff.SAME` / `DEL` / `ADD`，一段改动里先删后加）、`diff.lines_with_ends(text)`（每行带着 `\n`）。两头相同的行先去掉再比，只改了几行的大文件也快；内存是 O(D²)（D 是改动的行数），改动超过约 2000 行时换成 Myers 的线性空间分治，大文件整个重写也不会占几个 GB。测试里和系统的 `diff -u` 逐字对比。来自 lgit（git 专用的 `diff --git` 头在 `apps/lgit/git/patch.lark`）。
- `std/math.lark`：`math.MAX` / `math.MIN`，`abs`、`min`、`max`、`clamp`、`sign`、`pow`（快速幂）、`gcd`、`lcm`、`isqrt`、`floor_div` / `floor_mod`（向下取整的除法和非负余数；`/` 和 `%` 是向零取整的）、`sum`。float 版：`math.PI`、`math.E`、`math.INF`、`math.NAN`，`abs`、`min`、`max`、`clamp`、`sign`、`sum` 按第一个参数的类型重载（float 的乘方用内置的 `float_pow(x, y)`），另有 `is_nan`、`is_inf`、`is_finite`、`approx(a, b, eps)`（按相对误差比较）。
- `std/fmt.lark`：`fmt.hex`、`fmt.bin`、`fmt.radix(n, base)`，`fmt.thousands(1234567)` → `1,234,567`，`fmt.fixed(31416, 4)` → `3.1416`，`fmt.fixed(3.14159, 2)` → `3.14`，`fmt.width(s)`（终端显示宽度：中日韩文字、全角符号、表情两列，— … → 这类标点一列，组合附加符号 0 列；`fmt.char_width(码点)` 是单个字符的），按显示宽度补空格的 `align_left` / `align_right` / `align_center`，以及 `fmt.table(rows)`：对齐的表格，第一行是表头，数字列靠右。 另有 `fmt.byte_size(1536)` 是 `"1.5 KiB"`（按 1024 进位，保留一位小数）。
- `std/json.lark`：`json.Json` 枚举（`Null`、`Bool`、`Num`（int）、`Float`（float）、`Str`、`Arr`、`Obj`），`json.parse(s) -> Json!`（出错信息带行列），`get(j, 键)`、`at(j, 下标)`、`as_int`（只认 `Num`）、`as_float`（`Num` 和 `Float` 都认）、`as_bool`、`as_str`、`count`、`keys`，`format`（紧凑）和 `format_pretty`（缩进两格），插值时同 `format`。整数读成 `Num`，不丢精度；带小数点或指数的数、以及超出 int 范围的整数读成 `Float`；输出 `Float` 用最短写法，`inf` / `nan` 写成 `null`；`\uXXXX` 和代理对会转成 UTF-8。 按路径取：`json.path(j, "user.tags.0") -> Json?`（对象按键、数组按下标），`json.path_str` / `path_int` / `path_float` / `path_bool(j, 路径)`；构造：`json.object([(键, 值), …])`、`json.insert(&j, 键, 值)`。
- `std/re.lark`：正则表达式（按字节匹配；字面量、`.`、`[a-z]` `[^…]`、`\d \w \s`、`* + ?`、`{m}` `{m,}` `{m,n}`、后面加 `?` 变成非贪心、`(…)` 分组和 `(?:…)`、`^ $`、`|`，最前面写 `(?i)` 忽略大小写；没有反向引用和 `\b`）。实现是 Pike VM，时间和 文字长度 × 模式长度 成正比，不会因为 `(a*)*b` 这种写法变成指数时间；带“能以哪些字节开头”的跳过表。`re.compile(模式) -> Re!`、`re.is_match`、`re.find_at(r, s, 起点) -> (开始, 结束)?`、`re.find_all -> [(开始, 结束)]`、`re.captures(r, s) -> [str]?`（第 0 项是整个匹配）、`re.captures_at(r, s, 起点) -> [(开始, 结束)]?`、`re.replace_all`（换成的文字里 `$1` 是第 1 个分组，`$$` 是 `$`）、`re.split`，`r.groups` 是分组个数；一行行扫大段文字时用 `re.casefold` 整段转一次，再用 `re.find_in` / `re.is_match_in` 只看一段；扫很多段时先 `m = re.matcher(r)`，再 `re.is_match_in(&m, …)` / `re.find_in(&m, …)`，线程表在几次匹配之间留着，不用每次重新分配（`find_all`、`replace_all`、`split` 里面也这样做）。选项按写的顺序靠前的优先（和 Go 一样；`grep -E` 取最长的）。来自 lgrep，和 `grep -E` 逐字对比过。
- `std/digest.lark`：`digest.sha256` / `sha512` / `sha1`（`[u8] -> [u8]`，要十六进制写 `digest.to_hex(digest.sha1(s.to_bytes()))`），`digest.hmac_sha256(key, msg)` / `hmac_sha512` / `hmac_sha1`（别的摘要用 `digest.hmac(h, 块长, key, msg)`），比较 MAC 用 `digest.equal(a, b)`（耗时和内容无关，不要用 `==`），`digest.crc32`（zlib / gzip 用的），`digest.to_hex` / `digest.from_hex(s) -> [u8]!`。SHA-1 只为了和 git 这类格式兼容。不叫 `std/hash`：`hash` 是 `Hash` 接口的函数名。
- `std/base64.lark`：`base64.encode(bytes)` / `base64.decode(s) -> [u8]!`、`encode_str` / `decode_str(s) -> str!`（出错信息写明第几个字符不对），以及 URL 安全的 `encode_url` / `decode_url`（`-` 和 `_`，不补 `=`）。解码很严格：字母表以外的字符（包括换行）、长度或 `=` 不对、多余的位不是 0 时都是 `None`。十六进制用 `digest.to_hex` / `digest.from_hex`。
- `std/url.lark`：URL 查询串（照 Go 的 net/url）。`url.escape_query(s)`（字母、数字和 `-._~` 不变，空格写成 `+`，别的写成 `%XX`）、`url.unescape_query(s) -> str!`、`url.format_query([(k, v)])`（按给的顺序，用 `&` 连起来）、`url.parse_query(q) -> [(str, str)]!`（跳过空的段，没有 `=` 时值是 `""`，有 `;` 时出错，重复的键都留着）。先证明再写（`formal/Lark/Url.lean`）。
- `std/http.lark`：HTTP/1.1 协议本身（来自 lhttp）。服务器这边 `http.parse_request(buf, pos) -> (Request?, 下一个的位置, 状态码)`（支持流水线，只认 Content-Length 的请求体）、`http.header`、`http.is_keep_alive`、`http.unescape_path`、`http.format_response(状态码, 头部, 正文, head, conn, 毫秒)`、`http.error_page`、`http.mime_type`、`http.escape_html`、`http.escape_path`、`http.format_date`；客户端：一次性的 `http.get(url) -> Response!`、`http.request(方法, url, 头部, 正文)`（每次一个新连接，读到服务器关闭为止）；要连续发好几个请求时用 `cl = http.new_client()`，`cl.get(url)?`、`cl.request(方法, url, 头部, 正文)?`：用完的连接留着下次用（每个客户端最多 4 条），空闲的连接被对方关掉了时可以重发的方法（GET、HEAD、PUT、DELETE、OPTIONS）自动换新连接再发，跟随最多 5 次重定向（`cl.set_max_redirects(n)`，0 表示不跟随），读写超时 10 秒（`cl.set_timeout_ms(ms)`）；Client 不能在任务之间共用，每个任务建自己的。都只有 http://，解得开 chunked，`http.parse_response`、`http.decode_chunked`、`http.parse_url`。服务器的连接循环：`http.serve(l, h)?`，h 是 `Fn(Request) -> Response`，每个连接一个任务，keep-alive、流水线、30 秒没有动静就关掉，HEAD 只发头部；只有 accept 出错时才返回；要能停下来时用 `http.serve_until(l, h, stop)`（`stop` 是 `sync.Cancel`）：取消以后不再接受新连接，进行中的请求做完（回复里写 Connection: close），空闲的连接关掉，然后返回 Ok（见 lproxy）。回复用 `http.reply(状态码, 头部, 正文)`、`http.reply_error(状态码)`。路由（Go 1.22 的 ServeMux）：`r = http.new_router()`，`r.handle("GET /items/{id}", h)`（方法可以不写；`{名字...}` 是剩下的整段路径），`http.serve(l, |req| http.route(r, req))`，handler 里用 `http.param(req, "id")` 取值；几条都能匹配时取最具体的，路径对、方法不对回 405 和 Allow，都不对回 404。`Request` 多了 `params` 字段。lhttp、lcache 都用它，见 `apps/lcache/main.lark`。
- `std/os.lark`：出错信息是“动作 路径：系统给的原因”。
  - 文件：`os.read` / `os.write` / `os.append`（`str!` / `()!`），`os.exists` / `os.is_file` / `os.is_dir`，`os.stat(p) -> FileInfo!`（`is_file`、`is_dir`、`is_symlink`、`size`、`mtime_ms`、`mode`：权限位，比如 `0o755`）和不跟着符号链接走的 `os.lstat`，`os.chmod(p, 0o755)`，`os.symlink(target, link)`、`os.read_link(p) -> str!`，硬链接 `os.hard_link(existing, new_path)`，`os.set_mtime(p, ms)` 改修改时间（毫秒，和 `mtime_ms` 一样；访问时间不变），`os.rename`、`os.remove`（文件或空目录）、`os.remove_all`（连同目录里的东西；符号链接只删链接本身）。
  - 目录：`os.read_dir(dir) -> [str]!`（按字节序排好，不含 `.` 和 `..`）、`os.mkdir`、`os.mkdir_all`、`os.cwd`。
  - 路径：`os.join_path`、`os.base`、`os.dir`、`os.ext`、`os.stem`、`os.with_ext(p, ".md")`、`os.is_abs`，`os.clean(p)`（合并 `/`、去掉 `.`、抵消 `a/..`）、`os.rel(from, to) -> str?`；这几个只按字面算，不访问文件系统。路径函数放在 `std/os` 而不是单独的 `std/path` 模块：导入了模块的文件不能再用模块名当变量名，而 `path` 是最常用的变量名。
  - 通配符：`os.glob_match(模式, 名字)`（`*` `?` `[a-z]` `[!a-z]` `\`，都不跨 `/`），`os.glob("src/**/*.lark") -> [str]!`（`**` 是任意多层目录，以 `.` 开头的名字要模式那一段也以 `.` 开头才匹配，结果排好序），`os.walk(dir) -> [str]!`（下面所有的文件）。`os.temp_dir()` 是 `$TMPDIR`，没有时是 `/tmp`。 `os.exe_path() -> str!` 是当前程序的绝对路径（解析过符号链接）。`os.at_exit(f)` 登记进程退出时（正常结束、`exit`、`panic`）要执行的 `Fn() -> ()`，按登记的逆序。
  - 环境变量：`os.env(name) -> str?`，要默认值时写 `os.env(name) ?? 默认值`。
  - 子进程：`os.shell_output(cmd) -> str!`（返回标准输出，退出码不为 0 时是错误）、`os.shell(cmd) -> int`（退出码，比 `system` 返回的原始等待状态好用）。这两个经过 `sh`（可以用管道、重定向），参数要自己转义；不需要 shell 时用 `std/proc`（参数直接交给程序）。时间用 `time.unix_ms()`。
  - 底下的内置函数是 `try_write_file`、`try_append_file`、`try_list_dir`、`try_remove`、`try_mkdir`、`try_rename`、`try_cwd`、`try_getenv`、`try_capture`、`file_kind`、`run_cmd`、`now_ms`，以及 `std/time` 用的 `now_ns`、`mono_ns`（单调时钟），`std/io` 用的 `try_open`、`try_fd_read`、`try_fd_write`、`try_fd_close`（文件描述符），`std/net` 用的 `try_tcp_connect`、`try_tcp_listen`、`try_tcp_accept`、`try_sock_port`、`try_sock_write`、`try_sock_timeout`，也可以直接用。
- `std/iter.lark`：列表和迭代器上的常用函数，`import "std/iter"` 之后写 `iter.map(xs, |x| x * 2)`。
  - 来源：`iter.range(lo, hi)`、`iter.count_from(n)`（无限）、任何列表、自定义迭代器，或者能借用遍历的类型（如 Map、Set）。
  - **适配器**（惰性）：`map`、`filter`、`take_n`、`skip_n`、`take_while`、`enumerate`、`zip(a, b)`、`chain(a, b)`，以及把列表包成迭代器的 `each(xs)`。它们只把来源包起来，返回的结构体（`Mapped`、`Filtered`、`Taken`……）本身也是迭代器，每次 `next` 才往前走一步，所以能一层层套、能接在无限迭代器后面：`iter.count_from(1).map(|n| n * n).take_n(5).collect()` → `[1, 4, 9, 16, 25]`。来源是列表时直接传：每个适配器按第一个参数重载，列表的那个先用 `each` 包一下；`zip`、`chain` 的第二个来源要是迭代器，列表写 `ys.each()`。闭包会存进结构体，参数类型是 `Fn(T) -> U`，所以捕获的变量会复制进去（见 `examples/lazy.lark`）。
  - **取值**：`collect`、`fold(it, init, |acc, x| …)`、`find -> T?`、`any`、`all`、`count`，接在列表、迭代器或适配器后面都行。`find`、`any`、`all` 找到答案就停，所以能用于无限迭代器。来源归函数所有，要接着用的列表先 `copy()`。
  - 2026-10 以前分两套：立即求值的 `map` / `filter` / `take_n` / `skip_n` / `enumerate` 直接返回列表，惰性的叫 `lazy_map` 等、不收列表。合并以后旧的写法要改：`iter.map(xs, f)` 后面补 `.collect()`，`lazy_` 前缀去掉（`lazy_take` → `take_n`，`lazy_skip` → `skip_n`），`xs.each().lazy_filter(…)` 可以直接写 `xs.filter(…)`。
  - **链式调用**：`xs.copy().map(|x| x * 2).collect()`、`xs.filter(|x| x > 0).enumerate().collect()`、`Countdown(n: 3).zip(words.each())`。规则：`x.f(…)` 在 x 的类型所在的模块、当前模块和根模块里都找不到 `f`（也不是内置函数）时，会去 import 的模块里找“扩展方法”，也就是第一个参数是带 `Iter` / `Next` 约束的类型参数、或者是列表 `[T]` 的 pub 泛型函数。两个模块都有时报错，请写成 `模块.f(x, …)`。自己在根模块里定义的同名函数优先（比如 `examples/closure.lark` 自己的 `map`）。见 `examples/chain.lark`。
  - 约束 `Iter[T]`：`[I: Iter[T], T]` 表示 I 是元素为 T 的列表、迭代器或能借用遍历的类型。推断时先确定 I，再由它推出 T，所以闭包参数不用写类型。不满足时报“int 不满足 Iter”。
  - 约束 `Next[T]`：和 `Iter[T]` 一样，只是只接受有 `next` 的迭代器。适配器收迭代器的那个重载用它；`zip`、`chain` 的第二个来源给了列表时报“[int] 不满足 Next：…列表可以先用 iter.each(xs) 包成迭代器”，而不是在库里面报错。
  - `next` 是不带模块前缀的协议名：库里的适配器调用 `next(&m.src)` 时，能找到来源（包括你自己程序里的迭代器）的 `next`。

## 所有权与内存

### 所有权规则

lark0 和 lark1 都会检查：

- 非可复制类型（结构体、枚举、列表）赋值或传给 `take` 参数时会被移走；移走后再使用会报错。
- 只读借用（普通参数、`for` 循环变量、`match` 绑定）不能被移走，也不能赋值或以 `&` 传出。“引用不能存储”就是由这条规则保证的。
- 不能从字段或列表元素里移出值，需要时请用 `.copy()`、`pop`、`replace` 或 `match take`。
- 循环里可以移走循环外的变量，但必须在本轮结束前（以及每个 `continue` 之前）重新赋值，例如 `lhs = Binary(op, lhs, rhs)`。
- `&x` 传入时，`x` 不能出现在同一调用的其它参数里；被移走的变量也一样。
- `for x in xs` 和 `match xs` 期间，`xs` 被冻结，不能修改。
- 一个分支里移走的变量，在 `if` / `match` 之后视为已移走；`return` 所在的分支不计入。

### 生成代码的内存策略

- 值离开作用域时，调用生成的 `lk_drop_*`；`return`、`break`、`continue` 之前也会释放沿途作用域里的值。
- 移走 = 按位复制后把原变量清零（`LK_MOVE`）。析构函数遇到零值什么都不做，所以“可能已被移走”的变量不需要运行时标记。
- 结构体按值存放，列表是 `{data, len, cap}`。枚举、`T?` 和 `T!` 也按值存放：枚举是 `{ tag, union }`（tag 从 1 开始，0 表示已移走），`T?` 是 `{ some, v }`，`T!` 是 `{ set, ok, val, err }`（所以函数返回 `T!` 不用分配内存）。只有沿“按值包含”关系（结构体字段、元组元素、变体字段、`T?` 的值、`T!` 的两边）包含了自己的枚举、`T?` 和 `T!` 放在堆上，如 `enum Ex { Add(Ex, Ex) }`、`type Node { next: Node? }` 里的 `Node?`；经过列表等包含自己不算。见 `design/enum-by-value.md` 和 `examples/enumval.lark`。

### 和设计文档不同的地方

- **`str` 可以隐式复制**：它是不可变的、运行时引用计数，复制只是计数加一。这样写编译器时不用到处写 `.copy()`。
- **`match` 默认借用**；要拆开并取得字段的所有权，必须写 `match take`。
- **用 UFCS 调用时自动加 `&`**：`xs.push(1)` 等价于 `push(&xs, 1)`。
