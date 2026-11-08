# Lark 的可靠性：核心演算和要证的定理

（2026-11 草稿。第一步：把编译器实际执行的规则整理成一个小演算，写清楚要证什么、证明依赖代码生成的哪些约定。
下一步是在 Lean 4 里写出来、证明，见最后一节。）

规则以代码为准：类型检查在 `compiler/check.lark`，所有权检查在 `compiler/own.lark`（下面写成 `own_expr` 这样的函数名），
跳出时的释放在 `compiler/cg_expr.lark` 的 `drop_jump`。DESIGN.md 第 6、7、8、12、15 节是给人看的版本。

## 1 要证什么

**定理（类型安全 + 内存安全）**：程序通过了类型检查和所有权检查，没有用 `extern "c"`，编译时没有加 `-DLK_UNCHECKED`，那么它运行时
只有这几种结局：正常结束、`panic` / `exit`、一直运行下去（死循环、死锁）、栈溢出。并且运行的每一步都满足：

1. **不读空位**：读到的变量、字段、元素都有值（不是被移走后留下的空位）。
2. **每个值恰好释放一次**：拥有的值离开作用域、被覆盖、或者所在的容器被释放时释放；不会释放两次，不会漏掉（不算引用计数成环）。
3. **借用期间不变**：只读借用（普通参数、借用 `match` 绑定的名字、`for` 的循环变量）指向的值，在借用期间不会被修改、移走或释放。
4. **排他**：`inout` 借用期间，同一个值不会经由别的路径被读或写。

加上并发（第 6 节）以后再加一条：

5. **没有数据竞争**：两个任务不会同时访问同一个值，除非两边都只读（`shared`），或者都在同一个 `Mutex` 的 `lock` 块里。

不在保证之内：`extern "c"` 调用的 C 代码、`-DLK_UNCHECKED`（溢出会回绕）、死锁、栈溢出、`os.shell` 之类调用的外部程序。
也不证编译器本身（生成的 C 是否忠实实现这些规则）：第 7 节列出证明依赖的代码生成约定，用差分测试检查。

## 2 核心演算 Lark-core

只留下和所有权有关的部分。泛型、接口、`dyn`、模块和可见性、重载、协议函数、常量都在类型检查时消掉，或者对所有权没有影响，先不放进来。

```
类型   T ::= int | bool | str | (T, …) | S | E | [T] | T? | fn(T…) -> T | Fn(T…) -> T
           | shared T | Mutex[T] | Chan[T]
           S 是结构体（字段 f: T），E 是枚举（变体 V(T…)）
可复制  int、bool、u8 这类平凡类型和 str（str 带引用计数，复制是计数加一，修改前写时复制）
位置   p ::= x | p.f | p[e]                     （根变量 root(p) = x）
模式   参数 m ::= read | inout | take
表达式 e ::= 字面量 | p | e op e | f(a, …) | S(f: e, …) | V(e, …) | (e, …) | [e, …]
           | if e { b } else { b } | match e { pat => e, … } | match take e { V(x, …) => e, … }
           | { b } | |x, …| e | return e? | break L? | continue L? | e?
           | scope { b } | spawn(f, e) | lock p as x { b }
实参   a ::= e | &p
语句   s ::= x = e | p = e | p op= e | e | for e { b } | for x in e { b } | for i in e..e { b }
           | defer { b } | L: for …
块     b ::= s; …; e?
```

`for x in v`（借用遍历）、自定义迭代器（`next(inout it) -> T?`）、`select`、`Chan` 的 `send` / `recv` 在第 6 节和第 8 节里补。

## 3 运行时的值和内存

- **存储**：每个变量一个槽，值是树（结构体、枚举、元组、列表是嵌套的值）。只有 `str`、`shared`、`Fn`、`Mutex`、`Chan` 是指向堆上
  共享对象的指针，带引用计数。除了这几种，值之间没有共享，也没有指向别的槽的指针。
- **空位 ⊥**：移走一个变量就把它的槽设成 ⊥（实现里是 `LK_MOVE`：按位复制后清零，释放全零的值什么也不做）。
- **借用**是一条路径 `root.f[i]…`（实现里是指针），只在一次调用、一个 `match` 或一个 `for` 期间存在，不能存进变量或值里
  （“借用不能存储”）：这是整个证明最省力的地方，不需要生命周期。
- **闭包**：`fn` 闭包的环境是一组指向捕获变量的只读借用，只活在一次调用期间；`Fn` 闭包创建时把捕获的变量**复制**进堆上的环境，
  之后和外面没有关系。

## 4 所有权规则

所有权检查是一个按程序顺序走一遍的抽象解释。状态 `S = (live, moved)`：`live = false` 表示这里不可达（`return`、`break` 之后），
`moved` 是可能已被移走的变量集合（**过近似**：任何一条路径上被移走就算）。环境 `O` 记着：

- `frozen`：正被借用的 `match`、`for`、`lock` 冻结的根变量；
- `pinned`：前面的 `defer` 用到的变量；
- `clo_base`：在闭包里时，编号比它小的是捕获的外层变量（只读）；
- 每层循环的 `break` / `continue` 处的状态（带标签的跳出先记在 `far` 里，到目标循环收尾时并进去）。

每个表达式按一种**求值模式**检查：`owning`（拿走值）、`reading`（借来看）、`discard`（结果丢掉）。判断写成
`O ⊢ e : 模式, S ⇒ S'`。

### 4.1 变量和位置（`own_expr`）

| 编号 | 规则 | 代码 |
|---|---|---|
| R1 | 读 `x`：`x ∉ moved` | `EVar`：“值已经被移走” |
| R2 | 以 `owning` 用不可复制的 `x`：`x` 是自己拥有的（不是参数、`inout`、借用的绑定），不在闭包的捕获里，`x ∉ frozen`，`x ∉ pinned`；之后 `moved ∪= {x}` | `EVar` |
| R3 | 不能从位置里移出：以 `owning` 用不可复制的 `p.f`、`p[i]` 是错误（重载的下标除外，它返回新值） | `EField`、`EIndex` |
| R4 | 元组、列表、构造、`take` 参数、`return`、赋值的右边按 `owning` 检查；运算的两边、条件、下标、插值按 `reading` | 各分支 |
| R5 | `reading` 一个不可复制类型的 `if`、`match`、块：分支按 `owning` 检查（分支的值是新的，不是指向别处的借用） | `arm_mode` |

### 4.2 调用（`own_call`）

| 编号 | 规则 |
|---|---|
| R6 | `&p` 的根 `r`：`p` 是位置，不经过 `shared`，`r` 不是只读的、不是捕获的、`r ∉ frozen`；模块外不能经过有私有字段的结构体的字段（`field_guard`） |
| R7 | **排他**：`&p` 的根 `r` 不能出现在同一次调用的别的实参里，除非那个实参是平凡类型、不是位置的新值（调用结果、构造），或者是按 `take` 传的 `str`（会先复制）。按只读捕获了 `r` 的闭包也算出现（`aliases`） |
| R8 | 一个实参里移走的变量（直接按 `take` 传的，或者实参里的块、`if`、`match` 移走的）不能出现在别的实参里 |
| R9 | 实参按书写顺序检查（和生成的代码的求值顺序一致）；返回 `never` 的调用之后不可达 |

### 4.3 分支、循环、跳出

| 编号 | 规则 |
|---|---|
| R10 | `if` / `match` 之后的状态是各分支状态的并（`union_st`）：任何一个分支里移走的，之后都算移走；不可达的分支不参与 |
| R11 | 借用的 `match e`、`for x in e`：`root(e)` 在分支里、循环体里冻结；`match take e` 拿走 `e`，不冻结 |
| R12 | 循环：本轮结束时、每个 `continue` 处，循环外声明的变量不能比进循环时多移走（必须在本轮里重新赋值，`loop_check`） |
| R13 | 循环之后的状态 = 进循环时 ∪ 本轮结束时 ∪ 各个 `break` 处（`loop_finish`）；`break L` / `continue L` 记到标签 L 的那层 |
| R14 | `return` 拿走返回值，之后不可达 |
| R15 | `for 条件 { … }` 的条件每轮都算，属于这个循环（2026-11 修过：类型检查原来把它算在外层，`break 外层` 只跳出一层） |

### 4.4 赋值

| 编号 | 规则 |
|---|---|
| R16 | `x = e`：先按 `owning` 检查 `e`；`x` 不是只读的、不是捕获的、`x ∉ frozen`；之后 `moved -= {x}`（重新赋值让 x 又有了值） |
| R17 | `p = e`（`p` 是字段或元素）：根 `r` 同 R6 的条件，且 `r ∉ moved`（不能往空位里写一部分） |

### 4.5 闭包、defer、并发

| 编号 | 规则 |
|---|---|
| R18 | 闭包体单独检查（可能调用多次，也可能一次都不调用），不改变外面的状态；体里捕获的变量只读，不能移走（R2 的 `clo_base`） |
| R19 | 闭包里不能写 `return`、`break`、`continue`、`?`、`defer`、`scope`、`lock`（check.lark） |
| R20 | `Fn` 闭包不能捕获 `fn` 参数（它是借来的，可能活得没有闭包久），也不能捕获有自定义析构的值 |
| R21 | `defer { b }`：`b` 用到的外面的变量钉住（`pinned`）到块结束，期间不能移走（可以重新赋值，defer 看到的是离开时的值）；`b` 按现在的状态检查一遍，不改变外面的状态。defer 里不能 `return`、`?`，循环不能带标签 |
| R22 | `spawn(f, x)` 只能直接写在 `scope` 里；`f` 是恰好一个 `take` 参数的普通函数（不是闭包），`x` 按 `owning` 检查 |
| R23 | `lock p as x { b }`：`p` 是位置，`root(p)` 在块里冻结；`x` 相当于 `inout` 参数（能改、能 `&x` 传下去，不能移走） |
| R24 | `shared` 的内容只读（不能经由它赋值或 `&` 传递），也不能装 `Mutex`、`Chan`（经由它们能修改） |

## 5 证明的思路

标准的“进展 + 保持”，状态里带一个**所有权不变量** `I(σ, S, O)`，把检查器的抽象状态和真实的存储 `σ` 对应起来：

1. 不在 `moved` 里的、还在作用域里的变量，在 `σ` 里都有值（不是 ⊥）。这就是第 1 节的第 1 条。
2. 当前所有活着的借用（调用栈上每一层的只读参数、`inout` 参数、`match` 绑定、`for` 变量）指向的路径都有值；
   只读借用的路径的根要么在某一层的 `frozen` 里，要么是调用者传进来的只读参数（被调用的函数改不到它）。
3. `inout` 借用的路径和其它活着的借用不重叠。

要证的引理：

- **语法上的别名就是全部别名**：除了 `str`、`shared`、`Fn`、`Mutex`、`Chan` 的共享对象，两条路径指向同一块内存当且仅当一条是另一条的前缀。
  这是值语义加“借用不能存储”给的，也是为什么 R7、R11 只要看根变量就够。
- **冻结**：`root ∈ frozen` 时，所有能修改它的写法（赋值、`&` 传递、移走）都被 R2、R6、R16、R17 拦住；没有全局可变变量，被调用的函数只能经由
  参数修改，而参数又被 R7 管着。
- **共享对象**：`str` 写时复制（计数不是 1 时先复制再改），所以经由共享的 `str` 看不到修改；`shared` 只读；`Fn` 的环境只读；
  `Mutex` 的内容只在 `lock` 块里经由 `x` 访问，同一时刻只有一个 `lock` 块拿着它。
- **合并是过近似**：`union_st` 只会让 `moved` 变大，所以对每条实际执行的路径都成立（单调性）。
- **跳出**：`break` / `continue` / `return` / `?` 前，`drop_jump` 按从里到外的顺序释放沿途的值、执行 defer、解锁；R12 保证 `continue` 回到循环开头时
  循环外的变量都有值。

## 6 并发

模型：每个任务一个调用栈，共享一个存储。`spawn(f, x)` 把 `x` 从当前任务的存储移进新任务；`scope` 块结束前（以及从块里跳出去之前）等它
spawn 的任务都结束。任务之间只有三种东西是共享的：`shared`（只读）、`Mutex`（只能在 `lock` 块里访问）、`Chan`（`send` 移入，`recv` 移出）。
`spawn` 的函数不是闭包、只有一个 `take` 参数，所以新任务拿不到当前任务的任何借用：数据竞争自由归结为上面三种共享对象各自的规则，
加上引用计数在有任务时用原子操作（运行时的 `lk_mt`，属于实现，不在模型里）。

## 7 证明依赖的代码生成约定

证明讲的是语言的规则；下面这些是生成的 C 必须做到的，证明里当作公理，用测试检查：

| 编号 | 约定 | 在哪里 |
|---|---|---|
| A1 | 实参、构造的字段按书写顺序求值 | `arg_slots`、`ctor_vals` |
| A2 | 移走的变量清零，释放全零的值什么也不做 | `LK_MOVE`、各个 `lk_drop_*` |
| A3 | 临时值（调用结果、借用 `match` 的被匹配值）活到语句或 `match` 结束 | cg_expr |
| A4 | 跳出时从里到外：释放每层的值、执行这层的 defer（倒序）、解锁 `lock`；跳出 `scope` 时最后等任务结束 | `drop_jump` |
| A5 | `str` 修改前检查计数，不是 1 时先复制 | `lk_str_append_raw` |
| A6 | 有任务在运行时引用计数用原子操作；没有时用普通加减（spawn 在任务能运行之前就把计数切过去） | `lk_mt`、`lk_rc_inc` |

## 8 整理规则时发现的问题

1. **DESIGN.md 和实现对不上（已改文档）**：第 15 节说 scope 和 lock 块里不能 `return`、`?`、`break` / `continue` 到块外，
   实际上可以（`check_scope`、`check_lock` 的注释，`drop_jump` 先释放、解锁，最后等任务）。DESIGN.md 已经改成和实现一致。
2. **漏洞（已修，2026-11）：实参里间接移走的变量**。R8 原来只看直接按 `take` 传的变量。`f(&v, { v })`、`f(&v, if c { v } else { w })` 这样的写法里，
   第二个实参是按 `reading` 检查的块或 `if`，R5 让它的分支按 `owning` 检查，于是 `v` 在这次调用里被移走，同时 `&v` 又借给了被调用的函数，
   被调用的函数拿到的是已经清零的 `v`（按 A1、A2，内存上不出错，但写进去的东西白写，调用之后 `v` 算移走）。
   现在 `own_call` 在检查完每个实参后，看这个实参新移走了哪些变量，它们不能出现在别的实参里（也就不能是 `&` 的根）。出错测试 `tests/err1/arg_moved`。
3. **偏保守（不影响可靠性）**：R7 和 R11 只看根变量，所以 `f(&a.x, &a.y)`（两个不重叠的字段）、`for x in a.items { a.n += 1 }` 都被拒绝。
   要放宽的话，证明里的“语法别名”引理要改成按路径前缀判断。
4. **`str` 是可复制类型**：证明里 `str` 要按带计数的共享对象建模，靠 A5 写时复制保证第 1 节的第 3 条；这是唯一一个“可复制但不是平凡值”的类型。
5. **对拍发现模型比实现保守（已改 Exit.lean，2026-11）**：Exit.lean 的检查离开 `decl x` 的作用域时，各个出口记的“可能没有值”里还留着 x，
   所以循环里声明、又在本轮里移走的局部变量（`for { v0 = [1]; v1 = v0 }`）被当成“在循环里被移走、本轮结束前没有重新赋值”。
   own.lark 接受这样的程序，这是对的：v0 每轮都是新的，本轮结束时已经释放。改成离开作用域时把 x 从记录里去掉（`Out.hide`），证明跟着改。

## 9 Lean 4 的进度（`formal/`，在里面 `lake build`）

| 文件 | 内容 | 定理 | 状态 |
|---|---|---|---|
| `Lark/Core.lean` | 变量、移走、借来看、分支、赋值（R1、R2、R10、R16） | `no_use_after_move` | 证完（2026-11） |
| `Lark/Loop.lean` | 加上 `loop`、`break`、`continue`，语义带燃料（R12、R13） | `loop_never_stuck` | 证完（2026-11） |
| `Lark/Call.lean` | 调用的三种参数模式：按指针（生成的 C）和按值复制进出（语言的意思）两套语义；排他性和只读参数不能赋值（R6、R7、R8） | `call_agree`：通过检查时两套结果一样；`f(&v, v)` 不检查时真的不一样 | 证完（2026-11） |
| `Lark/Drop.lean` | 堆上的盒子、赋值时释放旧值、借用时冻结根变量、结束时释放所有变量（R2、R11、R16，A2、A4） | `drop_exactly_once`：不读释放了的盒子、不重复释放、结束时堆是空的；借用期间重新赋值不检查时真的会读到释放了的值 | 证完（2026-11） |
| `Lark/Task.lean` | 分叉—汇合的并发（scope、spawn 移进去）、shared 只读、Mutex 只能在 lock 里用、新任务不继承锁（第 6 节；Chan 不在模型里） | `race_free`：通过检查的程序没有数据竞争；两个任务都写同一个变量不检查时真的冲突 | 证完（2026-11） |
| `Lark/Chan.lean` | 交错执行的语义：每步挑一个任务走一条指令，recv 在通道空时等待；send 把盒子转进通道、recv 转出来（第 6 节） | `chan_race_free`：任何调度下，任务碰的盒子都属于它自己；send 以后还用原来的变量不检查时真的会碰到别的任务的盒子 | 证完（2026-11） |
| `Lark/Exit.lean` | 嵌套作用域：局部变量和 defer 按登记的倒序处理；正常走完、break、continue、return（? 同 return）离开时逐层释放、执行 defer；defer 钉住变量（R12–R14、R21，A2、A4） | `exit_sound`：不管怎么离开都不出错、defer 读得到值，结束时堆是空的；defer 钉住的变量被移走不检查时真的会读到空位 | 证完（2026-11） |
| `Lark/Clo.lean` | 借来的闭包（按引用读、被调用任意多次）和 Fn 闭包（创建时复制、自己拥有副本、可以活得比原变量久）；闭包体只读捕获的值（R18；R19、R20 在模型里是结构上的） | `clo_sound`：不读空位或释放了的盒子、不重复释放，结束时堆是空的；闭包体移走捕获的值、被调用两次不检查时真的读到空位 | 证完（2026-11） |
| `Lark/Full.lean` | 合并：Exit.lean 的作用域、defer、break / continue / return，加上借用的 for / match（经由借用读、借用期间冻结，R11、R16）、两参数调用（只读、inout、take，排他性 R6–R8）和闭包（借来的闭包、Fn 闭包写成借用加局部变量，R18）；复用 Exit.lean 的存储和引理 | `full_sound`：不管怎么离开都不出错（包括经由借用读）、defer 读得到值，结束时堆是空的；借用期间重新赋值不检查时真的读到释放了的值 | 证完（2026-11） |
| `Lark/Utf8.lean` | 标准库：std/utf8.lark 的 valid_len、code_at、code_points、chars、is_valid、from_code_point（字节串写成 List Nat） | `code_points_valid`：解出的码点都合法，交给 from_code_point 不会 panic；`chars_concat`：切成字符再拼回去是原来的字节；`decode_encode`、`encode_decode`：合法码点和合法 UTF-8 来回转换不变。写这一条时发现原来的解码把 C3 41 解成一个 Á、C0 80 解成 NUL、ED A0 80 解成代理区的码点，已照 Go 改成每个不合法的字节一个 U+FFFD | 证完（2026-11） |
| `Lark/Base64.lean` | 标准库：std/base64.lark 的 encode / decode 和 URL 写法（字母表写成 chr / val，位运算写成算术） | `decode_encode`：decode(encode d) = Ok d；`decode_url_encode_url`：decode_url(encode_url d) = Ok d。顺带证了 encode 的输出过得了 decode 的每一项检查：没有 =、长度、= 的个数、剩下的位是 0；反方向 `decode_canonical`、`decode_url_canonical`：decode 接受的字符串只能是 encode 的输出（URL 写法另外接受补上 = 的），每段数据只有一种写法 | 证完（2026-11） |
| `Lark/Csv.lean` | 标准库：std/csv.lark 的 parse_sep 和 format_sep（引号括起来的字段、""、\r\n、末尾的 \r、空行） | `field_fmt`：写出来的字段读回来不变、停在分隔符或换行上；`parse_format`：分隔符不是 \r \n "、每行至少一列时 parse(format(rows)) = rows（零列的行读回来是一个空字段，和 csv.lark 写的一样） | 证完（2026-11） |
| `Lark/Sort.lean` | 标准库：std/sort.lark 的 sorted（msort_by、merge_by）、lower_bound、upper_bound、binary_search、dedup | `sorted_asc`：从小到大；`sorted_stable`：每个键的元素和原来一样、先后不变（稳定，结果是原来的排列）；`lower_bound_spec`、`upper_bound_spec`、`bounds_eq`：[lower_bound, upper_bound) 正好是等于 x 的下标；`bsearch_some`、`bsearch_none`；`dedup_good`、`dedup_mem`、`dedup_sorted`：相邻不重复、元素不丢不多、排好的列表去重后严格递增 | 证完（2026-11） |
| `Lark/Bytes.lean` | 标准库：std/bytes.lark 的 push_u16/u32_be/le、push_u64_be 和对应的读（int 写成 64 位的 bits，u64 读回时按有符号解） | `rt16be`…`rt32le`：写进去再从同一位置读，得到低 16 / 32 位；`rt64be`：u64 读回原来的 int（负数也一样）；`be16_rd`…`le32_rd`：任意字节读成整数再写回去不变 | 证完（2026-11） |
| `Lark/Json.lean` | 标准库：std/json.lark 的 format 和 parse（quote / read_str、int_str / float_str 和 read_num、数组、对象、512 层的嵌套限制；读写成带燃料的递归） | `rs_quote`：quote 写出来的字符串读回来不变；`parse_format`：`Good 0 j` 时 parse(format(j)) = j。前提：Int 在 64 位里；Float 比较的是文字，float_str 的输出合乎 `FloatText`，parse_float(float_str(x)) = x 是 strtod 的事实、不在 Lean 里；inf / nan 不在内；嵌套不超过 512 层；对象的键和值一样多 | 证完（2026-11） |
| `Lark/Deque.lean` | 标准库：std/deque.lark 的环形缓冲区（buf 写成下标到 Option 的函数，head、n、cap） | `pushBack_ok`、`pushFront_ok`、`popFront_ok`、`popBack_ok`：在“从队头到队尾的列表”上就是列表的对应操作，满了时翻倍不改变内容；`get_ok`、`of_ok`；都保持不变式 WF（n ≤ cap、head < cap、没有空位，所以 iter_at 不会 panic） | 证完（2026-11） |
| `Lark/Heap.lean` | 标准库：std/heap.lark 的 insert（上浮）和 pop_min（下沉），元素写成 Nat，循环写成带燃料的递归 | `insert_heap`、`popMin_heap`：保持堆的性质；`root_le`：取出的是最小值；`insert_cnt`、`popMin_cnt`：每个值出现的次数只差放进 / 取出的那一次；`pop_mono`：连着 pop 不会变小，into_sorted 从小到大 | 证完（2026-11） |
| `Lark/Digest.lean` | 标准库：std/digest.lark 的 crc32（短的逐位算、长的查表）、to_hex / from_hex、equal；SHA-1 / SHA-256 / SHA-512 / HMAC 照标准逐步写，没有另外的规格，靠 tests/unit/digest.lark 的标准测试向量 | `crc32_ok`：查表和逐位算对任何输入一样（`st_lin`：一步对 ^ 线性；`tab_ok`）；`tab_idx`：查表不越界；`fromHex_toHex`；`equal_ok`：true 正好当两个字节串相同 | 证完（2026-11） |
| `Lark/Str.lean` | 标准库：std/str.lark 的 index_from / find、split（一般的路和 sep 只有一个字节的逐字节路）、replace_all、count、cut；字符串写成字节列表 | `find_ok`：找到的是第一次出现、找不到时确实没有；`split_join_ok`、`split_free_ok`：用 sep 接回去是原串，每段不含 sep；`split1_eq`：两条路切得一样；`replaceAll_ok`、`count_ok`、`cut_ok`、`cut_none` | 证完（2026-11） |
| `Lark/Fmt.lean` | 标准库：std/fmt.lark 的 radix / hex / bin（% 和 / 向 0 截断，负数累计防溢出）、thousands、fixed(int, digits)；width、对齐、table、byte_size 是排版，float 的 fixed 依赖 round，没有证 | `loop_nat`：负数累计的循环和对 |n| 用 Nat 一样；`radix_ok`：每位 < base、首位不是 0、读回是 |n|、负号正好在 n < 0；`thou_strip`：去掉逗号是原数字；`fixed_ok`：小数点后正好 digits 位，补 0 不改值 | 证完（2026-11） |
| `Lark/Map.lean` | 标准库：std/map.lark 的开放寻址哈希表（slots 写成下标到 Option 的函数，起点 hash ^ seed 打散写成任意函数 hf，& (n-1) 写成 % n），map_slot、insert（含扩容）、map_rehash、get、remove、retain；remove 里“后面的挪开再放回”写成 eraseIdx | `slot_present` / `slot_absent`：有键时停在它的槽，没有时停在空槽且一定会停；`rh_eq`：Lark 的重建和一个个放进去一样；`insert_ok`、`get_ok`、`remove_ok`、`retain_ok`：都保持不变式，按键找的结果和“按插入顺序的键值对列表”一样，插入顺序保持 | 证完（2026-11） |
| `Lark/Varint.lean` | 先证明再写库：std/bytes.lark 的 push_uvarint / uvarint（无符号 LEB128，照 Go 的 binary.Uvarint；Lean 的 none 是 Lark 的 Err） | `enc_ok`：每字节 < 256、最多 10 个；`uvarint_enc`：写出来再读回去不变；`uvarint_safe`：任意输入读成功时结果 < 2^64、读 1..10 个字节 | 证完（2026-11） |
| `Lark/TreeMap.lean` | 先证明再写库：std/treemap.lark 的 AVL 树（make_node / rebalance / insert_node / find_node / split_min / remove_node / at_node 对应 Lean 的 mk / bal / ins / get / sm / del / at?；键是 Int，代码只用 `<`） | `insert_ok` / `remove_ok`：保持不变式（AVL 平衡、存的高度和大小对、中序严格递增），中序变成列表上的插入 / 删除，之后 get k 是新值 / None、别的键不变；`get_ok`：get 就是在中序里找；`at_ok`：at i 是中序第 i 项；`ins_avl` / `del_avl`：高度变化不超过 1 | 证完（2026-11） |
| `Lark/Url.lean` | 先证明再写库：std/url.lark 的查询串（escape / unesc / splitOn / cutEq / parseQ 对应 escape_query / unescape_range / 按 & 切开 / 在第一个 = 处分开 / parse_query；Lean 的 none 是 Lark 的 Err） | `unesc_esc`：任意字节串 escape 再 unescape 回到原样；`esc_safe` / `esc_not`：escape 的结果只有不用编码的字节和 % +，没有 & = ;；`parse_format`：任意键值对列表 format 再 parse 回到原样，顺序不变 | 证完（2026-11） |
| `Lark/Semver.lean` | 先证明再写库：std/semver.lark（cmp / cmp_pre / cmp_id / cmp_bytes 对应 cmpV / cmpPre / cmpId / cmpList cmpN；parse_num / parse_ids 对应 parseNum / parseId、parseBuilds；数字的模型是不限大小的 Nat，代码里超过 18 位出错，预发布的数字标识符按“先比长度再逐字节比”，没有前导零时和按数字比一样） | `lawV`：比较是全序（交换两边结果反过来、相等当且仅当除了构建信息都一样、自反、小于可以传递）；`parse_format`：合法的版本写出来再解析回到原样 | 证完（2026-11） |
| `Lark/Tls.lean` | 先证明再写：apps/ltls 阶段 1 的加密原语（实验性）。ChaCha20、Poly1305、ChaCha20-Poly1305、X25519 照 RFC 8439 / 7748 写成规格，用 `#guard` 对 RFC 的测试向量；证明了 seal 再 open 回到明文、open 成功时输入正好是 seal 的结果、交给 Poly1305 的数据能唯一拆回 (aad, 密文)、HKDF-Expand-Label 的 info 能唯一拆回 (长度, label, context)、HKDF-Expand 的输出长度和块计数、掩码选择和交换、阶梯的两种交换写法一样、求逆的平方-乘序列是 a^(p-2)、私钥截位以后是 8 的倍数且在 [2^254, 2^255)。没证明的：分段乘法和进位与规格一致（靠测试向量）、a^(p-2) 是逆（要 p 是素数）、常数时间 |
| `Lark/Tls13.lean` | 先证明再写：apps/ltls 阶段 2（实验性）。带长度前缀的格式（记录、握手消息）写出来再读回来不变，读成功时输入正好是 写出来的 ++ 剩下的；记录长度超过 2^14 + 256 拒绝；内层明文能拆回 (内容, 类型)，全是 0 的拒绝；序号小于 2^64 时 nonce 不重复；加密的记录解得开；客户端状态机走到 connected 时事件一定以完整的握手开头（Finished 没核对就不收发应用数据，不能跳过 Certificate / CertificateVerify）。SHA-256、HMAC 和密钥计算用 `#guard` 逐个对 RFC 8448 第 3 节的值。没覆盖的：AES-GCM（RFC 8448 用它，所以加密以后的记录没对）、证书和签名的验证 |
| `Lark/Hello.lean` | 先证明再写：apps/ltls 阶段 3（实验性）。ClientHello、ServerHello 和扩展列表写出来再读回来不变；读成功时输入正好是用读出来的字段写出来的。用 RFC 8448 的 ClientHello（9 个扩展）和 ServerHello 检查：解析以后再写回去逐字节一样。没覆盖：各个扩展内容自己的格式 |
| `Lark/Session.lean` | 先证明再写：apps/ltls 阶段 3（实验性）。信道原样送到、两边共享秘密一样时，客户端状态机走到 connected、服务器接受客户端的 Finished、两边的应用流量密钥和 IV 一样、应用数据两个方向都解得开；CertificateVerify 验证不过或服务器的 Finished 对不上时走不到 connected。CertificateVerify 是 Ed25519 签名（0x0807），按格式写的签名验证得过客户端就认（cvOk_cvMsg）；公钥现在是钉住的，从证书里取是阶段 4b；X25519 两边一样、Ed25519 签了再验通过靠测试；改字节就核对不过要 HMAC 抗碰撞、Ed25519 不可伪造，没有证明 |
| `Lark/Ed25519.lean` | 先证明再写：apps/ltls 阶段 4a（实验性）。SHA-512 和 Ed25519 照 RFC 8032 第 5.1 节写成规格，用 `#guard` 对了第 7.1 节的 TEST 1、2、3、SHA(abc)；证明了签名不是 64 字节或 S ≥ L 时验证不过、y ≥ p 时解码失败、私钥截位以后是 8 的倍数且在 [2^254, 2^255)、CertificateVerify 签的内容能唯一拆回消息摘要。没证明：签了再验一定通过（要群律）、常数时间 |
| `Lark/Der.lean` | 先证明再写：apps/ltls 阶段 4b 的第一步（实验性）。DER 的长度只认最短的写法，读出来的元素写回去和输入一样、标准写法一定读得回来（`decLen_some`、`decLen_encLen`、`parseTlv_some`、`parseTlv_tlv`）；Ed25519 公钥（SubjectPublicKeyInfo，RFC 8410）和证书的最外层（tbsCertificate、算法 Ed25519、64 字节签名）同样双向证明；用 `#guard` 对了 RFC 8410 第 10 节的公钥和证书，证书的签名验证通过。没做：名字、有效期、扩展、证书链 |
| `Lark/Lsp.lean` | 先证明再写：apps/llsp 阶段 1。分帧：消息写出来再读回来不变（`parse_frame`），读成功时内容和剩下的正好是输入的后缀（`parse_some`），Content-Length 只能有一个、最长 64 MiB。位置：文档按 UTF-8 字符切开、`\r\n` 并成一个，列按 UTF-16 或 UTF-8 数；任何位置换成的偏移都在字符边界上、不超过文档长度（`off_boundary`），边界上的偏移和文档里真有的位置来回换不变（`pos_off`、`off_pos`）。修改：长度对（`edit_len`、`change_len`）。没证：不合法的 UTF-8 客户端怎么数、JSON-RPC 的内容 |
| `Lark/LspRpc.lean` | 先证明再写：apps/llsp 阶段 2。JSON-RPC 的请求和回复、生命周期（initialize → shutdown → exit）的状态机。没退出时每个请求正好得到一条回复、id 对得上（`step_req`），通知从不得到回复（`note_quiet`），一串消息处理下来回复的 id 正好是 exit 之前各个请求的 id、按顺序（`run_replies`）；initialize 之前别的请求不处理（`uninit_guard`），shutdown 以后不会再回到运行中（`shutdown_stays`），exit 的退出码（`exit_code`），退出以后什么都不做（`exited_stuck`）；客户端发来的回复丢掉，不是请求的 JSON 回复 -32600，读不出来的 JSON 回复 -32700。没证：JSON 本身的解析、各个功能的内容 |
| `Lark/LspDoc.lean` | 先证明再写：apps/llsp 阶段 3。打开的文档（didOpen / didChange / didClose）：打开以后读到的就是打开时的内容、关掉以后读不到（`open_get`、`close_get`），版本更大时内容是按顺序作用所有修改的结果（`change_get`），版本没变大或者没打开时什么都不变（`change_stale`、`change_unknown`），版本不会变小（`change_mono`），一串修改拆成两次通知发结果一样（`change_split`），一个文档只被它自己的通知改变（`step_other`、`run_other`）。没证：从 JSON 里读出 uri、版本和修改 |
| `Lark/LspDiag.lean` | 先证明再写：apps/llsp 阶段 4。诊断：编译器的行列（从 1 数、列是字节、只有 \n 换行）先换成字节偏移，再用阶段 1 的 posOf 换成 LSP 的位置。偏移 → 编译器的行列 → 偏移不变（`c_round`），换成的偏移不超过文档长度（`cOff_le`），编译器指着字符开头时编辑器里标在同一个字节上（`dpos_exact`、`diag_round`）；编译器写出的错误行能读回行、列和信息（`parse_fmt`）；发诊断的一定是这次通知的文档、带最新的版本，关掉时清空（`pubs_latest`），不发的通知什么都没改（`pubs_quiet`），每条通知最多发一次（`pubs_len`）。没证：编译器报的错本身对不对、运行编译器 |
| `Lark/LspDef.lean` | 先证明再写：apps/llsp 阶段 5。跳到定义：llsp 自己扫描源文件，不经过编译器。光标下的词包含光标、不超出文档（`word_bounds`），往右已经到头（`word_end`）；行首（可以先写 `pub `）的 `fn` / `type` / `enum` / `const` / `interface` 后面的名字是声明，扫出来的每个声明在它的偏移上正好是这个名字，非空、都是标识符的字节、是完整的词（`decls_word`）；找到的定义满足同样的性质、在某一行的开头之后（`find_word`、`find_line`）。没证：import 的路径怎么对应到文件；方法、枚举的变体、局部变量 |
| `Lark/LspSym.lean` | 先证明再写：apps/llsp 阶段 6。文档大纲：就是阶段 5 扫出来的声明，每个标上种类（fn → Function、type → Struct、enum → Enum、const → Constant、interface → Interface）。大纲去掉种类以后正好是 decls、顺序一样（`symbols_decls`），每一项在它的偏移上正好是这个名字、是完整的词（`symbols_word`），范围在文档里面（`symbols_in`）。没证：大纲只有一层；范围只是名字，不是整个声明 |
| `Lark/LspFmt.lean` | 先证明再写：apps/llsp 阶段 7。格式化：把文档交给现有的 lark-fmt，只换中间不一样的那段（光标不跳）。开头、结尾一样的字节两边确实一样、两段不重叠（`pre_take`、`pre_le`、`suf_ok`、`suf_le`、`pre_suf`），换掉 [a, b) 以后正好是格式化的结果（`fmt_edit`），a、b 在字符边界上时换成 LSP 的位置、再按阶段 1 的 change 作用，结果也正好是它（`fmt_change`）。没证：格式化工具本身；取字符边界 |
| `Lark/LspComp.lean` | 先证明再写：apps/llsp 阶段 8。补全：前缀是光标前面那半个词，候选是本文件的声明和关键字，或者 `模块.` 时 import 进来的文件里 `pub` 的声明。补全的每一项都是候选、以前缀开头，每个以前缀开头的候选都在里面（`complete_iff`），没有重复（`complete_nodup`）；本文件的每一项要么是关键字、要么是真有的声明（`local_sound`），`模块.` 的每一项是那个文件真有的 `pub` 声明（`module_sound`）。没证：import 的路径怎么对应到文件；方法、字段、局部变量、标准库 |
| `Lark/LspSem.lean` | 先证明再写：apps/llsp 阶段 9。语义高亮：一个字节一个字节地走，记着在代码、字符串、注释还是字符字面量里，只在代码里找词。找出的每个词在它的偏移上正好是一串标识符的字节、非空、往右到头（`scan_word`），词按位置排好、互不重叠（`scan_disjoint`）；按 LSP 的规定写成相对前一个的差，位置排好时解回来正好是原来的（`decode_encode`）。没证：每个词是什么种类（看上下文猜的）；字符串里 #{…} 插值的代码不上色 |
| `Lark/VtParse.lean` | 先证明再写：apps/lterm 阶段 1。转义序列的解析器（DEC / ANSI 的状态机，Paul Williams 的图）：任何状态、任何字节都有下一步；CAN / SUB 从任何状态回到 ground、清掉读了一半的序列（`step_cancel`）；ESC 从任何状态重新开始（`step_escape`）；每个字节最多出一个动作（`run_len`）；ground 里的普通文字原样按顺序变成 print（`run_text`）；OSC 字符串里的文字不会变成 print（`run_osc`）。#guard 检查了 CSI 参数、私有标记、省略和封顶的参数、序列里的控制字符、OSC 的两种结束、DCS、SOS。参数里的 : 当成 ;。 |
| `Lark/VtUtf8.lean` | 先证明再写：apps/lterm 阶段 2。UTF-8 的流式解码：字节一个一个喂，没凑齐的字符先存着，坏字节照标准库每次一个、U+FFFD。交出去的字节拼起来再接上存着的正好是喂进去的全部（`settle_join`、`feed_join`）；存着的要么空、要么是合法字符的真前缀、最多 3 个字节（`feed_pend`、`pend_short`）；交出去的每段不空、最多 4 个字节（`feed_ne`）；码点都合法（`decode_valid`）。字符宽度只有 0 / 1 / 2（`width_le`），ASCII 是 1（`width_ascii`），两张区间表排好、不重叠（#guard）。和 Utf8.codePoints 一样只在 #guard 和随机测试里对照；宽度表只收了常用区间。 |
| `Lark/VtScreen.lean` | 先证明再写：apps/lterm 阶段 3。屏幕：R 行 × C 列的格子、光标、自动换行（pend）、滚动区域。任何操作（写字、回车换行、反向换行、退格、制表、光标移动、EL / ED / ECH、ICH / DCH、IL / DL、SU / SD、DECSTBM）以后屏幕都是好的：正好 R 行、每行 C 格、宽字符不会只剩一半、光标在屏幕里、top ≤ bot < R（`step_ok`、`run_ok`、`init_ok`）；每行改完都经过 rowFix（补齐、修补宽字符，`heal_wf`、`heal_len`）；滚动只动区域里的行（`up_outside`、`down_outside`）。#guard 检查了写字、自动换行、滚动、宽字符、擦除、插入删除、滚动区域、CUP。还没有样式、模式、备用屏幕、滚动缓冲、改大小。 |
| `Lark/VtSgr.lean` | 先证明再写：apps/lterm 阶段 4。颜色和样式（SGR，CSI … m）：参数一个一个走，记着是不是在读 38 / 48 的扩展色。任何参数序列以后颜色都在范围里，不合法的颜色不写进去（`one_ok`、`step_ok`、`run_ok`、`apply_ok`）；参数分两段走结果一样（`run_append`）；CSI m 和 CSI 0 m 都复位（`apply_nil`、`apply_zero`）。#guard 检查了粗体、红字、256 色、真彩色、超出范围、写坏的扩展色、22、亮色、默认色。冒号的子参数没做。 |
| `Lark/VtMode.lean` | 先证明再写：apps/lterm 阶段 5。模式（DECSET / DECRST）、备用屏幕、保存光标：屏幕外面包一层，记着自动换行（?7）、显示光标（?25）、括号粘贴（?2004），备用屏幕（?47 / ?1047 / ?1049）进去时把主屏幕整个存起来。任何操作以后现在的屏幕和存着的主屏幕都是好的（`step_ok`、`run_ok`、`init_ok`）；进备用屏幕、做任何不切换屏幕的操作、再出来，主屏幕原样回来（`alt_restore`）；自动换行关掉时写字不换行（`nowrap_y`）。#guard 检查了关掉自动换行、备用屏幕进出和重复进出、保存恢复光标、不认识的模式。原点模式、插入模式、鼠标模式没做。 |
| `Lark/VtSb.lean` | 先证明再写：apps/lterm 阶段 6。滚动缓冲和改大小：整个屏幕往上滚时滚出去的行按顺序放进滚动缓冲，缓冲 ++ 屏幕这段历史一行不丢、顺序不变，只在最后添了空行（`up_keep`、`hist_up`）；缓冲最多 cap 行，留下最新的一段，没满时不丢（`keep_len`、`keep_suffix`、`keep_all`）；改成任何大小以后屏幕都是好的（`resize_ok`、`resizeT_ok`），光标那一行还在光标所在的地方（`resize_cur`），行数变少时挪走的是顶上的行（`resize_lost`）。#guard 检查了滚出去的行、缓冲满了丢最旧的、改小改大、宽字符被切开。改列数时不重新折行（reflow）。 |
| `Lark/VtDraw.lean` | 先证明再写：apps/lterm 阶段 7。把仿真出来的屏幕画到真的终端上，只画变了的地方：每一行和上一次画出去的比，一样的不画，不一样的从第一个不一样的格子开始画剩下的。旧画面执行这些命令正好得到新画面（`applyRow_ok`、`draw_ok`）；从更早的地方开始画也对（`applyRow_le`，宽字符要退回左半）；画面没变时什么都不画（`diff_same`）；一行画出去的格子不比这一行多（`cost_le`）。改大小时整个重画。 |
| `Lark/VtView.lean` | 先证明再写：apps/lterm 阶段 8。翻看滚动缓冲：看到的是 滚动缓冲 ++ 屏幕 里的一个窗口。窗口总是正好 R 行（`view_len`）；不翻时就是现在的屏幕（`view_zero`）；窗口是历史里连续的一段（`view_sub`）；翻到最上面从缓冲的第一行开始（`view_top`）；上翻不超过顶（`up_le`），没碰到顶时上翻再下翻回到原处（`up_down`），下翻够了回到屏幕（`down_zero`）。翻看时有新输出窗口不跟着内容走、搜索没做。 |
| `Lark/VtReply.lean` | 先证明再写：apps/lterm 阶段 9。回答终端查询（DSR 光标位置、状态、DA1、DA2）：数字写成十进制再按解析器的办法读回来还是原来的数（`dec_acc`）；回答光标位置的字节交给阶段 1 的解析器，正好解析成一个 CSI [行, 列] R（`dsr_parse`，用到 `run_digs`、`run_sep`、`run_fin`）。别的回答是固定的字节串；DECCKM 只记着交给外面的终端。 |
| `Lark/VtCharset.lean` | 先证明再写：apps/lterm 阶段 10。画框线的字符集（DEC Special Graphics：ESC ( 0 / ESC ) 0、SO / SI）：0x5F–0x7E 以外的字符不变（`map_out`），用 ASCII 时什么都不变（`map_ascii`）；换出来的字符都占一格（`gfx_width`、`map_width`，用阶段 2 的 width）；不同的字母换成不同的字符（`gfx_inj`）；ESC ( B + SI 或者复位以后一定回到 ASCII（`reset_ascii`）；设置 G0 不影响 G1（`designate_other`）。别的字符集、SS2 / SS3 没做。 |
| `Lark/VtRegion.lean` | 先证明再写：apps/lterm 阶段 11。滚动区域从屏幕顶上开始（[0, b]，codex 这类不用备用屏幕、下面留一块界面的程序）时，往上滚出去的行也进滚动缓冲：滚出去的 n 行接上滚动以后区域里的 b + 1 行，正好是滚动以前的区域接上 n 个空行（`region_keep`、`region_hist`）；区域下面的行不动（`region_below`）；滚超过 b + 1 行和滚 b + 1 行一样（`up_clamp`），所以最多存 b + 1 行。区域不从顶上开始时还是不存（和 xterm 一样）。 |
| `Lark/VtSel.lean` | 先证明再写：apps/lterm 阶段 12。鼠标选中和复制：从哪头往哪头拖都一样，选中的正好是两个位置之间的格子（`mk_symm`、`mk_in`）；去掉行尾空白以后原来的行就是它接上空白、它自己不以空白结尾、行尾多几个空白不影响（`trim_split`、`trim_end`、`trim_pad`）；复制的文字按换行切开正好是每一行选中的部分，一共 最后一行 - 第一行 + 1 行（`split_join`、`copy_lines`）；双击选的词包含点的位置、里面都是词里的字符、两头再往外一格就不是了（`left_*`、`right_*`）。 |
| `Lark/VtMouse.lean` | 先证明再写：apps/lterm 阶段 13。把鼠标交给里面的程序（CSI ? 1000 / 1002 / 1003 / 1006 h）：SGR 格式的报告交给阶段 1 的解析器正好解析成 CSI < [码, 列 + 1, 行 + 1] M / m（`sgr_parse`，用 VtReply 的 `dec_acc`）；按下 / 松开、拖动 / 移动、滚轮的码分别在 0–31、32–63、64 以上，按下时码 % 4 是哪个键、码 / 4 是修饰键（`code_*`）；没打开时不报、按下松开滚轮都报、不按键移动只有 1003 报、按着键拖只有 1002 / 1003 报（`off_quiet`、`press_on`、`motion_*`）；关掉任何一个都不报（`set_off`），别的模式号不动（`set_other`）；老格式正好 6 个字节、都小于 256（`x10_len`）。 |
| `Lark/VmCore.lean` | 先证明再写：apps/lvm 阶段 1。从零写的轻量线程跑在一个小的栈式虚拟机里，按跑了几条指令抢占：一个时间片最多跑 budget 条指令（`slice_le`），因为用完而停下时正好跑了 budget 条（`slice_budget`）；先跑 n 条被抢占、再跑 m 条，和一口气跑 n + m 条结果完全一样——什么时候被换下去都不改变线程算出来的东西（`slice_split`）；时间片是 1 时就是走一步（`slice_one`）。 |
| `Lark/VmSched.lean` | 先证明再写：apps/lvm 阶段 2。M:N 调度：W 个 worker 各有正在跑的线程和先进先出的队列，加上等着的和结束了的；pick、抢占、等待、结束、唤醒、偷别人队列里的，每一步每个线程出现的次数都不变（`step_cnt`），spawn 只给新线程加一次（`spawn_cnt`）；所以从开始走到的任何状态里每个线程最多在一个地方（`reach_inv`），同一个线程不会同时在两个 worker 上跑（`no_double`），活着的线程不会丢（`alive`）；有活要干时调度器总能走一步（`can_move`），闲着的 worker 能偷到（`steal_ok`）；通道收到的正好是发出的那串的开头（`send_inv`、`recv_inv`、`got_prefix`）。 |
| `Lark/VmCall.lean` | 先证明再写：apps/lvm 阶段 3。函数调用：call 把返回的地方和调用前的局部变量压成一帧、换一份新的局部变量，ret 原样换回来（`call_saves`、`ret_restores`）；调用深度最多 D 帧，再 call 就出错（`step_fr`、`depth_le`、`slice_depth`）；加了调用以后时间片的性质照样成立，在函数里被抢占也看不见（`slice_le`、`slice_budget`、`slice_split`、`slice_one`）。 |
| `Lark/VmPar.lean` | 先证明再写：apps/lvm 阶段 4。一次偷别人队列的前一半，每个线程出现的次数也不变（`stealN_cnt`），加上原来那几步照样每个线程最多在一个地方、不会同时在两个 worker 上跑（`reach2_inv`、`no_double2`），别人队列不空时总能偷到（`steal_half_ok`）；有界通道：缓冲不超过容量、满了发的线程等着、收的时候补上等着的值，每一步都保持“收到的 ++ 缓冲 = 发出的”（`bsend_inv`、`bwait_inv`、`brecv_inv`、`brefill_inv`、`handoff_inv`、`takeW_inv`、`bprefix`、`bbound`）；每个 worker 一把锁，拿着锁时只去拿编号更大的锁，就不会一圈互相等（`no_deadlock`）。 |
| `Lark/VmFair.lean` | 先证明再写：apps/lvm 阶段 5。拿线程、放回自己队列只改自己那个 worker，不同 worker 上的这两步谁先谁后结果一样，所以正在跑的线程可以放进 worker 自己的锁里、这两步只拿一把锁（`upd_comm`、`setW_comm`、`pick_comm`、`preempt_comm`、`pick_preempt_comm`）；select：同时等好几个通道的线程排进每个通道，被一个叫醒后从所有通道里撤掉，不会被叫醒第二次，别的线程不受影响（`sel_block_cnt`、`sel_block_keep`、`sel_wake_gone`、`sel_wake_keep`、`sel_no_twice`）；公平：队列里排第 k 个的线程，这个 worker 再拿 k + 1 次线程以内一定轮到它，不管中间加进来多少个；被偷也不会往后排（`fair`、`ix_app`、`ix_app_right`）。 |
| `Lark/VmTimer.lean` | 先证明再写：apps/lvm 阶段 6。睡着的线程按到期时间排好，插进去以后还是排好的、插进去的就是原来的加上新的（`ins_sorted`、`ins_mem`）；每次只从头上拿到期了的，拿出来的都到期了、剩下的都没到期、合起来正好是原来的（`due_ok`、`due_rest`、`due_split`），和把所有睡着的都看一遍结果一样；带超时的 select：每次等发一个新编号，编号对得上才叫醒，所以同一次等只会被叫醒一次、上一次留下的旧定时器项叫不醒这一次（`wake_once`、`stale_ignored`、`wblock_fresh`）。 |

对拍（`sh formal/difftest.sh 个数 种子 loop|call`，先 make stage1）：`formal/DiffGen.lean` 随机生成小程序，Lean 的检查和 build/lark1 各判一次。
loop 一套用证过的 `chkL`；call 一套加上两参数调用（只读、inout、take）和借用的 for，用 `chkC`（chkL 加上 Call 的排他性、Drop 的冻结，拼起来没有单独证）。
defer、clo 两套直接用证过的 Exit.lean、Clo.lean 的 `chk`（clo 一套在最后补上 Lark 自动做的释放）。两边都拒绝时还要求 lark1 报的是所有权错误。
2026-11：loop 3000 个、call 300 个全部一致；defer 一开始有 27/3000 个不一致（模型比实现保守，见第 8 节第 5 条），改了 Exit.lean 以后 3000 个全部一致；clo 3000 个全部一致。`make formal` 把四套各跑 500 个。

所有权的八个文件里，检查都写成和 own.lark 同一个算法的可执行函数，末尾用 `decide` 跑几个例子，确认和真实编译器的判断一致。

原来的计划（后面几步照此往下）：

建议的文件和顺序（每一步都能单独 `lake build`）：

1. `Syntax.lean`：第 2 节的类型、表达式、语句。
2. `Typing.lean`：类型规则（去掉泛型以后很直接）。
3. `Ownership.lean`：第 4 节的判断，写成和 own.lark 一样的函数（可执行），再证它满足几条性质（单调、合并是上界）。
4. `Semantics.lean`：带存储和 ⊥ 的小步语义，跳出时的释放按 A4。
5. `Soundness.lean`：不变量 `I`，进展和保持；先证不带闭包和 defer 的子集，再一样一样加。
6. 并发（第 6 节）放在顺序部分证完以后。

需要在本机装 Lean 4（`elan`）。我这边跑不了 Lean，写好的文件要你在本地 `lake build`，把报错贴回来，和现在改编译器的做法一样。
