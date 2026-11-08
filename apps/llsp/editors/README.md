# 在编辑器里用 llsp

llsp 通过 stdin / stdout 和编辑器通信，任何支持 LSP 的编辑器都能用。它现在能做：

- **诊断**：打开或者修改 `.lark` 文件后，用 `lark1` 检查，把错误和警告标在编辑器里；
- **跳到定义**：本文件里的 `fn` / `type` / `enum` / `const` / `interface`，以及 `模块.名字`（会去找 import 的那个文件）；
- **文档大纲**：列出本文件里的声明。
- **格式化**：用 `build/lark-fmt`（`make fmt-tool` 生成）格式化，只换不一样的那段，光标不跳。
- **补全**：本文件的声明、关键字和内置类型；输入 `模块.` 后列出那个文件里 `pub` 的声明。
- **语义高亮**：`textDocument/semanticTokens/full`，按上下文给参数、局部变量、字段、函数、类型、模块上色（编辑器的语法高亮之外再加一层）。

## 语法高亮

高亮不经过 llsp，是编辑器自己按规则给代码上色，规则和 `compiler/lex.lark` 一样：

- `vscode/syntaxes/lark.tmLanguage.json`：VS Code 用的 TextMate 语法，装了扩展就有；
- `nvim/syntax/lark.vim`：Neovim 和 Vim 用的语法文件，复制到 `~/.config/nvim/syntax/lark.vim`（Vim 是 `~/.vim/syntax/lark.vim`）；
- `openidea/lark.toml`：OpenIDEA 的高亮是借 CodeMirror 的 Rust 模式做的近似，见下面第 5 节。

Helix 的高亮要用 tree-sitter 语法，还没写。OpenIDEA 的 tree-sitter 语法编在程序里，加不了新的，所以只能近似。

## 1. 构建

在仓库根目录：

```
make lark-tool
cd apps/llsp && LARK_HOME="$PWD/../.." ../../build/lark build; cd ../..
```

得到 `apps/llsp/build/llsp`。

llsp 运行时需要找到 Lark 的安装目录（里面要有 `build/lark1` 和 `std/`）才能发诊断：

- 设置了环境变量 `LARK_HOME` 时用它；
- 否则从 llsp 所在的目录往上找。所以直接用 `apps/llsp/build/llsp`、不复制到别处时，不设置 `LARK_HOME` 也可以。

找不到时 llsp 照样能跳到定义、列大纲，只是没有诊断，并且在标准错误里提示一句。

下面的例子里，`/path/to/lark` 换成你的仓库路径。

## 2. Neovim（0.11 以上）

把 `nvim/lark.lua` 复制到 `~/.config/nvim/plugin/lark.lua`，然后把文件开头的 `lark_root` 改成你的仓库路径。

打开一个 `.lark` 文件后：

- `:checkhealth vim.lsp` 能看到 llsp 已经连上；
- 有错误时行号旁边会出现标记；
- `gd` 跳到定义（文件里设置了这个快捷键）；
- `gO` 列出文档大纲（Neovim 0.11 默认的快捷键）。

Neovim 会告诉服务器它能用 UTF-8 的列，所以 llsp 和 Neovim 之间的列按字节算。

## 3. Helix

把 `helix/languages.toml` 里的内容加到 `~/.config/helix/languages.toml`，并改掉里面的路径。

- `hx --health lark` 能看到 llsp；
- `gd` 跳到定义，`<space>s` 列出大纲。

## 4. VS Code

`vscode/` 是一个最小的扩展。

```
cd apps/llsp/editors/vscode
npm install
```

然后两种用法：

- **调试运行**：用 VS Code 打开 `apps/llsp/editors/vscode` 这个目录，按 F5，在弹出的窗口里打开 `.lark` 文件；
- **安装**：`npx @vscode/vsce package` 生成 `.vsix`，再在扩展面板里选 “从 VSIX 安装”。

在设置里填：

- `llsp.path`：`/path/to/lark/apps/llsp/build/llsp`
- `llsp.larkHome`：`/path/to/lark`（可以不填，见上面第 1 节）

F12 跳到定义，Ctrl+Shift+O（macOS 上是 Cmd+Shift+O）列出大纲。

## 5. OpenIDEA

把 `openidea/lark.toml` 复制到 OpenIDEA 的配置目录下的 `languages/`，再把里面的 `/path/to/lark` 换成你的仓库路径：

- macOS：`~/Library/Application Support/ai.l0ng.openidea/languages/lark.toml`
- Windows：`%APPDATA%\ai.l0ng.openidea\languages\lark.toml`
- Linux：`~/.config/ai.l0ng.openidea/languages/lark.toml`

语言只在启动时读一次，复制完要重启 OpenIDEA。之后：

- 设置里的「Languages & Frameworks → Language Servers」能看到 `llsp`；
- 打开 `.lark` 文件，错误和警告标在行号旁边（llsp 用 `lark1` 检查，所以 `LARK_HOME` 或者从 llsp 位置往上找的规则见第 1 节；`lark.toml` 里已经写好了 `env`）；
- 跳到定义、文档大纲也是 llsp 给的。

高亮是近似的：`lark.toml` 里没有 `tree-sitter`（OpenIDEA 的语法是编进程序里的，加不了新的），只有 `ui-mode = "Rust"`，借 CodeMirror 的 Rust 模式上色。`fn`、`type`、`enum`、`if`、`else`、`match`、`for`、`in`、`return`、`break`、`continue`、`true`、`false`、`pub`、`const` 和 Rust 一样是关键字，注释、字符串、数字也一样；`take`、`inout`、`interface`、`scope`、`select` 不会被上色。

llsp 还给语义高亮（`semanticTokens`），这一层不靠 Rust 模式，是 llsp 看上下文算的。OpenIDEA 只接它认识的种类，llsp 发的这几种都能上色：

- 类型、函数、参数、字段、enum 的变体（常量色）；
- 局部变量：在 OpenIDEA 的设置里打开「语义高亮」（`settings.toml` 里 `semanticHighlighting = true`）后是彩虹色；
- 关键字：llsp 把它们标成 `selfTypeKeyword`（OpenIDEA 不认 `keyword`，但把 `selfTypeKeyword` 画成关键字色），所以 `take`、`inout`、`interface`、`scope`、`select` 也有关键字色了；
- `self`：标成 `selfKeyword`，用 self 的颜色；
- 修饰：`fn` / `type` / `enum` / `interface` 声明的名字带 `declaration`（函数的声明和调用颜色不同），`int`、`str` 这些内置类型带 `defaultLibrary`（builtin 色）。

模块名（`namespace`）OpenIDEA 的主题里没有颜色，看不出来；字符串、注释、数字还是 Rust 模式上的色。

没有 `tree-sitter` 就没有本地语法树，所以文档大纲靠 llsp 的 `documentSymbol`，不是编辑器自己从语法树里算的。

`lark.toml` 写错了 OpenIDEA 不会报错，只是当它不存在；日志 `~/Library/Logs/ai.l0ng.openidea/` 里会有一行 `ignoring …/lark.toml: …`。

## 提示 permission denied 时

构建出来的程序丢了执行权限（目录被同步工具重写过时会这样）。不用重新构建，在仓库根目录：

```
make perms
```

它给 `build/` 和 `apps/*/build/` 里的程序都加上执行权限。VS Code 扩展每次启动 llsp 之前也会自动补上 llsp 和 `build/lark1` 的权限。

## 出问题时

先在终端里手动跑一次，确认 llsp 能启动、能回复：

```
printf 'Content-Length: 58\r\n\r\n{"jsonrpc":"2.0","id":1,"method":"initialize","params":{}}' | apps/llsp/build/llsp
```

应该看到一条 `Content-Length: …` 开头的回复，里面有 `"capabilities"`。

之后 llsp 会因为 stdin 关了、又没有收到 exit 而退出，退出码是 1，这是正常的。

- Neovim：`:lua vim.cmd.edit(vim.lsp.get_log_path())` 查看日志；
- VS Code：输出面板里选 “Lark (llsp)”。

## 还不支持

- 悬停、重命名、查找引用；
- 跳到标准库（`json.Json` 这种）、方法、枚举的变体、局部变量；
- 诊断：相对文件所在目录的 import、`lark.pkg` 里依赖的别的包。
