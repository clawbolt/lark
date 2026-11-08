/-
apps/lterm 的证明 · 阶段 1：转义序列的解析器
先证明，再写 apps/lterm/vt/parse.lark。

终端从程序那里收到的是一串字节：大多数是要显示的文字，夹着控制字符（换行、退格……）和转义序列
（ESC [ 1 ; 2 H 移动光标、ESC ] 0 ; 标题 BEL 设置标题……）。解析器一个字节一个字节地走，
把字节流切成一个个动作（Act），屏幕（下一阶段）再按动作去改格子。
状态机照 DEC / ANSI 的标准（vt100.net 上 Paul Williams 的那张图）：
  ground（普通文字）、esc（ESC 之后）、escInter（ESC 加中间字节）、
  csiEntry / csiParam / csiInter / csiIgnore（ESC [ 开头的控制序列）、
  osc（ESC ] 开头的字符串，BEL 或 ESC \ 结束）、
  dcsEntry / dcsParam / dcsInter / dcsPass / dcsIgnore（ESC P 开头的设备控制串）、
  sos（ESC X / ESC ^ / ESC _ 开头、整段丢掉的字符串）。
从任何状态：CAN（0x18）、SUB（0x1A）取消正在读的序列、回到 ground；ESC（0x1B）重新开始一个转义序列
（OSC、DCS 正在读时先把它们交出去，ESC \ 就是它们的结束符 ST）。
字节按字节看：UTF-8 的多字节字符在 ground 里一个字节一个 print，下一阶段再拼成字符；C1 控制字符（0x80–0x9F）不认，
因为在 UTF-8 里它们是多字节字符的一部分（和 xterm、Ghostty 的 UTF-8 模式一样）。

证明了：
- 解析器是全函数：任何状态、任何字节都有下一步，所以任何字节流都能吃完，不会卡住（step 的定义本身）；
- `step_cancel`：任何状态下 CAN / SUB 都回到 ground，正在读的参数、字符串全部清掉；
- `step_escape`：任何状态下 ESC 都从头开始一个新的转义序列；
- `run_len`：每个字节最多出一个动作（Option），所以动作不会比字节多；
- `run_text`：从 ground 开始，一串普通文字（不小于 0x20、不是 DEL）原样、按顺序变成 print，状态还是 ground；
- `run_osc`：OSC 字符串（标题等）里的文字一个都不会变成 print，全收进 data，状态还是 osc。
例子（#guard）里检查了：CSI 的参数、私有标记（ESC [ ? 25 l）、省略的参数、参数封顶 65535、
CSI 中间的控制字符照样执行、CAN 取消、ESC 中间字节、OSC 用 BEL 和 ESC \ 结束、DCS。
没证（以后的阶段）：参数里的 :（子参数，SGR 38:2::r:g:b）当成 ; 处理；OSC / DCS 的长度没有上限（Lark 里封顶）。
-/

import Lark.Lsp

namespace Lark
namespace VtParse

def bs (s : String) : List Nat := s.toList.map Char.toNat

inductive St
  | ground | esc | escInter
  | csiEntry | csiParam | csiInter | csiIgnore
  | osc
  | dcsEntry | dcsParam | dcsInter | dcsPass | dcsIgnore
  | sos
deriving DecidableEq, Repr

inductive Act
  | print (c : Nat)                                             -- 显示一个字节
  | exec (c : Nat)                                              -- 控制字符：换行、回车、退格、响铃……
  | esc (inter : List Nat) (f : Nat)                            -- ESC 中间字节 结尾字节
  | csi (params : List Nat) (inter : List Nat) (f : Nat)        -- ESC [ 参数 中间字节 结尾字节；私有标记（? 等）在 inter 的开头
  | osc (data : List Nat)                                       -- ESC ] 内容 BEL
  | dcs (params : List Nat) (inter : List Nat) (f : Nat) (data : List Nat)
deriving DecidableEq, Repr

structure P where
  st : St
  params : List Nat   -- 读完的参数
  cur : Nat           -- 正在读的参数
  any : Bool          -- 读到过数字或分隔符（没有时参数是空的，不是 [0]）
  inter : List Nat    -- 中间字节和私有标记
  final : Nat         -- DCS 的结尾字节（之后是它的内容）
  data : List Nat     -- OSC / DCS 的内容
deriving DecidableEq, Repr

def clear (st : St) : P := ⟨st, [], 0, false, [], 0, []⟩
def init : P := clear .ground

def maxParam : Nat := 65535

def isDig (c : Nat) : Bool := 0x30 ≤ c && c ≤ 0x39
def isInter (c : Nat) : Bool := 0x20 ≤ c && c ≤ 0x2F
def isPriv (c : Nat) : Bool := 0x3C ≤ c && c ≤ 0x3F
def isFinal (c : Nat) : Bool := 0x40 ≤ c && c ≤ 0x7E
def isSep (c : Nat) : Bool := c = 0x3B || c = 0x3A

def digit (p : P) (c : Nat) : P := { p with cur := min maxParam (p.cur * 10 + (c - 0x30)), any := true }
def sep (p : P) : P := { p with params := p.params ++ [p.cur], cur := 0, any := true }
def collect (p : P) (c : Nat) : P := { p with inter := p.inter ++ [c] }
def put (p : P) (c : Nat) : P := { p with data := p.data ++ [c] }
def goto (p : P) (st : St) : P := { p with st := st }
def allParams (p : P) : List Nat := if p.any then p.params ++ [p.cur] else []

/-- ESC 打断时要交出去的：OSC 和 DCS 的内容（ESC \ 是它们的结束符） -/
def finish (p : P) : Option Act :=
  match p.st with
  | .osc => some (.osc p.data)
  | .dcsPass => some (.dcs (allParams p) p.inter p.final p.data)
  | _ => none

/-- CSI 和 DCS 的参数部分（csiEntry / csiParam 里，不是私有标记的字节）；dcs：是不是 DCS -/
def params (p : P) (c : Nat) (dcs : Bool) : P × Option Act :=
  if isDig c then (goto (digit p c) (if dcs then .dcsParam else .csiParam), none)
  else if isSep c then (goto (sep p) (if dcs then .dcsParam else .csiParam), none)
  else if isInter c then (goto (collect p c) (if dcs then .dcsInter else .csiInter), none)
  else if isFinal c then
    (if dcs then ({ goto p .dcsPass with final := c }, none)
     else (clear .ground, some (.csi (allParams p) p.inter c)))
  else (p, none)

def body (p : P) (c : Nat) : P × Option Act :=
  match p.st with
  | .ground =>
    if c < 0x20 then (p, some (.exec c))
    else if c = 0x7F then (p, none)
    else (p, some (.print c))
  | .esc =>
    if c < 0x20 then (p, some (.exec c))
    else if isInter c then (goto (collect p c) .escInter, none)
    else if c = 0x5B then (clear .csiEntry, none)
    else if c = 0x5D then (clear .osc, none)
    else if c = 0x50 then (clear .dcsEntry, none)
    else if c = 0x58 ∨ c = 0x5E ∨ c = 0x5F then (clear .sos, none)
    else if c = 0x7F then (p, none)
    else (clear .ground, some (.esc p.inter c))
  | .escInter =>
    if c < 0x20 then (p, some (.exec c))
    else if isInter c then (collect p c, none)
    else if c = 0x7F then (p, none)
    else (clear .ground, some (.esc p.inter c))
  | .csiEntry =>
    if c < 0x20 then (p, some (.exec c))
    else if isPriv c then (goto (collect p c) .csiParam, none)
    else params p c false
  | .csiParam =>
    if c < 0x20 then (p, some (.exec c))
    else if isPriv c then (goto p .csiIgnore, none)
    else params p c false
  | .csiInter =>
    if c < 0x20 then (p, some (.exec c))
    else if isInter c then (collect p c, none)
    else if isFinal c then (clear .ground, some (.csi (allParams p) p.inter c))
    else if c < 0x40 then (goto p .csiIgnore, none)
    else (p, none)
  | .csiIgnore =>
    if c < 0x20 then (p, some (.exec c))
    else if isFinal c then (clear .ground, none)
    else (p, none)
  | .osc =>
    if c = 0x07 then (clear .ground, some (.osc p.data))
    else if c < 0x20 then (p, none)
    else (put p c, none)
  | .dcsEntry =>
    if c < 0x20 then (p, none)
    else if isPriv c then (goto (collect p c) .dcsParam, none)
    else params p c true
  | .dcsParam =>
    if c < 0x20 then (p, none)
    else if isPriv c then (goto p .dcsIgnore, none)
    else params p c true
  | .dcsInter =>
    if c < 0x20 then (p, none)
    else if isInter c then (collect p c, none)
    else if isFinal c then ({ goto p .dcsPass with final := c }, none)
    else if c < 0x40 then (goto p .dcsIgnore, none)
    else (p, none)
  | .dcsPass => if c = 0x7F then (p, none) else (put p c, none)
  | .dcsIgnore => (p, none)
  | .sos => (p, none)

/-- 走一个字节：最多出一个动作 -/
def step (p : P) (c : Nat) : P × Option Act :=
  if c = 0x18 ∨ c = 0x1A then (clear .ground, some (.exec c))
  else if c = 0x1B then (clear .esc, finish p)
  else body p c

def run : P → List Nat → List Act
  | _, [] => []
  | p, c :: r => (step p c).2.toList ++ run (step p c).1 r

def last : P → List Nat → P
  | p, [] => p
  | p, c :: r => last (step p c).1 r

theorem step_cancel (p : P) (c : Nat) (h : c = 0x18 ∨ c = 0x1A) :
    step p c = (clear .ground, some (.exec c)) := by
  simp only [step]
  rw [Lsp.iteT h]

theorem step_escape (p : P) : (step p 0x1B).1 = clear .esc := by
  simp [step]

theorem run_len : ∀ (p : P) (l : List Nat), (run p l).length ≤ l.length
  | _, [] => by simp [run]
  | p, c :: r => by
    have h1 := run_len (step p c).1 r
    have h2 : (step p c).2.toList.length ≤ 1 := by
      cases (step p c).2 <;> simp
    simp only [run, List.length_append, List.length_cons]
    omega

/-- 普通文字：不小于 0x20、不是 DEL -/
def text (c : Nat) : Bool := 0x20 ≤ c && c != 0x7F

theorem step_text (c : Nat) (h : text c = true) : step init c = (init, some (.print c)) := by
  have hh := h
  simp [text] at hh
  have h1 : c ≠ 0x18 := by omega
  have h2 : c ≠ 0x1A := by omega
  have h3 : c ≠ 0x1B := by omega
  have h4 : ¬ c < 0x20 := by omega
  have h5 : c ≠ 0x7F := by omega
  simp [step, body, init, clear, h1, h2, h3, h4, h5]

theorem run_text : ∀ (l : List Nat), (∀ c ∈ l, text c = true) → run init l = l.map Act.print
  | [], _ => by simp [run]
  | c :: r, h => by
    have hc : text c = true := h c (by simp)
    have hr : ∀ x ∈ r, text x = true := fun x hx => h x (by simp [hx])
    simp only [run, step_text c hc]
    rw [run_text r hr]
    simp

theorem step_osc (p : P) (c : Nat) (hp : p.st = .osc) (hc : 0x20 ≤ c) : step p c = (put p c, none) := by
  have h1 : c ≠ 0x18 := by omega
  have h2 : c ≠ 0x1A := by omega
  have h3 : c ≠ 0x1B := by omega
  have h4 : ¬ c < 0x20 := by omega
  have h5 : c ≠ 0x07 := by omega
  simp [step, body, hp, h1, h2, h3, h4, h5]

theorem run_osc : ∀ (l : List Nat) (p : P), p.st = .osc → (∀ c ∈ l, 0x20 ≤ c) →
    run p l = [] ∧ (last p l).st = .osc ∧ (last p l).data = p.data ++ l
  | [], p, hp, _ => by simp [run, last, hp]
  | c :: r, p, hp, h => by
    have hc : 0x20 ≤ c := h c (by simp)
    have hr : ∀ x ∈ r, 0x20 ≤ x := fun x hx => h x (by simp [hx])
    have hs := step_osc p c hp hc
    have hq : (put p c).st = .osc := by simp [put, hp]
    obtain ⟨e1, e2, e3⟩ := run_osc r (put p c) hq hr
    refine ⟨?_, ?_, ?_⟩
    · simp only [run, hs]
      simpa using e1
    · simp only [last, hs]
      exact e2
    · simp only [last, hs]
      rw [e3]
      simp [put]

/-! ## 例子 -/

-- 文字、CSI 移动光标、再是文字
#guard run init (bs "ab\x1b[1;2Hc") == [.print 97, .print 98, .csi [1, 2] [] 72, .print 99]
-- 私有标记：ESC [ ? 25 l（隐藏光标）
#guard run init (bs "\x1b[?25l") == [.csi [25] [63] 108]
-- 没有参数是空的；省略的参数是 0
#guard run init (bs "\x1b[H") == [.csi [] [] 72]
#guard run init (bs "\x1b[;5H") == [.csi [0, 5] [] 72]
-- 参数封顶 65535
#guard run init (bs "\x1b[99999999m") == [.csi [65535] [] 109]
-- CSI 中间的控制字符照样执行，序列接着读
#guard run init (bs "\x1b[1\n2m") == [.exec 10, .csi [12] [] 109]
-- CAN 取消读了一半的序列
#guard run init (bs "\x1b[12\x18x") == [.exec 24, .print 120]
-- ESC 中间字节 结尾字节：ESC ( B 选字符集
#guard run init (bs "\x1b(B") == [.esc [40] 66]
-- OSC：BEL 结束；ESC \ 结束（之后的 ESC \ 本身是一个 esc 动作）
#guard run init (bs "\x1b]0;hi\x07x") == [.osc (bs "0;hi"), .print 120]
#guard run init (bs "\x1b]2;t\x1b\\") == [.osc (bs "2;t"), .esc [] 92]
-- DCS：参数 1、中间字节 $、结尾字节 q、内容 m
#guard run init (bs "\x1bP1$qm\x1b\\") == [.dcs [1] [36] 113 (bs "m"), .esc [] 92]
-- 序列里多了私有标记：整段丢掉
#guard run init (bs "\x1b[1?2hx") == [.print 120]
-- SOS / PM / APC 的内容整段丢掉
#guard run init (bs "\x1b_abc\x1b\\d") == [.esc [] 92, .print 100]

end VtParse
end Lark
