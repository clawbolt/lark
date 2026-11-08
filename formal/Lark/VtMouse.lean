/-
apps/lterm 的证明 · 阶段 13：把鼠标交给里面的程序
先证明，再写 apps/lterm/vt/mouse.lark。

vim、htop、codex、tmux 这类程序打开鼠标模式以后，终端不再自己选中，而是把点击、拖动、滚轮写成字节交给程序：
- CSI ? 1000 h：报按下、松开、滚轮；? 1002 h：再加上按着键拖动；? 1003 h：再加上不按键移动（off / press / drag / any）；
  CSI ? 1000 / 1002 / 1003 l：都不报。
- CSI ? 1006 h（SGR 格式）：ESC [ < 码 ; 列 + 1 ; 行 + 1 M（松开时最后是 m）。没打开 1006 时用老格式（X10）：
  ESC [ M 后面三个字节 32 + 码、33 + 列、33 + 行，放不下（超过 255）时不报。
- 码：按键 0 左、1 中、2 右；拖动 + 32（移动时没按键是 3 + 32）；滚轮 64 上、65 下；Shift + 4、Meta + 8、Ctrl + 16。
  老格式里松开不知道是哪个键，码是 3。

证明了：
- `sgr_parse`：SGR 格式的那串字节交给阶段 1 的解析器（VtParse），正好解析成一个动作 CSI < [码, 列 + 1, 行 + 1] M / m，
  不多也不少——程序（也用同样的标准解析）读到的正是这个事件（用阶段 9 VtReply 的 dec_acc、run_digs、run_sep）；
- `code_press`、`code_motion`、`code_wheel`：按下 / 松开的码小于 32、拖动 / 移动在 32 到 63、滚轮至少 64，
  按下时码 % 4 是哪个键、码 / 4 是 Shift / Meta / Ctrl——程序从码就能分出是什么事件；
- `off_quiet`、`press_on`、`motion_free`、`motion_held`：没打开时什么都不报；打开了按下、松开、滚轮都报；
  不按键移动只有 1003 报，按着键拖只有 1002 和 1003 报；
- `set_off`、`set_other`：关掉 1000 / 1002 / 1003 里的任何一个都不报了；别的模式号不动鼠标的状态；
- `x10_len`：老格式报的时候正好 6 个字节，每个都小于 256。
例子（#guard）里检查了：左键按下、松开、右键拖、滚轮、Ctrl、老格式、解析回来。
-/
import Lark.Lsp
import Lark.VtParse
import Lark.VtReply

namespace Lark
namespace VtMouse

open VtParse
open VtReply

/-! ## 模式 -/

inductive Track where
  | off | press | drag | any
  deriving DecidableEq, Repr

structure M where
  track : Track
  sgr : Bool
  deriving DecidableEq, Repr

def start : M := ⟨.off, false⟩

def isMouse (n : Nat) : Prop := n = 1000 ∨ n = 1002 ∨ n = 1003

instance (n : Nat) : Decidable (isMouse n) := by unfold isMouse; infer_instance

def trackOf (n : Nat) : Track := if n = 1000 then .press else if n = 1002 then .drag else .any

/-- CSI ? n h / l -/
def setMode (m : M) (n : Nat) (on : Bool) : M :=
  if n = 1006 then { m with sgr := on }
  else if isMouse n then { m with track := if on then trackOf n else .off }
  else m

theorem set_off (m : M) {n : Nat} (h : isMouse n) : (setMode m n false).track = .off := by
  have h1 : ¬n = 1006 := by unfold isMouse at h; omega
  unfold setMode
  rw [Lsp.iteF h1, Lsp.iteT h]
  rfl

theorem set_other (m : M) {n : Nat} (on : Bool) (h1 : ¬n = 1006) (h2 : ¬isMouse n) : setMode m n on = m := by
  unfold setMode
  rw [Lsp.iteF h1, Lsp.iteF h2]

/-! ## 事件和码 -/

inductive Kind where
  | press | release | motion | wheel
  deriving DecidableEq, Repr

/-- btn：按下、松开时是哪个键（0 左、1 中、2 右）；拖动时按着的键；滚轮 0 上、1 下。
held：移动时有没有按着键。mods：1 Shift、2 Meta、4 Ctrl 加起来。x、y 从 0 开始 -/
structure Ev where
  kind : Kind
  btn : Nat
  held : Bool
  mods : Nat
  x : Nat
  y : Nat
  deriving DecidableEq, Repr

def base (e : Ev) : Nat :=
  match e.kind with
  | .press => e.btn
  | .release => e.btn
  | .motion => (if e.held then e.btn else 3) + 32
  | .wheel => 64 + e.btn

def code (e : Ev) : Nat := base e + 4 * e.mods

/-- 这个事件报不报 -/
def wants (t : Track) (e : Ev) : Bool :=
  match t, e.kind with
  | .off, _ => false
  | .press, .motion => false
  | .drag, .motion => e.held
  | _, _ => true

theorem off_quiet (e : Ev) : wants .off e = false := by
  unfold wants
  cases e.kind <;> rfl

theorem press_on {t : Track} {e : Ev} (ht : t ≠ .off) (hk : e.kind ≠ .motion) : wants t e = true := by
  unfold wants
  cases t <;> cases hc : e.kind <;> simp_all

theorem motion_free {t : Track} {e : Ev} (hk : e.kind = .motion) (hh : e.held = false) :
    wants t e = true ↔ t = .any := by
  unfold wants
  cases t <;> simp [hk, hh]

theorem motion_held {t : Track} {e : Ev} (hk : e.kind = .motion) (hh : e.held = true) :
    wants t e = true ↔ (t = .drag ∨ t = .any) := by
  unfold wants
  cases t <;> simp [hk, hh]

theorem code_press {e : Ev} (hk : e.kind = .press ∨ e.kind = .release) (hb : e.btn < 3) :
    code e % 4 = e.btn ∧ code e / 4 = e.mods := by
  have e1 : base e = e.btn := by
    unfold base
    rcases hk with h | h <;> rw [h]
  unfold code
  rw [e1]
  omega

theorem code_motion {e : Ev} (hk : e.kind = .motion) (hb : e.btn < 4) (hm : e.mods < 8) :
    32 ≤ code e ∧ code e < 64 := by
  have e1 : base e = (if e.held then e.btn else 3) + 32 := by
    unfold base
    rw [hk]
  unfold code
  rw [e1]
  split <;> omega

theorem code_wheel {e : Ev} (hk : e.kind = .wheel) : 64 ≤ code e := by
  have e1 : base e = 64 + e.btn := by
    unfold base
    rw [hk]
  unfold code
  rw [e1]
  omega

theorem code_small {e : Ev} (hk : e.kind = .press ∨ e.kind = .release) (hb : e.btn < 3) (hm : e.mods < 8) :
    code e < 32 := by
  have e1 : base e = e.btn := by
    unfold base
    rcases hk with h | h <;> rw [h]
  unfold code
  rw [e1]
  omega

/-! ## SGR 格式（? 1006） -/

def fin (e : Ev) : Nat := if e.kind = .release then 0x6D else 0x4D

theorem fin_cases (e : Ev) : fin e = 0x4D ∨ fin e = 0x6D := by
  unfold fin
  split
  · exact Or.inr rfl
  · exact Or.inl rfl

def sgr (e : Ev) : List Nat :=
  0x1B :: 0x5B :: 0x3C :: (dec (code e) ++ (0x3B :: (dec (e.x + 1) ++ (0x3B :: (dec (e.y + 1) ++ [fin e])))))

theorem run_finM {p : P} (h : p.st = .csiParam) (f : Nat) (hf : f = 0x4D ∨ f = 0x6D) :
    run p [f] = [.csi (allParams p) p.inter f] := by
  have e : step p f = (clear .ground, some (.csi (allParams p) p.inter f)) := by
    rcases hf with rfl | rfl <;> simp [step, body, params, h, isDig, isSep, isPriv, isInter, isFinal]
  show (step p f).2.toList ++ run (step p f).1 [] = _
  rw [e]
  rfl

theorem sgr_parse {e : Ev} (hc : code e ≤ maxParam) (hx : e.x + 1 ≤ maxParam) (hy : e.y + 1 ≤ maxParam) :
    run VtParse.init (sgr e) = [.csi [code e, e.x + 1, e.y + 1] [0x3C] (fin e)] := by
  have e0 : run VtParse.init (sgr e)
      = run (goto (collect (clear .csiEntry) 0x3C) .csiParam)
          (dec (code e) ++ (0x3B :: (dec (e.x + 1) ++ (0x3B :: (dec (e.y + 1) ++ [fin e]))))) := rfl
  rw [e0, run_digs (dec (code e)) _ (dec_dig _) (dec_ne _), run_sep _,
    run_digs (dec (e.x + 1)) _ (dec_dig _) (dec_ne _), run_sep _,
    run_digs (dec (e.y + 1)) _ (dec_dig _) (dec_ne _), run_finM _ (fin e) (fin_cases e)]
  show [Act.csi [acc 0 (dec (code e)), acc 0 (dec (e.x + 1)), acc 0 (dec (e.y + 1))] [0x3C] (fin e)] = _
  rw [dec_acc _ hc, dec_acc _ hx, dec_acc _ hy]
  all_goals first | rfl | exact Or.inl rfl | exact Or.inr rfl

/-! ## 老格式（X10） -/

/-- 老格式的码：松开时不知道是哪个键，是 3 -/
def xcode (e : Ev) : Nat := if e.kind = .release then 3 + 4 * e.mods else code e

def x10 (e : Ev) : Option (List Nat) :=
  if 32 + xcode e < 256 ∧ 33 + e.x < 256 ∧ 33 + e.y < 256 then
    some [0x1B, 0x5B, 0x4D, 32 + xcode e, 33 + e.x, 33 + e.y]
  else none

theorem x10_len {e : Ev} {l : List Nat} (h : x10 e = some l) : l.length = 6 ∧ ∀ c ∈ l, c < 256 := by
  unfold x10 at h
  split at h
  · rename_i hb
    simp only [Option.some.injEq] at h
    subst h
    refine ⟨rfl, ?_⟩
    intro c hc
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> omega
  · simp at h

/-- 报给程序的字节（不报时是 none） -/
def report (m : M) (e : Ev) : Option (List Nat) :=
  if wants m.track e = true then (if m.sgr then some (sgr e) else x10 e) else none

theorem report_off (e : Ev) (s : Bool) : report ⟨.off, s⟩ e = none := by
  unfold report
  simp [off_quiet]

/-! ## 例子 -/

def ev (k : Kind) (b : Nat) (h : Bool) (m x y : Nat) : Ev := ⟨k, b, h, m, x, y⟩

-- 左键在左上角按下、在 (9, 4) 松开
#guard sgr (ev .press 0 false 0 0 0) == [0x1B, 0x5B, 0x3C, 0x30, 0x3B, 0x31, 0x3B, 0x31, 0x4D]
#guard sgr (ev .release 0 false 0 9 4) == [0x1B, 0x5B, 0x3C, 0x30, 0x3B, 0x31, 0x30, 0x3B, 0x35, 0x6D]
-- 右键拖：2 + 32；滚轮下：65；Ctrl + 左键：16
#guard code (ev .motion 2 true 0 0 0) == 34
#guard code (ev .motion 0 false 0 0 0) == 35
#guard code (ev .wheel 1 false 0 0 0) == 65
#guard code (ev .press 0 false 4 0 0) == 16
-- 解析回来
#guard run VtParse.init (sgr (ev .wheel 0 false 0 79 23)) == [.csi [64, 80, 24] [0x3C] 0x4D]
#guard run VtParse.init (sgr (ev .release 2 false 1 3 5)) == [.csi [6, 4, 6] [0x3C] 0x6D]
-- 老格式：松开是 3；放不下时不报
#guard x10 (ev .release 0 false 0 0 0) == some [0x1B, 0x5B, 0x4D, 35, 33, 33]
#guard x10 (ev .press 0 false 0 300 0) == none
-- 模式：1000 不报移动、1002 报按着键拖、1003 都报；关掉以后都不报
#guard report (setMode (setMode start 1000 true) 1006 true) (ev .motion 0 true 0 1 1) == none
#guard report (setMode (setMode start 1002 true) 1006 true) (ev .motion 0 true 0 1 1) == some (sgr (ev .motion 0 true 0 1 1))
#guard report (setMode (setMode start 1002 true) 1006 true) (ev .motion 0 false 0 1 1) == none
#guard (report (setMode start 1003 true) (ev .motion 0 false 0 1 1)).isSome
#guard report (setMode (setMode start 1003 true) 1003 false) (ev .press 0 false 0 1 1) == none

end VtMouse
end Lark
