/-
apps/lterm 的证明 · 阶段 4：颜色和样式（SGR，CSI … m）
先证明，再写 apps/lterm/vt/style.lark。

程序用 CSI 参数 m 设置之后写的字的样式：0 复位，1 粗体，31 红字，38;5;208 256 色里的第 208 个，
48;2;r;g;b 真彩色背景……一个 CSI 里可以有好几个，按顺序生效。
38 / 48 后面跟着几个参数才是一个颜色，所以参数一个一个走，记着是不是在读扩展色（X）：
  none（普通的参数）、pick（读到 38 / 48，下一个是 5 还是 2）、idx（下一个是 256 色的下标）、
  r / g / b（真彩色的三个分量）、dead（扩展色写坏了：这个 CSI 后面的参数都不管）。

证明了：
- `one_ok`、`step_ok`、`run_ok`、`apply_ok`：任何参数序列以后，颜色都在范围里（256 色的下标 < 256，真彩色的分量 < 256），
  不合法的颜色不会写进去（直接不改）；
- `run_append`：参数可以分两段走，结果一样（序列跨两段到达时也对）；
- `apply_nil`、`apply_zero`：CSI m 和 CSI 0 m 都复位成默认样式。
例子（#guard）里检查了：粗体 + 红字、256 色、真彩色背景后面接下划线、超出范围的下标、写坏的扩展色、
22 同时去掉粗体和暗淡、亮色 90–97 / 100–107、39 / 49 默认色、分两段走。
没做：冒号的子参数（38:2::r:g:b，解析器把 : 当成 ;，所以会读错）；21 双下划线、53 上划线这些不常用的。
-/

import Lark.Lsp

namespace Lark
namespace VtSgr

inductive Color
  | dflt                     -- 默认色
  | idx (n : Nat)            -- 256 色：0–7 普通、8–15 亮色、16–255
  | rgb (r g b : Nat)        -- 真彩色
deriving DecidableEq, Repr

def colorOk : Color → Bool
  | .dflt => true
  | .idx n => n < 256
  | .rgb r g b => r < 256 && g < 256 && b < 256

structure Sty where
  fg : Color := .dflt
  bg : Color := .dflt
  bold : Bool := false
  dim : Bool := false
  italic : Bool := false
  under : Bool := false
  blink : Bool := false
  inverse : Bool := false
  hidden : Bool := false
  strike : Bool := false
deriving DecidableEq, Repr

def dflt : Sty := {}

abbrev Ok (s : Sty) : Prop := colorOk s.fg = true ∧ colorOk s.bg = true

/-- 改前景色（true）或者背景色（false） -/
def setC : Sty → Bool → Color → Sty
  | s, true, c => { s with fg := c }
  | s, false, c => { s with bg := c }

/-- 一个普通的参数 -/
def one (s : Sty) (p : Nat) : Sty :=
  if p = 0 then dflt
  else if p = 1 then { s with bold := true }
  else if p = 2 then { s with dim := true }
  else if p = 3 then { s with italic := true }
  else if p = 4 then { s with under := true }
  else if p = 5 then { s with blink := true }
  else if p = 7 then { s with inverse := true }
  else if p = 8 then { s with hidden := true }
  else if p = 9 then { s with strike := true }
  else if p = 22 then { s with bold := false, dim := false }
  else if p = 23 then { s with italic := false }
  else if p = 24 then { s with under := false }
  else if p = 25 then { s with blink := false }
  else if p = 27 then { s with inverse := false }
  else if p = 28 then { s with hidden := false }
  else if p = 29 then { s with strike := false }
  else if 30 ≤ p ∧ p ≤ 37 then setC s true (.idx (p - 30))
  else if p = 39 then setC s true .dflt
  else if 40 ≤ p ∧ p ≤ 47 then setC s false (.idx (p - 40))
  else if p = 49 then setC s false .dflt
  else if 90 ≤ p ∧ p ≤ 97 then setC s true (.idx (p - 90 + 8))
  else if 100 ≤ p ∧ p ≤ 107 then setC s false (.idx (p - 100 + 8))
  else s

/-- 是不是在读扩展色；fg：读的是前景色（38）还是背景色（48） -/
inductive X
  | none
  | pick (fg : Bool)
  | idx (fg : Bool)
  | r (fg : Bool)
  | g (fg : Bool) (r : Nat)
  | b (fg : Bool) (r g : Nat)
  | dead
deriving DecidableEq, Repr

def step : Sty × X → Nat → Sty × X
  | (s, .none), p => if p = 38 then (s, .pick true) else if p = 48 then (s, .pick false) else (one s p, .none)
  | (s, .pick fg), p => if p = 5 then (s, .idx fg) else if p = 2 then (s, .r fg) else (s, .dead)
  | (s, .idx fg), p => (if p < 256 then setC s fg (.idx p) else s, .none)
  | (s, .r fg), p => (s, .g fg p)
  | (s, .g fg r), p => (s, .b fg r p)
  | (s, .b fg r g), p => (if r < 256 ∧ g < 256 ∧ p < 256 then setC s fg (.rgb r g p) else s, .none)
  | (s, .dead), _ => (s, .dead)

def run (st : Sty × X) (l : List Nat) : Sty × X := l.foldl step st

/-- CSI … m：没有参数时等于 0 -/
def apply (s : Sty) (ps : List Nat) : Sty := if ps = [] then dflt else (run (s, .none) ps).1

theorem setC_ok {s : Sty} {c : Color} (fg : Bool) (h : Ok s) (hc : colorOk c = true) : Ok (setC s fg c) := by
  cases fg
  · exact ⟨h.1, hc⟩
  · exact ⟨hc, h.2⟩

theorem dflt_ok : Ok dflt := ⟨rfl, rfl⟩

theorem iteOk {c : Prop} [Decidable c] {a b : Sty} (ha : c → Ok a) (hb : ¬c → Ok b) : Ok (if c then a else b) := by
  by_cases hc : c
  · rw [Lsp.iteT hc]
    exact ha hc
  · rw [Lsp.iteF hc]
    exact hb hc

theorem one_ok (s : Sty) (p : Nat) (h : Ok s) : Ok (one s p) := by
  unfold one
  repeat
    first
      | exact h
      | exact dflt_ok
      | exact ⟨h.1, h.2⟩
      | (apply setC_ok _ h; simp [colorOk] <;> omega)
      | (apply iteOk <;> intro _)

theorem step_ok (s : Sty) (x : X) (p : Nat) (h : Ok s) : Ok (step (s, x) p).1 := by
  cases x with
  | none =>
    simp only [step]
    by_cases h1 : p = 38
    · rw [Lsp.iteT h1]
      exact h
    · rw [Lsp.iteF h1]
      by_cases h2 : p = 48
      · rw [Lsp.iteT h2]
        exact h
      · rw [Lsp.iteF h2]
        exact one_ok s p h
  | pick fg =>
    simp only [step]
    by_cases h1 : p = 5
    · rw [Lsp.iteT h1]
      exact h
    · rw [Lsp.iteF h1]
      by_cases h2 : p = 2
      · rw [Lsp.iteT h2]
        exact h
      · rw [Lsp.iteF h2]
        exact h
  | idx fg =>
    simp only [step]
    by_cases h1 : p < 256
    · rw [Lsp.iteT h1]
      exact setC_ok fg h (by simp [colorOk, h1])
    · rw [Lsp.iteF h1]
      exact h
  | r fg => exact h
  | g fg r => exact h
  | b fg r g =>
    simp only [step]
    by_cases h1 : r < 256 ∧ g < 256 ∧ p < 256
    · rw [Lsp.iteT h1]
      exact setC_ok fg h (by simp [colorOk, h1.1, h1.2.1, h1.2.2])
    · rw [Lsp.iteF h1]
      exact h
  | dead => exact h

theorem run_ok : ∀ (l : List Nat) (s : Sty) (x : X), Ok s → Ok (run (s, x) l).1
  | [], _, _, h => h
  | p :: r, s, x, h => by
    have e : run (s, x) (p :: r) = run (step (s, x) p) r := rfl
    rw [e]
    exact run_ok r (step (s, x) p).1 (step (s, x) p).2 (step_ok s x p h)

theorem apply_ok (s : Sty) (ps : List Nat) (h : Ok s) : Ok (apply s ps) := by
  unfold apply
  by_cases h1 : ps = []
  · rw [Lsp.iteT h1]
    exact dflt_ok
  · rw [Lsp.iteF h1]
    exact run_ok ps s .none h

theorem run_append (st : Sty × X) (a b : List Nat) : run st (a ++ b) = run (run st a) b := by
  simp [run]

theorem apply_nil (s : Sty) : apply s [] = dflt := by simp [apply]

theorem apply_zero (s : Sty) : apply s [0] = dflt := by simp [apply, run, step, one]

/-! ## 例子 -/

#guard apply dflt [1, 31] == ({ bold := true, fg := .idx 1 } : Sty)
#guard apply dflt [38, 5, 208] == ({ fg := .idx 208 } : Sty)
#guard apply dflt [48, 2, 1, 2, 3, 4] == ({ bg := .rgb 1 2 3, under := true } : Sty)
-- 超出范围的下标：不改；写坏的扩展色：后面的参数都不管
#guard apply dflt [38, 5, 300] == dflt
#guard apply dflt [38, 7, 1] == dflt
-- 复位；22 同时去掉粗体和暗淡；亮色；默认色
#guard apply ({ bold := true, fg := .idx 2 } : Sty) [] == dflt
#guard apply ({ bold := true, dim := true } : Sty) [22] == dflt
#guard apply dflt [90, 107] == ({ fg := .idx 8, bg := .idx 15 } : Sty)
#guard apply ({ fg := .idx 3 } : Sty) [39] == dflt
-- 分两段走：读了一半的扩展色记着
#guard run (dflt, .none) [38, 2] == (dflt, X.r true)
#guard run (run (dflt, .none) [38, 2, 10]) [20, 30] == run (dflt, .none) [38, 2, 10, 20, 30]

end VtSgr
end Lark
