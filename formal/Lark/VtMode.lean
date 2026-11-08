/-
apps/lterm 的证明 · 阶段 5：模式（DECSET / DECRST，CSI ? n h / CSI ? n l）、备用屏幕、保存光标
先证明，再写 apps/lterm/vt/mode.lark。

终端在屏幕（VtScreen.S）外面再包一层（T）：
- awm（?7，自动换行）：关掉以后写到最后一列不再换行，后面的字都写在最后一列上（noWrap）；
- tcem（?25，显示光标）、paste（?2004，括号粘贴）：只是记着，给以后画屏幕、转发粘贴用；
- ?47 / ?1047 / ?1049（备用屏幕）：进去时把主屏幕整个存起来（other），换成一个空的屏幕，光标位置不变；
  出来时把主屏幕原样换回来（全屏程序 vim、less 退出后，原来的内容回来）；已经在里面时再进去、不在里面时出来都不动；
- ESC 7 / ESC 8、CSI s / CSI u（DECSC / DECRC）：保存、恢复光标位置（恢复时限制在屏幕里）。

证明了：
- `step_ok`、`run_ok`、`init_ok`：任何操作以后，现在的屏幕和存着的主屏幕都是好的（VtScreen.Ok）；
- `alt_restore`：在主屏幕上进备用屏幕、做任何不切换屏幕的操作、再出来，主屏幕和进去之前一模一样（字、光标、滚动区域）；
- `nowrap_y`：自动换行关掉时写字不会换行（光标还在这一行）。
例子（#guard）里检查了：关掉自动换行、备用屏幕进出、重复进出、保存恢复光标、不认识的模式不动。
没做：DECOM（?6，原点模式）、IRM（插入模式）、鼠标的那些模式（?1000 等，只是转发，下一阶段用 pty 时再说）。
-/
import Lark.Lsp
import Lark.VtScreen

namespace Lark
namespace VtMode

structure T where
  scr : VtScreen.S                  -- 现在显示的屏幕
  other : Option VtScreen.S := none -- 在备用屏幕上时：存着的主屏幕
  awm : Bool := true
  tcem : Bool := true
  paste : Bool := false
  sx : Nat := 0                     -- DECSC 存的光标
  sy : Nat := 0

def init (R C : Nat) : T := { scr := VtScreen.init R C }

abbrev Ok (t : T) : Prop := VtScreen.Ok t.scr ∧ ∀ m, t.other = some m → VtScreen.Ok m

/-- 自动换行关掉时写一个字：和 put 一样，但是不留 pend（写到最后一列就停在那里） -/
def noWrap (s : VtScreen.S) (c w : Nat) : VtScreen.S :=
  if w = 0 ∨ (w = 2 ∧ s.C < 2) then s else { VtScreen.put s c w with pend := false }

def scrStep (t : T) (o : VtScreen.Op) : VtScreen.S :=
  match o with
  | .print c w => if t.awm then VtScreen.print t.scr c w else noWrap t.scr c w
  | o => VtScreen.step t.scr o

def enter (t : T) : T :=
  match t.other with
  | some _ => t
  | none => { t with other := some t.scr, scr := VtScreen.moveTo (VtScreen.init t.scr.R t.scr.C) t.scr.x t.scr.y false }

def leave (t : T) : T :=
  match t.other with
  | some m => { t with scr := m, other := none }
  | none => t

def isAlt (m : Nat) : Bool := m == 47 || m == 1047 || m == 1049

def setMode (t : T) (m : Nat) (on : Bool) : T :=
  if m = 7 then { t with awm := on }
  else if m = 25 then { t with tcem := on }
  else if m = 2004 then { t with paste := on }
  else if isAlt m = true then (if on then enter t else leave t)
  else t

inductive Op
  | scr (o : VtScreen.Op)
  | mode (m : Nat) (on : Bool)
  | save
  | restore

def step (t : T) : Op → T
  | .scr o => { t with scr := scrStep t o }
  | .mode m on => setMode t m on
  | .save => { t with sx := t.scr.x, sy := t.scr.y }
  | .restore => { t with scr := VtScreen.moveTo t.scr (VtScreen.lim t.scr.C t.sx) (VtScreen.lim t.scr.R t.sy) false }

def run (t : T) : List Op → T
  | [] => t
  | o :: r => run (step t o) r

/-! ## 都是好的 -/

theorem iteOk {c : Prop} [Decidable c] {a b : T} (ha : c → Ok a) (hb : ¬c → Ok b) : Ok (if c then a else b) := by
  by_cases hc : c
  · rw [Lsp.iteT hc]
    exact ha hc
  · rw [Lsp.iteF hc]
    exact hb hc

theorem noWrap_ok {s : VtScreen.S} (h : VtScreen.Ok s) (c w : Nat) : VtScreen.Ok (noWrap s c w) := by
  unfold noWrap
  by_cases hc : (w = 0 ∨ (w = 2 ∧ s.C < 2))
  · rw [Lsp.iteT hc]
    exact h
  · rw [Lsp.iteF hc]
    exact VtScreen.put_ok h c w

theorem scrStep_ok (t : T) (o : VtScreen.Op) (h : VtScreen.Ok t.scr) : VtScreen.Ok (scrStep t o) := by
  cases o
  case print c w =>
    show VtScreen.Ok (if t.awm then VtScreen.print t.scr c w else noWrap t.scr c w)
    by_cases ha : t.awm = true
    · rw [Lsp.iteT ha]
      exact VtScreen.print_ok h c w
    · rw [Lsp.iteF ha]
      exact noWrap_ok h c w
  all_goals exact VtScreen.step_ok t.scr _ h

theorem enter_ok {t : T} (h : Ok t) : Ok (enter t) := by
  unfold enter
  cases hc : t.other with
  | some _ => exact h
  | none =>
    obtain ⟨hs, _⟩ := h
    obtain ⟨hR, hC, _, _, hx, hy, _, _⟩ := id hs
    refine ⟨VtScreen.cur_ok (VtScreen.init_ok hR hC) t.scr.x t.scr.y false hx hy, ?_⟩
    intro m hm
    rw [← Option.some.inj hm]
    exact hs

theorem leave_ok {t : T} (h : Ok t) : Ok (leave t) := by
  unfold leave
  cases hc : t.other with
  | some m =>
    refine ⟨h.2 m hc, ?_⟩
    intro _ hm
    simp at hm
  | none => exact h

theorem setMode_ok {t : T} (h : Ok t) (m : Nat) (on : Bool) : Ok (setMode t m on) := by
  unfold setMode
  repeat
    first
      | exact h
      | exact enter_ok h
      | exact leave_ok h
      | (apply iteOk <;> intro _)

theorem step_ok (t : T) (o : Op) (h : Ok t) : Ok (step t o) := by
  cases o with
  | scr o => exact ⟨scrStep_ok t o h.1, h.2⟩
  | mode m on => exact setMode_ok h m on
  | save => exact h
  | restore =>
    obtain ⟨hR, hC, _⟩ := id h.1
    exact ⟨VtScreen.cur_ok h.1 _ _ false (VtScreen.lim_lt hC) (VtScreen.lim_lt hR), h.2⟩

theorem run_ok : ∀ (ops : List Op) (t : T), Ok t → Ok (run t ops)
  | [], _, h => h
  | o :: r, t, h => run_ok r (step t o) (step_ok t o h)

theorem init_ok {R C : Nat} (hR : 0 < R) (hC : 0 < C) : Ok (init R C) := by
  refine ⟨VtScreen.init_ok hR hC, ?_⟩
  intro _ hm
  simp [init] at hm

/-! ## 备用屏幕出来以后，主屏幕原样回来 -/

/-- 不切换屏幕的操作 -/
def noAlt : Op → Bool
  | .mode m _ => !isAlt m
  | _ => true

theorem setMode_other (t : T) {m : Nat} (on : Bool) (hm : isAlt m = false) : (setMode t m on).other = t.other := by
  unfold setMode
  by_cases h1 : m = 7
  · rw [Lsp.iteT h1]
  · rw [Lsp.iteF h1]
    by_cases h2 : m = 25
    · rw [Lsp.iteT h2]
    · rw [Lsp.iteF h2]
      by_cases h3 : m = 2004
      · rw [Lsp.iteT h3]
      · rw [Lsp.iteF h3]
        have h4 : ¬(isAlt m = true) := by rw [hm]; decide
        rw [Lsp.iteF h4]

theorem step_other (t : T) (o : Op) (hn : noAlt o = true) : (step t o).other = t.other := by
  cases o with
  | scr _ => rfl
  | mode m on =>
    have hm : isAlt m = false := by
      cases hb : isAlt m
      · rfl
      · simp [noAlt, hb] at hn
    exact setMode_other t on hm
  | save => rfl
  | restore => rfl

theorem run_other : ∀ (ops : List Op) (t : T), (∀ o ∈ ops, noAlt o = true) → (run t ops).other = t.other
  | [], _, _ => rfl
  | o :: r, t, hn => by
    have e : run t (o :: r) = run (step t o) r := rfl
    rw [e, run_other r (step t o) (fun o' ho => hn o' (by simp [ho]))]
    exact step_other t o (hn o (by simp))

theorem alt_restore (t : T) (ops : List Op) (h0 : t.other = none) (hn : ∀ o ∈ ops, noAlt o = true) :
    (step (run (step t (.mode 1049 true)) ops) (.mode 1049 false)).scr = t.scr := by
  have e1 : step t (.mode 1049 true) = enter t := by simp [step, setMode, isAlt]
  have e3 : ∀ u : T, step u (.mode 1049 false) = leave u := by
    intro u
    simp [step, setMode, isAlt]
  have o1 : (enter t).other = some t.scr := by simp [enter, h0]
  have o2 : (run (enter t) ops).other = some t.scr := by
    rw [run_other ops (enter t) hn, o1]
  rw [e1, e3]
  simp [leave, o2]

/-! ## 自动换行关掉时不换行 -/

theorem nowrap_y (t : T) (c w : Nat) (ha : t.awm = false) :
    (step t (.scr (.print c w))).scr.y = t.scr.y := by
  show (if t.awm then VtScreen.print t.scr c w else noWrap t.scr c w).y = t.scr.y
  have hn : ¬(t.awm = true) := by rw [ha]; decide
  rw [Lsp.iteF hn]
  unfold noWrap
  by_cases hc : (w = 0 ∨ (w = 2 ∧ t.scr.C < 2))
  · rw [Lsp.iteT hc]
  · rw [Lsp.iteF hc]
    unfold VtScreen.put
    by_cases h2 : t.scr.x + w < t.scr.C
    · rw [Lsp.iteT h2]
      rfl
    · rw [Lsp.iteF h2]
      rfl

/-! ## 例子 -/

def ws (l : List Nat) : List Op := l.map (fun c => .scr (.print c 1))

def line (t : T) (i : Nat) : List Nat := VtScreen.line t.scr i

-- 关掉自动换行：写到最后一列以后都写在最后一列上
#guard (fun t => line t 0 == VtScreen.bs "abd" && line t 1 == VtScreen.bs "   " && t.scr.x == 2)
  (run (init 2 3) ([.mode 7 false] ++ ws (VtScreen.bs "abcd")))
#guard (fun t => line t 1 == VtScreen.bs "d  ") (run (init 2 3) (ws (VtScreen.bs "abcd")))
-- 备用屏幕：进去是空的、光标不动；出来主屏幕原样回来
#guard (fun t => line t 0 == VtScreen.bs "  x" && t.other.isSome)
  (run (init 1 3) (ws (VtScreen.bs "ab") ++ [.mode 1049 true] ++ ws (VtScreen.bs "x")))
#guard (fun t => line t 0 == VtScreen.bs "ab " && t.scr.x == 2 && t.other.isNone)
  (run (init 1 3) (ws (VtScreen.bs "ab") ++ [.mode 1049 true] ++ ws (VtScreen.bs "xyz") ++ [.scr (.ed 2), .mode 1049 false]))
-- 重复进去不会把备用屏幕当成主屏幕存起来；不在里面时出来不动
#guard (fun t => line t 0 == VtScreen.bs "ab ")
  (run (init 1 3) (ws (VtScreen.bs "ab") ++ [.mode 47 true] ++ ws (VtScreen.bs "x") ++ [.mode 1047 true, .mode 1049 false]))
#guard (fun t => line t 0 == VtScreen.bs "ab " && t.other.isNone)
  (run (init 1 3) (ws (VtScreen.bs "ab") ++ [.mode 1049 false]))
-- 保存、恢复光标
#guard (fun t => t.scr.x == 2 && t.scr.y == 0)
  (run (init 2 3) (ws (VtScreen.bs "ab") ++ [.save, .scr (.cup 2 1), .restore]))
-- 光标、括号粘贴；不认识的模式不动
#guard (fun t => !t.tcem && t.paste && t.awm) (run (init 1 1) [.mode 25 false, .mode 2004 true, .mode 12345 false])

end VtMode
end Lark
