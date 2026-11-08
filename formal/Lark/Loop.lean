/-
Lark 可靠性证明 · 第二部分：循环、break、continue（design/soundness.md 的规则 R12、R13）

在 Core 上加 `loop`（Lark 的 `for { … }`；`for 条件 { … }` 就是 `loop { if 条件 {} else { break } … }`）、`break`、`continue`。
所有权检查 `chkL` 和 own.lark 的 loop_finish 一样：本轮结束时、每个 continue 处，可能被移走的变量不能比进循环时多（R12：
在循环里移走的变量必须在本轮结束前重新赋值）；循环之后的状态是进循环时、本轮结束时、各个 break 处的并（R13）。

循环可能不停，所以语义 `evalL` 带一个燃料 n：用完了返回 out（“还没跑完”），不算出错。
定理 `loop_never_stuck`：通过检查的程序，给多少燃料都不会卡住（读到空位）。
-/
import Lark.Core

namespace Lark

inductive LStmt where
  | skip
  | assign (x : Var) (e : Expr)
  | seq (s t : LStmt)
  | ite (c : Expr) (s t : LStmt)
  | brk
  | cont
  | loop (b : LStmt)
  deriving Repr

/-- 一条语句的结局：正常走完、break、continue、卡住（读到空位）、燃料用完 -/
inductive LRes where
  | ok (σ : Store)
  | brk (σ : Store)
  | cont (σ : Store)
  | stuck
  | out

def LRes.isStuck : LRes → Bool
  | .stuck => true
  | _ => false

def evalL : Nat → LStmt → Store → LRes
  | 0, _, _ => .out
  | _ + 1, .skip, σ => .ok σ
  | _ + 1, .assign x e, σ =>
    match evalE e σ with
    | none => .stuck
    | some (v, σ') => .ok (upd σ' x v)
  | n + 1, .seq s t, σ =>
    match evalL n s σ with
    | .ok σ' => evalL n t σ'
    | .brk σ' => .brk σ'
    | .cont σ' => .cont σ'
    | .stuck => .stuck
    | .out => .out
  | n + 1, .ite c s t, σ =>
    match evalE c σ with
    | none => .stuck
    | some (vc, σ1) => if vc.toInt = 0 then evalL n t σ1 else evalL n s σ1
  | _ + 1, .brk, σ => .brk σ
  | _ + 1, .cont, σ => .cont σ
  | n + 1, .loop b, σ =>
    match evalL n b σ with
    | .ok σ' => evalL n (.loop b) σ'
    | .cont σ' => evalL n (.loop b) σ'
    | .brk σ' => .ok σ'
    | .stuck => .stuck
    | .out => .out

/-! ## 所有权检查：每条语句给出走完时的状态（none 是走不到这里）、各个 break 处和各个 continue 处的状态 -/

structure Out where
  fall : Option (List Var)
  brks : List (List Var)
  conts : List (List Var)
  deriving DecidableEq, Repr

/-- 两个分支走完时的状态的并（own.lark 的 union_st：走不到的一边不算） -/
def joinF : Option (List Var) → Option (List Var) → Option (List Var)
  | none, b => b
  | some a, none => some a
  | some a, some b => some (a ++ b)

def unionAll (l : List (List Var)) : List Var := l.foldr (· ++ ·) []

/-- a 里的变量都在 m 里 -/
def sub (a m : List Var) : Bool := a.all (fun x => decide (x ∈ m))

def subF : Option (List Var) → List Var → Bool
  | none, _ => true
  | some a, m => sub a m

def chkL : LStmt → List Var → Option Out
  | .skip, m => some ⟨some m, [], []⟩
  | .assign x e, m =>
    match chkE e m with
    | none => none
    | some m1 => some ⟨some (m1.filter (fun y => y != x)), [], []⟩
  | .seq s t, m =>
    match chkL s m with
    | none => none
    | some o1 =>
      match o1.fall with
      | none => some o1                       -- 后面走不到，不检查（own_stmt 在 live = false 时直接返回）
      | some m1 =>
        match chkL t m1 with
        | none => none
        | some o2 => some ⟨o2.fall, o1.brks ++ o2.brks, o1.conts ++ o2.conts⟩
  | .ite c s t, m =>
    match chkE c m with
    | none => none
    | some m1 =>
      match chkL s m1, chkL t m1 with
      | some os, some ot => some ⟨joinF os.fall ot.fall, os.brks ++ ot.brks, os.conts ++ ot.conts⟩
      | _, _ => none
  | .brk, m => some ⟨none, [m], []⟩
  | .cont, m => some ⟨none, [], [m]⟩
  | .loop b, m =>
    match chkL b m with
    | none => none
    | some o =>
      -- R12：本轮结束时和每个 continue 处不能比进循环时多移走；R13：之后的状态是几处的并
      if subF o.fall m && o.conts.all (fun c => sub c m) then
        some ⟨some (m ++ o.fall.getD [] ++ unionAll o.brks), [], []⟩
      else none

/-! ## 结局和检查结果对得上：走完、break、continue 时，存储满足对应的状态的不变量；不会卡住 -/

def Good (o : Out) : LRes → Prop
  | .ok σ => ∃ mf, o.fall = some mf ∧ Inv mf σ
  | .brk σ => ∃ mb, mb ∈ o.brks ∧ Inv mb σ
  | .cont σ => ∃ mc, mc ∈ o.conts ∧ Inv mc σ
  | .stuck => False
  | .out => True

theorem sub_inv {a m : List Var} {σ : Store} (h : sub a m = true) (hi : Inv a σ) : Inv m σ := by
  simp only [sub, List.all_eq_true, decide_eq_true_eq] at h
  exact inv_mono h hi

theorem mem_unionAll {l : List (List Var)} {mb : List Var} {x : Var}
    (hm : mb ∈ l) (hx : x ∈ mb) : x ∈ unionAll l := by
  induction l with
  | nil => cases hm
  | cons a l ih =>
    show x ∈ a ++ unionAll l
    rcases List.mem_cons.mp hm with h | h
    · subst h
      exact List.mem_append_left _ hx
    · exact List.mem_append_right _ (ih h)

theorem joinF_left (a : List Var) (b : Option (List Var)) :
    ∃ c, joinF (some a) b = some c ∧ ∀ x, x ∈ a → x ∈ c := by
  cases b with
  | none => exact ⟨a, rfl, fun _ h => h⟩
  | some b => exact ⟨a ++ b, rfl, fun _ h => List.mem_append_left _ h⟩

theorem joinF_right (a : Option (List Var)) (b : List Var) :
    ∃ c, joinF a (some b) = some c ∧ ∀ x, x ∈ b → x ∈ c := by
  cases a with
  | none => exact ⟨b, rfl, fun _ h => h⟩
  | some a => exact ⟨a ++ b, rfl, fun _ h => List.mem_append_right _ h⟩

/-- 分支：一边的结局对得上它自己的检查结果，就对得上两边合并以后的结果 -/
theorem good_branch {os o : Out} {r : LRes}
    (hf : ∀ mf, os.fall = some mf → ∃ mf', o.fall = some mf' ∧ ∀ x, x ∈ mf → x ∈ mf')
    (hb : ∀ mb, mb ∈ os.brks → mb ∈ o.brks)
    (hc : ∀ mc, mc ∈ os.conts → mc ∈ o.conts)
    (g : Good os r) : Good o r := by
  cases r with
  | ok σ =>
    simp only [Good] at g ⊢
    obtain ⟨mf, h1, h2⟩ := g
    obtain ⟨mf', h3, h4⟩ := hf mf h1
    exact ⟨mf', h3, inv_mono h4 h2⟩
  | brk σ =>
    simp only [Good] at g ⊢
    obtain ⟨mb, h1, h2⟩ := g
    exact ⟨mb, hb mb h1, h2⟩
  | cont σ =>
    simp only [Good] at g ⊢
    obtain ⟨mc, h1, h2⟩ := g
    exact ⟨mc, hc mc h1, h2⟩
  | stuck => exact g
  | out => exact g

theorem chkL_sound : ∀ (n : Nat) (s : LStmt) (m : List Var) (o : Out) (σ : Store),
    chkL s m = some o → Inv m σ → Good o (evalL n s σ) := by
  intro n
  induction n with
  | zero =>
    intro s m o σ _ _
    simp [evalL, Good]
  | succ n ih =>
    intro s m o σ h hi
    cases s with
    | skip =>
      simp only [chkL, Option.some.injEq] at h
      subst h
      simp only [evalL, Good]
      exact ⟨m, rfl, hi⟩
    | assign x e =>
      cases he : chkE e m with
      | none => simp [chkL, he] at h
      | some m1 =>
        simp only [chkL, he, Option.some.injEq] at h
        subst h
        obtain ⟨v, σ1, hev, hi1, hv⟩ := chkE_sound e m m1 σ he hi
        simp only [evalL, hev, Good]
        refine ⟨_, rfl, ?_⟩
        intro y hy
        by_cases hyx : y = x
        · subst hyx
          simpa [upd] using hv
        · have hm : y ∉ m1 := by
            intro hm
            apply hy
            simp [List.mem_filter, hm, hyx]
          simpa [upd, hyx] using hi1 y hm
    | seq s t =>
      cases hs : chkL s m with
      | none => simp [chkL, hs] at h
      | some o1 =>
        have g1 := ih s m o1 σ hs hi
        cases hf : o1.fall with
        | none =>
          simp only [chkL, hs, hf, Option.some.injEq] at h
          subst h
          simp only [evalL]
          cases hr : evalL n s σ with
          | ok σ' =>
            rw [hr] at g1
            simp [Good, hf] at g1
          | brk σ' =>
            rw [hr] at g1
            exact g1
          | cont σ' =>
            rw [hr] at g1
            exact g1
          | stuck =>
            rw [hr] at g1
            exact g1
          | out => exact trivial
        | some m1 =>
          cases ht : chkL t m1 with
          | none => simp [chkL, hs, hf, ht] at h
          | some o2 =>
            simp only [chkL, hs, hf, ht, Option.some.injEq] at h
            subst h
            simp only [evalL]
            cases hr : evalL n s σ with
            | ok σ' =>
              rw [hr] at g1
              simp only [Good] at g1
              obtain ⟨mf, hmf, hi'⟩ := g1
              rw [hf] at hmf
              cases hmf
              have g2 := ih t m1 o2 σ' ht hi'
              exact good_branch (os := o2) (fun mf h => ⟨mf, h, fun _ hx => hx⟩)
                (fun _ h => List.mem_append_right _ h) (fun _ h => List.mem_append_right _ h) g2
            | brk σ' =>
              rw [hr] at g1
              simp only [Good] at g1 ⊢
              obtain ⟨mb, h1, h2⟩ := g1
              exact ⟨mb, List.mem_append_left _ h1, h2⟩
            | cont σ' =>
              rw [hr] at g1
              simp only [Good] at g1 ⊢
              obtain ⟨mc, h1, h2⟩ := g1
              exact ⟨mc, List.mem_append_left _ h1, h2⟩
            | stuck =>
              rw [hr] at g1
              exact g1
            | out => exact trivial
    | ite c s t =>
      cases hc : chkE c m with
      | none => simp [chkL, hc] at h
      | some m1 =>
        cases hs : chkL s m1 with
        | none => simp [chkL, hc, hs] at h
        | some os =>
          cases ht : chkL t m1 with
          | none => simp [chkL, hc, hs, ht] at h
          | some ot =>
            simp only [chkL, hc, hs, ht, Option.some.injEq] at h
            subst h
            obtain ⟨vc, σ1, hec, hi1, -⟩ := chkE_sound c m m1 σ hc hi
            simp only [evalL, hec]
            split
            · exact good_branch (os := ot)
                (fun mf h => by
                  simp only [h]
                  exact joinF_right os.fall mf)
                (fun _ h => List.mem_append_right _ h) (fun _ h => List.mem_append_right _ h)
                (ih t m1 ot σ1 ht hi1)
            · exact good_branch (os := os)
                (fun mf h => by
                  simp only [h]
                  exact joinF_left mf ot.fall)
                (fun _ h => List.mem_append_left _ h) (fun _ h => List.mem_append_left _ h)
                (ih s m1 os σ1 hs hi1)
    | brk =>
      simp only [chkL, Option.some.injEq] at h
      subst h
      simp only [evalL, Good]
      exact ⟨m, List.mem_singleton.mpr rfl, hi⟩
    | cont =>
      simp only [chkL, Option.some.injEq] at h
      subst h
      simp only [evalL, Good]
      exact ⟨m, List.mem_singleton.mpr rfl, hi⟩
    | loop b =>
      have hloop := h
      cases hb : chkL b m with
      | none => simp [chkL, hb] at h
      | some ob =>
        simp only [chkL, hb] at h
        split at h
        · rename_i hcond
          simp only [Option.some.injEq] at h
          simp only [Bool.and_eq_true, List.all_eq_true] at hcond
          obtain ⟨hfall, hconts⟩ := hcond
          have g := ih b m ob σ hb hi
          simp only [evalL]
          cases hr : evalL n b σ with
          | ok σ' =>
            rw [hr] at g
            simp only [Good] at g
            obtain ⟨mf, hmf, hi'⟩ := g
            rw [hmf] at hfall
            exact ih (.loop b) m o σ' hloop (sub_inv hfall hi')
          | cont σ' =>
            rw [hr] at g
            simp only [Good] at g
            obtain ⟨mc, hmc, hi'⟩ := g
            exact ih (.loop b) m o σ' hloop (sub_inv (hconts mc hmc) hi')
          | brk σ' =>
            rw [hr] at g
            simp only [Good] at g
            obtain ⟨mb, hmb, hi'⟩ := g
            subst h
            simp only [Good]
            exact ⟨_, rfl, inv_mono (fun x hx => List.mem_append_right _ (mem_unionAll hmb hx)) hi'⟩
          | stuck =>
            rw [hr] at g
            exact g
          | out => exact trivial
        · simp at h

/-- 定理：通过所有权检查的程序（可以有循环、break、continue），给多少燃料都不会读到移走以后留下的空位 -/
theorem loop_never_stuck (n : Nat) (s : LStmt) (m : List Var) (o : Out) (σ : Store)
    (h : chkL s m = some o) (hi : Inv m σ) : evalL n s σ ≠ .stuck := by
  intro he
  have g := chkL_sound n s m o σ h hi
  rw [he] at g
  exact g

/-! ## 例子：和 own.lark 的行为一致 -/

-- 循环里移走、本轮结束前没有重新赋值：报错（R12）
example : chkL (.loop (.ite (.num 1) .brk (.assign 1 (.move 0)))) [] = none := by decide
-- 移走以后 continue：也报错（R12）
example : chkL (.loop (.seq (.assign 1 (.move 0)) .cont)) [] = none := by decide
-- 本轮结束前重新赋值：可以
example : chkL (.loop (.seq (.assign 1 (.move 0)) (.assign 0 (.mk (.num 1))))) [] = some ⟨some [], [], []⟩ := by decide
-- 移走以后 break 出来：循环之后算移走，再用就报错（R13）
example : chkL (.seq (.loop (.seq (.assign 1 (.move 0)) .brk)) (.assign 2 (.copy 0))) [] = none := by decide
-- 不检查的话，第一个例子运行时真的会读到空位：第二轮读 x
example : (evalL 20 (.loop (.seq (.assign 1 (.move 0)) .skip)) (fun _ => .box 7)).isStuck = true := by decide

end Lark
