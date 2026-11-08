/-
Lark 可靠性证明 · 第一部分：移走以后不能再用（design/soundness.md 的规则 R1、R2、R10、R16）

最小的一块：变量、移走、重新赋值、分支。所有权检查 `chkS` 写成和 compiler/own.lark 一样的可执行函数
（状态是“可能已被移走的变量”的列表，分支之后取并集），运行时的语义 `evalS` 里移走把变量设成空位 ⊥，
读到 ⊥ 就卡住（返回 none）。定理 `no_use_after_move`：通过检查的程序运行时不会卡住。

还没有：循环、调用和借用（inout、排他）、释放（每个值恰好一次）、闭包、defer；按 soundness.md 第 9 节一步步加。
-/
namespace Lark

abbrev Var := Nat

/-- 运行时的值。box 代表不可复制的值（列表、结构体……）；bot 是移走后留下的空位 -/
inductive Val where
  | int (n : Int)
  | box (n : Int)
  | bot
  deriving DecidableEq, Repr

inductive Expr where
  | num (n : Int)
  | copy (x : Var)        -- 读一个可复制的变量
  | peek (x : Var)        -- 借来看（不移走），比如 len(xs)
  | move (x : Var)        -- 移走：之后 x 是空位
  | mk (e : Expr)         -- 新建一个不可复制的值
  | add (a b : Expr)
  | ite (c a b : Expr)    -- c 不为 0 时取 a
  deriving Repr

inductive Stmt where
  | skip
  | assign (x : Var) (e : Expr)
  | seq (s t : Stmt)
  | ite (c : Expr) (s t : Stmt)
  deriving Repr

abbrev Store := Var → Val

def upd (σ : Store) (x : Var) (v : Val) : Store := fun y => if y = x then v else σ y

def Val.toInt : Val → Int
  | .int n => n
  | .box n => n
  | .bot => 0

/-! ## 语义：读到空位就卡住（none） -/

def evalE : Expr → Store → Option (Val × Store)
  | .num n, σ => some (.int n, σ)
  | .copy x, σ => if σ x = .bot then none else some (σ x, σ)
  | .peek x, σ => if σ x = .bot then none else some (.int (σ x).toInt, σ)
  | .move x, σ => if σ x = .bot then none else some (σ x, upd σ x .bot)
  | .mk e, σ =>
    match evalE e σ with
    | none => none
    | some (v, σ') => some (.box v.toInt, σ')
  | .add a b, σ =>
    match evalE a σ with
    | none => none
    | some (va, σ1) =>
      match evalE b σ1 with
      | none => none
      | some (vb, σ2) => some (.int (va.toInt + vb.toInt), σ2)
  | .ite c a b, σ =>
    match evalE c σ with
    | none => none
    | some (vc, σ1) => if vc.toInt = 0 then evalE b σ1 else evalE a σ1

def evalS : Stmt → Store → Option Store
  | .skip, σ => some σ
  | .assign x e, σ =>
    match evalE e σ with
    | none => none
    | some (v, σ') => some (upd σ' x v)
  | .seq s t, σ =>
    match evalS s σ with
    | none => none
    | some σ' => evalS t σ'
  | .ite c s t, σ =>
    match evalE c σ with
    | none => none
    | some (vc, σ1) => if vc.toInt = 0 then evalS t σ1 else evalS s σ1

/-! ## 所有权检查（对应 own.lark 的 own_expr / own_stmt）：none 表示报错 -/

def chkE : Expr → List Var → Option (List Var)
  | .num _, m => some m
  | .copy x, m => if x ∈ m then none else some m                -- R1
  | .peek x, m => if x ∈ m then none else some m                -- R1
  | .move x, m => if x ∈ m then none else some (x :: m)         -- R2
  | .mk e, m => chkE e m
  | .add a b, m =>
    match chkE a m with
    | none => none
    | some m1 => chkE b m1
  | .ite c a b, m =>                                            -- R10：两个分支的并
    match chkE c m with
    | none => none
    | some m1 =>
      match chkE a m1, chkE b m1 with
      | some ma, some mb => some (ma ++ mb)
      | _, _ => none

def chkS : Stmt → List Var → Option (List Var)
  | .skip, m => some m
  | .assign x e, m =>                                           -- R16：重新赋值以后 x 又有值了
    match chkE e m with
    | none => none
    | some m1 => some (m1.filter (fun y => y != x))
  | .seq s t, m =>
    match chkS s m with
    | none => none
    | some m1 => chkS t m1
  | .ite c s t, m =>
    match chkE c m with
    | none => none
    | some m1 =>
      match chkS s m1, chkS t m1 with
      | some ms, some mt => some (ms ++ mt)
      | _, _ => none

/-! ## 不变量：不在 m 里的变量都有值（soundness.md 第 5 节的第 1 条） -/

abbrev Inv (m : List Var) (σ : Store) : Prop := ∀ x, x ∉ m → σ x ≠ .bot

theorem inv_mono {m m' : List Var} {σ : Store} (hs : ∀ x, x ∈ m → x ∈ m') (hi : Inv m σ) : Inv m' σ :=
  fun x hx => hi x (fun h => hx (hs x h))

theorem chkE_sound (e : Expr) : ∀ (m m' : List Var) (σ : Store),
    chkE e m = some m' → Inv m σ →
    ∃ v σ', evalE e σ = some (v, σ') ∧ Inv m' σ' ∧ v ≠ .bot := by
  induction e with
  | num n =>
    intro m m' σ h hi
    simp only [chkE, Option.some.injEq] at h
    subst h
    exact ⟨.int n, σ, rfl, hi, by intro h; cases h⟩
  | copy x =>
    intro m m' σ h hi
    simp only [chkE] at h
    split at h
    · simp at h
    · rename_i hx
      simp only [Option.some.injEq] at h
      subst h
      have hb : σ x ≠ .bot := hi x hx
      exact ⟨σ x, σ, by simp [evalE, hb], hi, hb⟩
  | peek x =>
    intro m m' σ h hi
    simp only [chkE] at h
    split at h
    · simp at h
    · rename_i hx
      simp only [Option.some.injEq] at h
      subst h
      have hb : σ x ≠ .bot := hi x hx
      exact ⟨.int (σ x).toInt, σ, by simp [evalE, hb], hi, by intro h; cases h⟩
  | move x =>
    intro m m' σ h hi
    simp only [chkE] at h
    split at h
    · simp at h
    · rename_i hx
      simp only [Option.some.injEq] at h
      subst h
      have hb : σ x ≠ .bot := hi x hx
      refine ⟨σ x, upd σ x .bot, by simp [evalE, hb], ?_, hb⟩
      intro y hy
      simp only [List.mem_cons, not_or] at hy
      simpa [upd, hy.1] using hi y hy.2
  | mk e ih =>
    intro m m' σ h hi
    simp only [chkE] at h
    obtain ⟨v, σ', he, hi', -⟩ := ih m m' σ h hi
    exact ⟨.box v.toInt, σ', by simp [evalE, he], hi', by intro h; cases h⟩
  | add a b iha ihb =>
    intro m m' σ h hi
    simp only [chkE] at h
    cases ha : chkE a m with
    | none => simp [ha] at h
    | some m1 =>
      simp only [ha] at h
      obtain ⟨va, σ1, hea, hi1, -⟩ := iha m m1 σ ha hi
      obtain ⟨vb, σ2, heb, hi2, -⟩ := ihb m1 m' σ1 h hi1
      exact ⟨.int (va.toInt + vb.toInt), σ2, by simp [evalE, hea, heb], hi2, by intro h; cases h⟩
  | ite c a b ihc iha ihb =>
    intro m m' σ h hi
    simp only [chkE] at h
    cases hc : chkE c m with
    | none => simp [hc] at h
    | some m1 =>
      cases ha : chkE a m1 with
      | none => simp [hc, ha] at h
      | some ma =>
        cases hb : chkE b m1 with
        | none => simp [hc, ha, hb] at h
        | some mb =>
          simp only [hc, ha, hb, Option.some.injEq] at h
          subst h
          obtain ⟨vc, σ1, hec, hi1, -⟩ := ihc m m1 σ hc hi
          by_cases hz : vc.toInt = 0
          · obtain ⟨v, σ2, heb, hi2, hv⟩ := ihb m1 mb σ1 hb hi1
            exact ⟨v, σ2, by simp [evalE, hec, hz, heb], inv_mono (fun x hx => by simp [hx]) hi2, hv⟩
          · obtain ⟨v, σ2, hea, hi2, hv⟩ := iha m1 ma σ1 ha hi1
            exact ⟨v, σ2, by simp [evalE, hec, hz, hea], inv_mono (fun x hx => by simp [hx]) hi2, hv⟩

theorem chkS_sound (s : Stmt) : ∀ (m m' : List Var) (σ : Store),
    chkS s m = some m' → Inv m σ → ∃ σ', evalS s σ = some σ' ∧ Inv m' σ' := by
  induction s with
  | skip =>
    intro m m' σ h hi
    simp only [chkS, Option.some.injEq] at h
    subst h
    exact ⟨σ, rfl, hi⟩
  | assign x e =>
    intro m m' σ h hi
    simp only [chkS] at h
    cases he : chkE e m with
    | none => simp [he] at h
    | some m1 =>
      simp only [he, Option.some.injEq] at h
      subst h
      obtain ⟨v, σ1, hev, hi1, hv⟩ := chkE_sound e m m1 σ he hi
      refine ⟨upd σ1 x v, by simp [evalS, hev], ?_⟩
      intro y hy
      by_cases hyx : y = x
      · subst hyx
        simpa [upd] using hv
      · have hm : y ∉ m1 := by
          intro hm
          apply hy
          simp [List.mem_filter, hm, hyx]
        simpa [upd, hyx] using hi1 y hm
  | seq s t ihs iht =>
    intro m m' σ h hi
    simp only [chkS] at h
    cases hs : chkS s m with
    | none => simp [hs] at h
    | some m1 =>
      simp only [hs] at h
      obtain ⟨σ1, hes, hi1⟩ := ihs m m1 σ hs hi
      obtain ⟨σ2, het, hi2⟩ := iht m1 m' σ1 h hi1
      exact ⟨σ2, by simp [evalS, hes, het], hi2⟩
  | ite c s t ihs iht =>
    intro m m' σ h hi
    simp only [chkS] at h
    cases hc : chkE c m with
    | none => simp [hc] at h
    | some m1 =>
      cases hs : chkS s m1 with
      | none => simp [hc, hs] at h
      | some ms =>
        cases ht : chkS t m1 with
        | none => simp [hc, hs, ht] at h
        | some mt =>
          simp only [hc, hs, ht, Option.some.injEq] at h
          subst h
          obtain ⟨vc, σ1, hec, hi1, -⟩ := chkE_sound c m m1 σ hc hi
          by_cases hz : vc.toInt = 0
          · obtain ⟨σ2, het, hi2⟩ := iht m1 mt σ1 ht hi1
            exact ⟨σ2, by simp [evalS, hec, hz, het], inv_mono (fun x hx => by simp [hx]) hi2⟩
          · obtain ⟨σ2, hes, hi2⟩ := ihs m1 ms σ1 hs hi1
            exact ⟨σ2, by simp [evalS, hec, hz, hes], inv_mono (fun x hx => by simp [hx]) hi2⟩

/-- 定理：通过所有权检查的程序运行时不会卡住（唯一会卡住的情况是读到移走以后留下的空位）。
    m 是开始时没有值的变量，σ 是开始时的存储 -/
theorem no_use_after_move (s : Stmt) (m m' : List Var) (σ : Store)
    (h : chkS s m = some m') (hi : Inv m σ) : evalS s σ ≠ none := by
  obtain ⟨σ', he, -⟩ := chkS_sound s m m' σ h hi
  simp [he]

/-! ## 例子：检查器的行为和 own.lark 一致 -/

-- 移走以后再读：报错（R1）
example : chkS (.seq (.assign 1 (.move 0)) (.assign 2 (.copy 0))) [] = none := by decide
-- 只在一个分支里移走，之后也算移走（R10）
example : chkS (.seq (.ite (.num 1) (.assign 1 (.move 0)) .skip) (.assign 2 (.copy 0))) [] = none := by decide
-- 重新赋值以后又能用（R16）
example : chkS (.seq (.assign 1 (.move 0)) (.seq (.assign 0 (.num 5)) (.assign 2 (.copy 0)))) [] = some [] := by decide
-- 不检查的话，同一个程序运行时真的会读到空位
example : (evalS (.seq (.assign 1 (.move 0)) (.assign 2 (.copy 0))) (fun _ => .int 0)).isNone = true := by decide

end Lark
