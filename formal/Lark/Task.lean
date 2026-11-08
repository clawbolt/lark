/-
Lark 可靠性证明 · 第五部分：并发没有数据竞争（design/soundness.md 第 6 节）

scope 块结束前（以及从块里跳出去之前）等它 spawn 的任务都结束，所以程序的并发结构是“分叉—汇合”的：
fork xs s t 表示 scope { spawn(f, xs)；t }，新任务运行 s，拿到移进去的变量 xs；当前任务接着运行 t；两边都结束才往下走。
这种结构下，两次访问可能同时发生，当且仅当它们分别在某个 fork 的两边（分叉—汇合程序的标准定义）。
数据竞争：同时发生的两次访问碰同一个变量，至少一次是写，而且没有同时拿着同一把锁。

任务之间能碰同一个变量的方式只有：自己拥有的（own，spawn 移进来的）、shared（sh，只读）、Mutex（mx，只能在 lock 块里访问）。
检查 `chk` 对应 own.lark 的 spawn 规则和“Mutex 只能在 lock 里用”：
- 读：自己拥有的、shared 的，或者正拿着锁的 Mutex；写：自己拥有的，或者正拿着锁的 Mutex
- spawn 移走的变量当前任务不能再用；新任务不继承当前任务拿着的锁

定理 `race_free`：own、sh、mx 互不相交时，通过检查的程序没有数据竞争。
不在模型里：Chan（send 把值移进去、recv 移出来，是运行时转移所有权，要带交错执行的语义才能证）；
引用计数在有任务时用原子操作（A6，属于运行时实现）。
-/
import Lark.Core

namespace Lark
namespace Task

inductive TS where
  | rd (x : Var)
  | wr (x : Var)
  | seq (s t : TS)
  | lock (m : Var) (s : TS)
  | fork (xs : List Var) (s t : TS)
  deriving Repr

/-- 一次访问：哪个变量、是不是写、当时拿着哪些锁 -/
structure Acc where
  x : Var
  w : Bool
  held : List Var

/-- 程序运行时的所有访问；新任务从不拿锁开始 -/
def fp (held : List Var) : TS → List Acc
  | .rd x => [⟨x, false, held⟩]
  | .wr x => [⟨x, true, held⟩]
  | .seq s t => fp held s ++ fp held t
  | .lock m s => fp (m :: held) s
  | .fork _ s t => fp [] s ++ fp held t

def Conflict (a b : Acc) : Prop :=
  a.x = b.x ∧ (a.w = true ∨ b.w = true) ∧ ∀ m, m ∈ a.held → m ∉ b.held

/-- 没有数据竞争：每个 fork 两边的访问两两不冲突 -/
def RaceFree : List Var → TS → Prop
  | _, .rd _ => True
  | _, .wr _ => True
  | held, .seq s t => RaceFree held s ∧ RaceFree held t
  | held, .lock m s => RaceFree (m :: held) s
  | held, .fork _ s t => RaceFree [] s ∧ RaceFree held t ∧
      ∀ a, a ∈ fp [] s → ∀ b, b ∈ fp held t → ¬ Conflict a b

def chk (own sh mx held : List Var) : TS → Bool
  | .rd x => decide (x ∈ own) || (decide (x ∈ sh) || (decide (x ∈ held) && decide (x ∈ mx)))
  | .wr x => decide (x ∈ own) || (decide (x ∈ held) && decide (x ∈ mx))
  | .seq s t => chk own sh mx held s && chk own sh mx held t
  | .lock m s => decide (m ∈ mx) && chk own sh mx (m :: held) s
  | .fork xs s t => xs.all (fun x => decide (x ∈ own)) && chk xs sh mx [] s &&
      chk (own.filter (fun y => !decide (y ∈ xs))) sh mx held t

/-! ## 证明 -/

/-- 通过检查的程序的每次访问：是自己拥有的，或者是读 shared，或者拿着这个 Mutex 的锁 -/
theorem acc_ok (sh mx : List Var) (s : TS) : ∀ (own held : List Var), chk own sh mx held s = true →
    ∀ a, a ∈ fp held s → a.x ∈ own ∨ (a.w = false ∧ a.x ∈ sh) ∨ (a.x ∈ a.held ∧ a.x ∈ mx) := by
  induction s with
  | rd x =>
    intro own held h a ha
    simp only [chk, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
    simp only [fp, List.mem_singleton] at ha
    subst ha
    rcases h with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl ⟨rfl, h⟩)
    · exact Or.inr (Or.inr h)
  | wr x =>
    intro own held h a ha
    simp only [chk, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
    simp only [fp, List.mem_singleton] at ha
    subst ha
    rcases h with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr h)
  | seq s t ihs iht =>
    intro own held h a ha
    simp only [chk, Bool.and_eq_true] at h
    simp only [fp, List.mem_append] at ha
    rcases ha with ha | ha
    · exact ihs own held h.1 a ha
    · exact iht own held h.2 a ha
  | lock m s ih =>
    intro own held h a ha
    simp only [chk, Bool.and_eq_true] at h
    exact ih own (m :: held) h.2 a ha
  | fork xs s t ihs iht =>
    intro own held h a ha
    simp only [chk, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨hsub, hs⟩, ht⟩ := h
    simp only [fp, List.mem_append] at ha
    rcases ha with ha | ha
    · rcases ihs xs [] hs a ha with h1 | h1 | h1
      · exact Or.inl (hsub _ h1)
      · exact Or.inr (Or.inl h1)
      · exact Or.inr (Or.inr h1)
    · rcases iht _ held ht a ha with h1 | h1 | h1
      · exact Or.inl (List.mem_filter.mp h1).1
      · exact Or.inr (Or.inl h1)
      · exact Or.inr (Or.inr h1)

/-- 定理：own、shared、Mutex 三类变量互不相交时，通过检查的程序没有数据竞争 -/
theorem race_free (sh mx : List Var) (s : TS) : ∀ (own held : List Var),
    (∀ x, x ∈ own → x ∉ sh) → (∀ x, x ∈ own → x ∉ mx) → (∀ x, x ∈ sh → x ∉ mx) →
    chk own sh mx held s = true → RaceFree held s := by
  induction s with
  | rd x => intros; trivial
  | wr x => intros; trivial
  | seq s t ihs iht =>
    intro own held d1 d2 d3 h
    simp only [chk, Bool.and_eq_true] at h
    exact ⟨ihs own held d1 d2 d3 h.1, iht own held d1 d2 d3 h.2⟩
  | lock m s ih =>
    intro own held d1 d2 d3 h
    simp only [chk, Bool.and_eq_true] at h
    exact ih own (m :: held) d1 d2 d3 h.2
  | fork xs s t ihs iht =>
    intro own held d1 d2 d3 h
    simp only [chk, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨hsub, hs⟩, ht⟩ := h
    have f1 : ∀ x, x ∈ own.filter (fun y => !decide (y ∈ xs)) → x ∈ own ∧ x ∉ xs := by
      intro x hx
      simpa [List.mem_filter] using hx
    refine ⟨ihs xs [] (fun x hx => d1 x (hsub x hx)) (fun x hx => d2 x (hsub x hx)) d3 hs,
      iht _ held (fun x hx => d1 x (f1 x hx).1) (fun x hx => d2 x (f1 x hx).1) d3 ht, ?_⟩
    intro a ha b hb hc
    obtain ⟨hx, hw, hl⟩ := hc
    rcases acc_ok sh mx s xs [] hs a ha with h1 | ⟨w1, s1⟩ | ⟨l1, m1⟩ <;>
    rcases acc_ok sh mx t _ held ht b hb with h2 | ⟨w2, s2⟩ | ⟨l2, m2⟩
    -- 两边都是自己拥有的：spawn 移走的变量当前任务不能再用
    · exact (f1 _ h2).2 (by rw [← hx]; exact h1)
    · exact d1 _ (hsub _ h1) (by rw [hx]; exact s2)
    · exact d2 _ (hsub _ h1) (by rw [hx]; exact m2)
    · exact d1 _ (f1 _ h2).1 (by rw [← hx]; exact s1)
    -- 两边都读 shared：都不是写
    · rw [w1, w2] at hw
      simp at hw
    · exact d3 _ s1 (by rw [hx]; exact m2)
    · exact d2 _ (f1 _ h2).1 (by rw [← hx]; exact m1)
    · exact d3 _ s2 (by rw [← hx]; exact m1)
    -- 两边都是 Mutex：都拿着这把锁
    · exact hl _ l1 (by rw [hx]; exact l2)

/-! ## 例子 -/

-- 新任务和当前任务都写 x0：x0 移进新任务以后当前任务不能再用
example : chk [0] [] [] [] (.fork [0] (.wr 0) (.wr 0)) = false := by decide
-- 不检查的话真的有竞争
example : ¬ RaceFree [] (.fork [] (.wr 0) (.wr 0)) := by
  intro h
  simp only [RaceFree] at h
  exact h.2.2 ⟨0, true, []⟩ (by simp [fp]) ⟨0, true, []⟩ (by simp [fp]) (by simp [Conflict])
-- 各写各的：可以
example : chk [0, 1] [] [] [] (.fork [0] (.wr 0) (.wr 1)) = true := by decide
-- 两边都读 shared：可以；写 shared：不行
example : chk [] [1] [] [] (.fork [] (.rd 1) (.rd 1)) = true := by decide
example : chk [] [1] [] [] (.fork [] (.wr 1) (.rd 1)) = false := by decide
-- 两边都在 lock 里写 Mutex：可以；不加锁：不行
example : chk [] [] [5] [] (.fork [] (.lock 5 (.wr 5)) (.lock 5 (.wr 5))) = true := by decide
example : chk [] [] [5] [] (.fork [] (.wr 5) (.lock 5 (.wr 5))) = false := by decide
-- 在 lock 里 spawn：新任务不拿着这把锁
example : chk [] [] [5] [] (.lock 5 (.fork [] (.wr 5) (.wr 5))) = false := by decide

end Task
end Lark
