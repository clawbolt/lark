/-
apps/lvm 的证明 · 阶段 6：睡着的线程按到期时间排好（堆），select 可以带超时
先证明，再改 apps/lvm/vm/sched.lark。

1. 定时器：睡着的线程按到期的时间排好（Sorted），每次只从头上拿到期了的（due），不用把所有睡着的都看一遍。
   实现里用 std/heap 的二叉堆（每次拿最小的），模型里用排好序的列表（ins 插到该在的地方）。
   证明了：插进去以后还是排好的（`ins_sorted`），插进去的就是原来的加上新的（`ins_mem`）；
   拿出来的都到期了（`due_ok`），剩下的都没到期（`due_rest`），拿出来的和剩下的合起来正好是原来的（`due_split`）——
   和原来把所有睡着的都看一遍（filter）结果一样，不会漏叫醒、也不会叫早了。
2. 带超时的 select（tselect）：线程同时排进几个通道和定时器。哪边先来就被哪边叫醒：
   - 通道先来：照 VmFair 的 selWake 从所有通道撤掉；定时器里那一项留着（在堆里删一项不方便），到期时再扔掉；
   - 定时器先到：照 selWake 从所有通道撤掉，返回"超时"。
   为了认出留着的旧项，每次等都发一个新的编号（wblock），叫醒时编号对得上才算（wwake）。
   证明了：同一次等只会被叫醒一次（`wake_once`）；上一次等留下的旧项叫不醒这一次（`stale_ignored`）；
   编号总是比发出去的都大，所以新发的不会和旧的重复（`wblock_fresh`）。
例子（#guard）里检查了：插进去的顺序、拿到期的、定时器先到 / 通道先来两种情况。
-/
import Lark.VmSched

namespace Lark
namespace VmTimer

/-! ## 1. 按到期时间排好的定时器（到期时间, 线程） -/

def Sorted : List (Nat × Nat) → Prop
  | [] => True
  | a :: r => (∀ b ∈ r, a.1 ≤ b.1) ∧ Sorted r

def ins (x : Nat × Nat) : List (Nat × Nat) → List (Nat × Nat)
  | [] => [x]
  | y :: r => if x.1 < y.1 then x :: y :: r else y :: ins x r

theorem ins_mem (x b : Nat × Nat) : ∀ (l : List (Nat × Nat)), b ∈ ins x l → b = x ∨ b ∈ l
  | [], h => by
    simp [ins] at h
    exact Or.inl h
  | y :: r, h => by
    unfold ins at h
    split at h
    · simp at h
      rcases h with e | e | e
      · exact Or.inl e
      · exact Or.inr (by simp [e])
      · exact Or.inr (by simp [e])
    · simp at h
      rcases h with e | e
      · exact Or.inr (by simp [e])
      · rcases ins_mem x b r e with e2 | e2
        · exact Or.inl e2
        · exact Or.inr (by simp [e2])

theorem ins_sorted (x : Nat × Nat) : ∀ (l : List (Nat × Nat)), Sorted l → Sorted (ins x l)
  | [], _ => by simp [ins, Sorted]
  | y :: r, h => by
    simp only [Sorted] at h
    obtain ⟨hy, hr⟩ := h
    unfold ins
    split
    · simp only [Sorted]
      refine ⟨?_, hy, hr⟩
      intro b hb
      simp at hb
      rcases hb with e | e
      · rw [e]
        omega
      · have := hy b e
        omega
    · simp only [Sorted]
      refine ⟨?_, ins_sorted x r hr⟩
      intro b hb
      rcases ins_mem x b r hb with e | e
      · rw [e]
        omega
      · exact hy b e

/-- 从头上拿到期了的（到期时间 ≤ now）：(拿出来的, 剩下的) -/
def due (now : Nat) : List (Nat × Nat) → List (Nat × Nat) × List (Nat × Nat)
  | [] => ([], [])
  | a :: r => if a.1 ≤ now then (a :: (due now r).1, (due now r).2) else ([], a :: r)

theorem due_ok (now : Nat) : ∀ (l : List (Nat × Nat)), ∀ b ∈ (due now l).1, b.1 ≤ now
  | [], b, hb => by simp [due] at hb
  | a :: r, b, hb => by
    unfold due at hb
    split at hb
    · rename_i ha
      simp at hb
      rcases hb with e | e
      · rw [e]
        exact ha
      · exact due_ok now r b e
    · simp at hb

theorem due_rest (now : Nat) : ∀ (l : List (Nat × Nat)), Sorted l → ∀ b ∈ (due now l).2, now < b.1
  | [], _, b, hb => by simp [due] at hb
  | a :: r, h, b, hb => by
    simp only [Sorted] at h
    obtain ⟨ha, hr⟩ := h
    unfold due at hb
    split at hb
    · exact due_rest now r hr b hb
    · simp at hb
      rcases hb with e | e
      · rw [e]
        omega
      · have := ha b e
        omega

theorem due_split (now : Nat) : ∀ (l : List (Nat × Nat)), (due now l).1 ++ (due now l).2 = l
  | [] => rfl
  | a :: r => by
    unfold due
    split
    · simp [due_split now r]
    · rfl

/-! ## 2. 每次等一个新编号：旧的定时器项叫不醒 -/

structure Wt where
  cur : Option Nat      -- 正在等的那一次的编号（没在等时是 none）
  next : Nat            -- 下一次等用的编号
  deriving DecidableEq, Repr

/-- 开始等：发一个新编号 -/
def wblock (s : Wt) : Wt := ⟨some s.next, s.next + 1⟩

/-- 带着编号 id 来叫醒：对得上才叫醒（返回 true），之后就不在等了 -/
def wwake (s : Wt) (id : Nat) : Bool × Wt :=
  if s.cur = some id then (true, { s with cur := none }) else (false, s)

theorem wake_once (s : Wt) (id : Nat) : (wwake (wwake s id).2 id).1 = false := by
  unfold wwake
  by_cases h : s.cur = some id <;> simp [h]

theorem stale_ignored (s : Wt) {id : Nat} (h : id < s.next) : (wwake (wblock s) id).1 = false := by
  unfold wwake wblock
  split
  · rename_i he
    simp at he
    exact absurd he (by omega)
  · rfl

theorem wblock_fresh (s : Wt) : (wblock s).next > s.next ∧ (wblock s).cur = some s.next := by
  simp [wblock]

/-! ## 例子 -/

#guard ins (5, 1) (ins (3, 2) (ins (9, 3) [])) == [(3, 2), (5, 1), (9, 3)]
#guard due 5 [(3, 2), (5, 1), (9, 3)] == ([(3, 2), (5, 1)], [(9, 3)])
#guard due 2 [(3, 2), (5, 1), (9, 3)] == ([], [(3, 2), (5, 1), (9, 3)])
-- 定时器先到：叫醒；之后通道带着同一个编号来，叫不醒
def w1 : Wt := wblock ⟨none, 0⟩
#guard (wwake w1 0).1 == true && (wwake (wwake w1 0).2 0).1 == false
-- 通道先来叫醒了，线程又等了一次（编号 1）：旧的定时器项（编号 0）叫不醒这一次
def w2 : Wt := wblock (wwake w1 0).2
#guard (wwake w2 0).1 == false && (wwake w2 1).1 == true

end VmTimer
end Lark
