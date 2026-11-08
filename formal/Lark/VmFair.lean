/-
apps/lvm 的证明 · 阶段 5：少拿锁（只动自己那个 worker 的步可以各做各的）、select（同时等好几个通道）、公平（不会饿死）
先证明，再改 apps/lvm/vm/sched.lark。

1. 少拿锁：把正在跑的线程（run）也放进 worker 自己的锁里，拿线程（pick）、放回队列尾巴（preempt）只拿自己那一把锁。
   这样做对，是因为这两步只改自己那个 worker（setW），不同 worker 上的这两步谁先谁后结果都一样：
   `upd_comm`、`setW_comm`、`setW_other`、`pick_comm`、`preempt_comm`、`pick_preempt_comm`。
2. select：一个线程同时等好几个通道（cs），排进每个通道的等着收的队列（selBlock）；
   哪个通道先来了东西就被那个叫醒，同时从所有通道的队列里撤掉（selWake）。
   证明了：排进去时只在 cs 里的通道多出现一次（`sel_block_cnt`、`sel_block_keep`）；
   叫醒以后它不在任何一个通道里（`sel_wake_gone`），所以不会被叫醒第二次、不会收走第二个值（`sel_no_twice`）；
   别的线程不受影响（`sel_wake_keep`）。
3. 公平：一个 worker 总是拿队列头上的线程跑，时间片用完放回尾巴（或者等着、结束了就不放回），
   别的线程（唤醒、spawn）只往尾巴上加。队列里排第 k 个（ix，从 0 数）的线程，
   这个 worker 再拿 k + 1 次线程以内一定轮到它（`fair`）——不管中间加进来多少个。
   偷不会让它往后排：被偷走的是前一半，在前一半里的位置不变（`ix_app`），留下的往前挪了（`ix_app_right`）。
例子（#guard）里检查了：两个 worker 的 pick 换个顺序一样、select 叫醒以后哪个通道里都没有它、排第 2 个的第 3 次轮到。
-/
import Lark.VmSched

namespace Lark
namespace VmFair

open VmSched

/-! ## 1. 只动自己那个 worker 的步 -/

def setW (s : S) (w : Nat) (k : Wk) : S := { s with ws := upd s.ws w k }

theorem upd_comm (f : Nat → Wk) {w v : Nat} (k k' : Wk) (h : w ≠ v) :
    upd (upd f w k) v k' = upd (upd f v k') w k := by
  funext i
  simp only [upd]
  by_cases hv : i = v
  · subst hv
    simp [Ne.symm h]
  · by_cases hw : i = w <;> simp [hv, hw, h]

theorem setW_comm (s : S) {w v : Nat} {a b : Wk} (h : w ≠ v) : setW (setW s w a) v b = setW (setW s v b) w a := by
  show ({ s with ws := upd (upd s.ws w a) v b } : S) = { s with ws := upd (upd s.ws v b) w a }
  rw [upd_comm s.ws a b h]

theorem setW_other {s : S} {w v : Nat} {b : Wk} (h : w ≠ v) : (setW s v b).ws w = s.ws w := upd_ne s.ws b h

theorem pick_is (s : S) (w x : Nat) (r : List Nat) : doPick s w x r = setW s w ⟨some x, r⟩ := rfl

theorem preempt_is (s : S) (w x : Nat) : doPreempt s w x = setW s w ⟨none, (s.ws w).q ++ [x]⟩ := rfl

/-- 两个 worker 各自拿线程：谁先谁后一样 -/
theorem pick_comm {s : S} {w v x y : Nat} {r r' : List Nat} (h : w ≠ v) :
    doPick (doPick s w x r) v y r' = doPick (doPick s v y r') w x r := by
  simp only [pick_is]
  exact setW_comm s h

/-- 两个 worker 各自把线程放回自己队列的尾巴：谁先谁后一样 -/
theorem preempt_comm {s : S} {w v x y : Nat} (h : w ≠ v) :
    doPreempt (doPreempt s w x) v y = doPreempt (doPreempt s v y) w x := by
  rw [preempt_is (doPreempt s w x), preempt_is (doPreempt s v y), preempt_is s w, preempt_is s v,
    setW_other (Ne.symm h), setW_other h]
  exact setW_comm s h

/-- 一个拿线程、另一个放回：谁先谁后一样 -/
theorem pick_preempt_comm {s : S} {w v x y : Nat} {r : List Nat} (h : w ≠ v) :
    doPreempt (doPick s w x r) v y = doPick (doPreempt s v y) w x r := by
  rw [preempt_is (doPick s w x r), pick_is (doPreempt s v y), pick_is s w, preempt_is s v,
    setW_other (Ne.symm h)]
  exact setW_comm s h

/-! ## 2. select -/

/-- 从一串里删掉所有的 x -/
def rm (x : Nat) : List Nat → List Nat
  | [] => []
  | h :: r => if h = x then rm x r else h :: rm x r

theorem rm_gone (x : Nat) : ∀ (l : List Nat), cnt1 x (rm x l) = 0
  | [] => rfl
  | h :: r => by
    have ih := rm_gone x r
    by_cases hh : h = x
    · simp [rm, hh, ih]
    · simp [rm, hh, cnt1, ih]

theorem rm_keep {x y : Nat} (hy : y ≠ x) : ∀ (l : List Nat), cnt1 y (rm x l) = cnt1 y l
  | [] => rfl
  | h :: r => by
    have ih := rm_keep hy r
    by_cases hh : h = x
    · subst hh
      simp [rm, cnt1, ih, Ne.symm hy]
    · simp [rm, hh, cnt1, ih]

/-- 线程 x 排进 cs 里每个通道的等着收的队列（rq c 是通道 c 的） -/
def selBlock (rq : Nat → List Nat) (cs : List Nat) (x : Nat) : Nat → List Nat :=
  fun c => if c ∈ cs then rq c ++ [x] else rq c

/-- x 被一个通道叫醒：从所有通道的队列里撤掉 -/
def selWake (rq : Nat → List Nat) (x : Nat) : Nat → List Nat := fun c => rm x (rq c)

theorem sel_block_cnt (rq : Nat → List Nat) (cs : List Nat) (x c : Nat) :
    cnt1 x (selBlock rq cs x c) = cnt1 x (rq c) + (if c ∈ cs then 1 else 0) := by
  unfold selBlock
  by_cases h : c ∈ cs
  · simp [h, cnt1_app, cnt1]
  · simp [h]

theorem sel_block_keep (rq : Nat → List Nat) (cs : List Nat) {x y : Nat} (hy : y ≠ x) (c : Nat) :
    cnt1 y (selBlock rq cs x c) = cnt1 y (rq c) := by
  unfold selBlock
  by_cases h : c ∈ cs
  · simp [h, cnt1_app, cnt1, Ne.symm hy]
  · simp [h]

theorem sel_wake_gone (rq : Nat → List Nat) (x c : Nat) : cnt1 x (selWake rq x c) = 0 := rm_gone x (rq c)

theorem sel_wake_keep (rq : Nat → List Nat) {x y : Nat} (hy : y ≠ x) (c : Nat) :
    cnt1 y (selWake rq x c) = cnt1 y (rq c) := rm_keep hy (rq c)

/-- 排进去、被叫醒一次以后，哪个通道里都没有它：不会被叫醒第二次 -/
theorem sel_no_twice (rq : Nat → List Nat) (cs : List Nat) (x c : Nat) :
    cnt1 x (selWake (selBlock rq cs x) x c) = 0 := sel_wake_gone _ x c

/-! ## 3. 公平 -/

/-- x 在队列里排第几个（从 0 数；不在时是长度） -/
def ix (x : Nat) : List Nat → Nat
  | [] => 0
  | h :: r => if h = x then 0 else ix x r + 1

theorem ix_app (x : Nat) (l : List Nat) : ∀ (q : List Nat), x ∈ q → ix x (q ++ l) = ix x q
  | [], hm => by simp at hm
  | h :: r, hm => by
    by_cases hx : h = x
    · simp [ix, hx]
    · have hr : x ∈ r := by
        rcases List.mem_cons.mp hm with e | e
        · exact absurd e.symm hx
        · exact e
      simp [ix, hx, ix_app x l r hr]

theorem ix_app_right (x : Nat) (b : List Nat) : ∀ (a : List Nat), x ∉ a → ix x (a ++ b) = a.length + ix x b
  | [], _ => by simp
  | h :: r, hm => by
    have hx : h ≠ x := fun e => hm (by rw [← e]; simp)
    have hr : x ∉ r := fun e => hm (by simp [e])
    simp only [List.cons_append, ix, hx, ↓reduceIte, ix_app_right x b r hr, List.length_cons]
    omega

/-- 一个 worker 上发生的事：拿头上的跑一个时间片（放回尾巴 / 不放回），或者别人往尾巴上加一个 -/
inductive QOp where
  | back | gone | add (y : Nat)
  deriving DecidableEq, Repr

/-- 跑完这一串事情的途中，x 有没有被拿出来跑过 -/
def served (x : Nat) : List QOp → List Nat → Bool
  | [], _ => false
  | .add y :: ops, q => served x ops (q ++ [y])
  | .back :: ops, [] => served x ops []
  | .gone :: ops, [] => served x ops []
  | .back :: ops, h :: r => h == x || served x ops (r ++ [h])
  | .gone :: ops, h :: r => h == x || served x ops r

/-- 拿了几次线程 -/
def turns : List QOp → Nat
  | [] => 0
  | .add _ :: ops => turns ops
  | .back :: ops => turns ops + 1
  | .gone :: ops => turns ops + 1

theorem fair (x : Nat) : ∀ (ops : List QOp) (q : List Nat), x ∈ q → ix x q < turns ops → served x ops q = true
  | [], _, _, h => by simp [turns] at h
  | .add y :: ops, q, hm, h => by
    show served x ops (q ++ [y]) = true
    exact fair x ops (q ++ [y]) (List.mem_append_left _ hm) (by rw [ix_app x [y] q hm]; exact h)
  | .back :: _, [], hm, _ => by simp at hm
  | .gone :: _, [], hm, _ => by simp at hm
  | .back :: ops, hd :: r, hm, h => by
    show (hd == x || served x ops (r ++ [hd])) = true
    by_cases hx : hd = x
    · simp [hx]
    · have hr : x ∈ r := by
        rcases List.mem_cons.mp hm with e | e
        · exact absurd e.symm hx
        · exact e
      have hi : ix x (hd :: r) = ix x r + 1 := by simp [ix, hx]
      have ht : ix x r < turns ops := by
        simp only [turns] at h
        omega
      have hb : (hd == x) = false := by simp [hx]
      rw [hb, Bool.false_or]
      exact fair x ops (r ++ [hd]) (List.mem_append_left _ hr) (by rw [ix_app x [hd] r hr]; exact ht)
  | .gone :: ops, hd :: r, hm, h => by
    show (hd == x || served x ops r) = true
    by_cases hx : hd = x
    · simp [hx]
    · have hr : x ∈ r := by
        rcases List.mem_cons.mp hm with e | e
        · exact absurd e.symm hx
        · exact e
      have hi : ix x (hd :: r) = ix x r + 1 := by simp [ix, hx]
      have ht : ix x r < turns ops := by
        simp only [turns] at h
        omega
      have hb : (hd == x) = false := by simp [hx]
      rw [hb, Bool.false_or]
      exact fair x ops r hr ht

/-! ## 例子 -/

-- 两个 worker 各自拿线程，换个顺序一样
def g0 : S := doSpawn (start 2) 1 1
#guard ((doPick (doPick g0 0 0 []) 1 1 []).ws 0).run == some 0
#guard ((doPick (doPick g0 0 0 []) 1 1 []).ws 1).run == ((doPick (doPick g0 1 1 []) 0 0 []).ws 1).run

-- 线程 5 同时等通道 0 和 2，被叫醒以后哪个里面都没有它，别的（线程 7）还在
def rq0 : Nat → List Nat := fun c => if c = 0 then [7] else []
#guard (selBlock rq0 [0, 2] 5 0) == [7, 5] && (selBlock rq0 [0, 2] 5 2) == [5] && (selBlock rq0 [0, 2] 5 1) == []
#guard (selWake (selBlock rq0 [0, 2] 5) 5 0) == [7] && (selWake (selBlock rq0 [0, 2] 5) 5 2) == []

-- 线程 3 排第 2 个：拿第 3 次时轮到它（中间加进来别的也一样）
#guard ix 3 [1, 2, 3] == 2
#guard served 3 [.back, .add 9, .gone] [1, 2, 3] == false
#guard served 3 [.back, .add 9, .gone, .back] [1, 2, 3] == true

end VmFair
end Lark
