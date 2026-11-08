/-
apps/lvm 的证明 · 阶段 2：M:N 调度（好几个工作线程、各自的队列、偷别人的、等待和唤醒、通道）
先证明，再写 apps/lvm/vm/sched.lark。

调度器有 W 个工作线程（worker），每个有：正在跑的线程 run（可能没有）、自己的就绪队列 q（先进先出）。
另外有等着的线程 blocked（等通道、等 join、睡着）和结束了的 done。线程用编号表示。
调度器能做的事（Step）：
- pick：worker 闲着，从自己的队列头上拿一个来跑；
- preempt：时间片用完（VmCore.slice 停在 budget），把正在跑的放回自己队列的尾巴（抢占）；
- block：正在跑的要等（recv 没东西、join 没结束、sleep），放进 blocked；
- finish：正在跑的结束了（halt / fault），放进 done；
- wake：等着的那个能接着跑了（通道来了东西、等的线程结束了、睡够了），放进某个 worker 的队列；
- steal：worker 闲着、自己的队列空了，从别的 worker 队列的头上偷一个（工作窃取）；
另外 spawn 把一个新的线程（编号没用过）放进某个 worker 的队列。

一个线程在几个地方（cnt）：所有 worker 的 run 和 q 里、blocked 里、done 里加起来出现几次。
证明了：
- `step_cnt`：调度器的任何一步，每个线程出现的次数都不变——不会丢，也不会多出一份；
- `spawn_cnt`：spawn 只给那个新线程加一次；
- `reach_inv`：从开始（一个线程 0）经过任何的步骤和 spawn，每个线程最多出现在一个地方；
- `no_double`：所以同一个线程不会同时在两个 worker 上跑（M:N 里最要紧的一条）；
- `alive`：活着（出现一次）的线程走完一步还在；
- `can_move`：只要有一个 worker 在跑线程或者队列不空，调度器就能走一步（不会自己卡住）；
  `steal_ok`：闲着、队列空的 worker，只要别人队列里有，就能偷到；
- 通道：`send_inv`、`recv_inv`、`got_prefix`：收到的正好是发出的那串的开头，按顺序、不丢、不重复。
例子（#guard）里检查了：开始的样子、pick、抢占、偷、等待和唤醒、spawn、通道。
-/
import Lark.Lsp

namespace Lark
namespace VmSched

/-! ## 数一个线程出现了几次 -/

def cnt1 (t : Nat) : List Nat → Nat
  | [] => 0
  | x :: r => (if x = t then 1 else 0) + cnt1 t r

theorem cnt1_app (t : Nat) : ∀ (a b : List Nat), cnt1 t (a ++ b) = cnt1 t a + cnt1 t b
  | [], b => by simp [cnt1]
  | x :: r, b => by
    simp only [List.cons_append, cnt1, cnt1_app t r b] <;> omega

theorem cnt1_one (t x : Nat) : cnt1 t [x] ≤ 1 := by
  simp only [cnt1]
  split <;> omega

structure Wk where
  run : Option Nat
  q : List Nat

def ofRun (t : Nat) : Option Nat → Nat
  | none => 0
  | some x => if x = t then 1 else 0

def cntW (t : Nat) (k : Wk) : Nat := ofRun t k.run + cnt1 t k.q

def upd (f : Nat → Wk) (w : Nat) (k : Wk) : Nat → Wk := fun i => if i = w then k else f i

theorem upd_eq (f : Nat → Wk) (w : Nat) (k : Wk) : upd f w k w = k := by simp [upd]

theorem upd_ne (f : Nat → Wk) {w i : Nat} (k : Wk) (h : i ≠ w) : upd f w k i = f i := by simp [upd, h]

/-- 前 n 个 worker 里出现几次 -/
def sumW (f : Nat → Wk) (t : Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => sumW f t n + cntW t (f n)

theorem sum_out (f : Nat → Wk) (w : Nat) (k : Wk) (t : Nat) : ∀ n, n ≤ w → sumW (upd f w k) t n = sumW f t n
  | 0, _ => rfl
  | n + 1, h => by
    simp only [sumW]
    rw [sum_out f w k t n (by omega), upd_ne f k (show n ≠ w by omega)]

theorem sum_upd (f : Nat → Wk) (w : Nat) (k : Wk) (t : Nat) :
    ∀ n, w < n → sumW (upd f w k) t n + cntW t (f w) = sumW f t n + cntW t k
  | 0, h => absurd h (Nat.not_lt_zero _)
  | n + 1, h => by
    simp only [sumW]
    by_cases hw : w = n
    · subst hw
      rw [sum_out f w k t w (Nat.le_refl _), upd_eq]
      omega
    · rw [upd_ne f k (show n ≠ w from fun e => hw e.symm)]
      have := sum_upd f w k t n (by omega)
      omega

theorem sum_ge1 (f : Nat → Wk) (t w : Nat) : ∀ n, w < n → cntW t (f w) ≤ sumW f t n
  | 0, h => absurd h (Nat.not_lt_zero _)
  | n + 1, h => by
    simp only [sumW]
    by_cases hw : w = n
    · subst hw
      omega
    · have := sum_ge1 f t w n (by omega)
      omega

theorem sum_ge2 (f : Nat → Wk) (t w v : Nat) (hwv : w ≠ v) :
    ∀ n, w < n → v < n → cntW t (f w) + cntW t (f v) ≤ sumW f t n
  | 0, h, _ => absurd h (Nat.not_lt_zero _)
  | n + 1, h1, h2 => by
    simp only [sumW]
    by_cases hw : w = n
    · subst hw
      have := sum_ge1 f t v w (by omega)
      omega
    · by_cases hv : v = n
      · subst hv
        have := sum_ge1 f t w v (by omega)
        omega
      · have := sum_ge2 f t w v hwv n (by omega) (by omega)
        omega

/-! ## 调度器 -/

structure S where
  W : Nat
  ws : Nat → Wk
  blocked : List Nat
  done : List Nat

def cnt (t : Nat) (s : S) : Nat := sumW s.ws t s.W + cnt1 t s.blocked + cnt1 t s.done

def doPick (s : S) (w x : Nat) (r : List Nat) : S := { s with ws := upd s.ws w ⟨some x, r⟩ }
def doPreempt (s : S) (w x : Nat) : S := { s with ws := upd s.ws w ⟨none, (s.ws w).q ++ [x]⟩ }
def doBlock (s : S) (w x : Nat) : S := { s with ws := upd s.ws w ⟨none, (s.ws w).q⟩, blocked := x :: s.blocked }
def doFinish (s : S) (w x : Nat) : S := { s with ws := upd s.ws w ⟨none, (s.ws w).q⟩, done := x :: s.done }
def doWake (s : S) (w : Nat) (pre post : List Nat) (x : Nat) : S :=
  { s with ws := upd s.ws w ⟨(s.ws w).run, (s.ws w).q ++ [x]⟩, blocked := pre ++ post }
def doSteal (s : S) (w v x : Nat) (r : List Nat) : S :=
  { s with ws := upd (upd s.ws v ⟨(s.ws v).run, r⟩) w ⟨none, [x]⟩ }
def doSpawn (s : S) (w x : Nat) : S := { s with ws := upd s.ws w ⟨(s.ws w).run, (s.ws w).q ++ [x]⟩ }

inductive Step : S → S → Prop
  | pick {s : S} {w x : Nat} {r : List Nat} :
      w < s.W → (s.ws w).run = none → (s.ws w).q = x :: r → Step s (doPick s w x r)
  | preempt {s : S} {w x : Nat} : w < s.W → (s.ws w).run = some x → Step s (doPreempt s w x)
  | block {s : S} {w x : Nat} : w < s.W → (s.ws w).run = some x → Step s (doBlock s w x)
  | finish {s : S} {w x : Nat} : w < s.W → (s.ws w).run = some x → Step s (doFinish s w x)
  | wake {s : S} {w x : Nat} {pre post : List Nat} :
      w < s.W → s.blocked = pre ++ x :: post → Step s (doWake s w pre post x)
  | steal {s : S} {w v x : Nat} {r : List Nat} :
      w < s.W → v < s.W → w ≠ v → (s.ws w).run = none → (s.ws w).q = [] → (s.ws v).q = x :: r →
      Step s (doSteal s w v x r)

theorem pick_cnt {s : S} {w x : Nat} {r : List Nat} (t : Nat) (hw : w < s.W)
    (hr : (s.ws w).run = none) (hq : (s.ws w).q = x :: r) : cnt t (doPick s w x r) = cnt t s := by
  show sumW (upd s.ws w ⟨some x, r⟩) t s.W + cnt1 t s.blocked + cnt1 t s.done = _
  have h1 := sum_upd s.ws w ⟨some x, r⟩ t s.W hw
  have h2 : cntW t (s.ws w) = cntW t ⟨some x, r⟩ := by
    simp only [cntW, hr, hq, ofRun, cnt1] <;> omega
  unfold cnt
  omega

theorem preempt_cnt {s : S} {w x : Nat} (t : Nat) (hw : w < s.W) (hr : (s.ws w).run = some x) :
    cnt t (doPreempt s w x) = cnt t s := by
  show sumW (upd s.ws w ⟨none, (s.ws w).q ++ [x]⟩) t s.W + cnt1 t s.blocked + cnt1 t s.done = _
  have h1 := sum_upd s.ws w ⟨none, (s.ws w).q ++ [x]⟩ t s.W hw
  have h2 : cntW t (s.ws w) = cntW t ⟨none, (s.ws w).q ++ [x]⟩ := by
    simp only [cntW, hr, ofRun, cnt1_app, cnt1] <;> omega
  unfold cnt
  omega

theorem block_cnt {s : S} {w x : Nat} (t : Nat) (hw : w < s.W) (hr : (s.ws w).run = some x) :
    cnt t (doBlock s w x) = cnt t s := by
  show sumW (upd s.ws w ⟨none, (s.ws w).q⟩) t s.W + cnt1 t (x :: s.blocked) + cnt1 t s.done = _
  have h1 := sum_upd s.ws w ⟨none, (s.ws w).q⟩ t s.W hw
  have h2 : cntW t (s.ws w) = cntW t ⟨none, (s.ws w).q⟩ + (if x = t then 1 else 0) := by
    simp only [cntW, hr, ofRun] <;> omega
  unfold cnt
  simp only [cnt1]
  omega

theorem finish_cnt {s : S} {w x : Nat} (t : Nat) (hw : w < s.W) (hr : (s.ws w).run = some x) :
    cnt t (doFinish s w x) = cnt t s := by
  show sumW (upd s.ws w ⟨none, (s.ws w).q⟩) t s.W + cnt1 t s.blocked + cnt1 t (x :: s.done) = _
  have h1 := sum_upd s.ws w ⟨none, (s.ws w).q⟩ t s.W hw
  have h2 : cntW t (s.ws w) = cntW t ⟨none, (s.ws w).q⟩ + (if x = t then 1 else 0) := by
    simp only [cntW, hr, ofRun] <;> omega
  unfold cnt
  simp only [cnt1]
  omega

theorem wake_cnt {s : S} {w x : Nat} {pre post : List Nat} (t : Nat) (hw : w < s.W)
    (hb : s.blocked = pre ++ x :: post) : cnt t (doWake s w pre post x) = cnt t s := by
  show sumW (upd s.ws w ⟨(s.ws w).run, (s.ws w).q ++ [x]⟩) t s.W + cnt1 t (pre ++ post) + cnt1 t s.done = _
  have h1 := sum_upd s.ws w ⟨(s.ws w).run, (s.ws w).q ++ [x]⟩ t s.W hw
  have h2 : cntW t ⟨(s.ws w).run, (s.ws w).q ++ [x]⟩ = cntW t (s.ws w) + (if x = t then 1 else 0) := by
    simp only [cntW, cnt1_app, cnt1] <;> omega
  have h3 : cnt1 t s.blocked = cnt1 t (pre ++ post) + (if x = t then 1 else 0) := by
    rw [hb]
    simp only [cnt1_app, cnt1] <;> omega
  unfold cnt
  omega

theorem steal_cnt {s : S} {w v x : Nat} {r : List Nat} (t : Nat) (hw : w < s.W) (hv : v < s.W) (hwv : w ≠ v)
    (hr : (s.ws w).run = none) (hq : (s.ws w).q = []) (hx : (s.ws v).q = x :: r) :
    cnt t (doSteal s w v x r) = cnt t s := by
  show sumW (upd (upd s.ws v ⟨(s.ws v).run, r⟩) w ⟨none, [x]⟩) t s.W + cnt1 t s.blocked + cnt1 t s.done = _
  have h1 := sum_upd (upd s.ws v ⟨(s.ws v).run, r⟩) w ⟨none, [x]⟩ t s.W hw
  have h2 := sum_upd s.ws v ⟨(s.ws v).run, r⟩ t s.W hv
  have e : upd s.ws v ⟨(s.ws v).run, r⟩ w = s.ws w := upd_ne s.ws _ hwv
  rw [e] at h1
  have h3 : cntW t (s.ws w) = 0 := by
    simp only [cntW, hr, hq, ofRun, cnt1] <;> omega
  have h4 : cntW t (s.ws v) = cntW t ⟨(s.ws v).run, r⟩ + (if x = t then 1 else 0) := by
    simp only [cntW, hx, cnt1] <;> omega
  have h5 : cntW t ⟨none, [x]⟩ = (if x = t then 1 else 0) := by
    simp only [cntW, ofRun, cnt1] <;> omega
  unfold cnt
  omega

theorem step_cnt {s s' : S} (h : Step s s') (t : Nat) : cnt t s' = cnt t s := by
  cases h with
  | pick hw hr hq => exact pick_cnt t hw hr hq
  | preempt hw hr => exact preempt_cnt t hw hr
  | block hw hr => exact block_cnt t hw hr
  | finish hw hr => exact finish_cnt t hw hr
  | wake hw hb => exact wake_cnt t hw hb
  | steal hw hv hwv hr hq hx => exact steal_cnt t hw hv hwv hr hq hx

theorem spawn_cnt {s : S} {w x : Nat} (t : Nat) (hw : w < s.W) :
    cnt t (doSpawn s w x) = cnt t s + (if x = t then 1 else 0) := by
  show sumW (upd s.ws w ⟨(s.ws w).run, (s.ws w).q ++ [x]⟩) t s.W + cnt1 t s.blocked + cnt1 t s.done = _
  have h1 := sum_upd s.ws w ⟨(s.ws w).run, (s.ws w).q ++ [x]⟩ t s.W hw
  have h2 : cntW t ⟨(s.ws w).run, (s.ws w).q ++ [x]⟩ = cntW t (s.ws w) + (if x = t then 1 else 0) := by
    simp only [cntW, cnt1_app, cnt1] <;> omega
  unfold cnt
  omega

theorem alive {s s' : S} (h : Step s s') {t : Nat} (ht : cnt t s = 1) : cnt t s' = 1 := by
  rw [step_cnt h t, ht]

/-! ## 从开始走到的状态 -/

def stw (i : Nat) : Wk := if i = 0 then ⟨none, [0]⟩ else ⟨none, []⟩

/-- 开始：W 个 worker，线程 0 在第 0 个的队列里 -/
def start (W : Nat) : S := ⟨W, stw, [], []⟩

inductive Reach : S → Prop
  | init (W : Nat) : Reach (start W)
  | step {s s' : S} : Reach s → Step s s' → Reach s'
  | spawn {s : S} {w x : Nat} : Reach s → w < s.W → cnt x s = 0 → Reach (doSpawn s w x)

def Inv (s : S) : Prop := ∀ t, cnt t s ≤ 1

theorem sum_start (t : Nat) : ∀ n, sumW stw t n ≤ cnt1 t [0]
  | 0 => Nat.zero_le _
  | n + 1 => by
    simp only [sumW]
    by_cases h : n = 0
    · subst h
      simp [sumW, stw, cntW, ofRun]
    · have ih := sum_start t n
      have e : cntW t (stw n) = 0 := by simp [stw, h, cntW, ofRun, cnt1]
      omega

theorem start_inv (W : Nat) : Inv (start W) := by
  intro t
  have h1 := sum_start t W
  have h2 := cnt1_one t 0
  show sumW stw t W + cnt1 t [] + cnt1 t [] ≤ 1
  simp only [cnt1]
  omega

theorem reach_inv {s : S} (h : Reach s) : Inv s := by
  induction h with
  | init W => exact start_inv W
  | step _ hs ih =>
    intro t
    rw [step_cnt hs t]
    exact ih t
  | @spawn s w x _ hw h0 ih =>
    intro t
    rw [spawn_cnt t hw]
    by_cases hx : x = t
    · subst hx
      rw [h0]
      simp
    · have := ih t
      simp only [hx, ↓reduceIte]
      omega

theorem no_double {s : S} (hi : Inv s) {w v t : Nat} (hw : w < s.W) (hv : v < s.W) (hwv : w ≠ v)
    (h1 : (s.ws w).run = some t) (h2 : (s.ws v).run = some t) : False := by
  have hs := sum_ge2 s.ws t w v hwv s.W hw hv
  have a1 : 1 ≤ cntW t (s.ws w) := by simp [cntW, h1, ofRun]
  have a2 : 1 ≤ cntW t (s.ws v) := by simp [cntW, h2, ofRun]
  have := hi t
  unfold cnt at this
  omega

theorem can_move {s : S} {w : Nat} (hw : w < s.W) (h : (s.ws w).run ≠ none ∨ (s.ws w).q ≠ []) :
    ∃ s', Step s s' := by
  cases hr : (s.ws w).run with
  | some x => exact ⟨_, Step.preempt hw hr⟩
  | none =>
    cases hq : (s.ws w).q with
    | nil =>
      rw [hr, hq] at h
      simp at h
    | cons x r => exact ⟨_, Step.pick hw hr hq⟩

theorem steal_ok {s : S} {w v x : Nat} {r : List Nat} (hw : w < s.W) (hv : v < s.W) (hwv : w ≠ v)
    (hr : (s.ws w).run = none) (hq : (s.ws w).q = []) (hx : (s.ws v).q = x :: r) :
    Step s (doSteal s w v x r) := Step.steal hw hv hwv hr hq hx

/-! ## 通道：先进先出 -/

structure Ch where
  sent : List Int
  buf : List Int
  got : List Int
  deriving DecidableEq, Repr

def ChInv (c : Ch) : Prop := c.got ++ c.buf = c.sent

def send (c : Ch) (v : Int) : Ch := { c with sent := c.sent ++ [v], buf := c.buf ++ [v] }
def doRecv (c : Ch) (x : Int) (r : List Int) : Ch := { c with buf := r, got := c.got ++ [x] }

theorem send_inv {c : Ch} (h : ChInv c) (v : Int) : ChInv (send c v) := by
  show c.got ++ (c.buf ++ [v]) = c.sent ++ [v]
  rw [← List.append_assoc, h]

theorem recv_inv {c : Ch} (h : ChInv c) {x : Int} {r : List Int} (hb : c.buf = x :: r) : ChInv (doRecv c x r) := by
  show (c.got ++ [x]) ++ r = c.sent
  rw [List.append_assoc, List.singleton_append, ← hb, h]

theorem got_prefix {c : Ch} (h : ChInv c) : ∃ rest, c.got ++ rest = c.sent := ⟨c.buf, h⟩

/-! ## 例子 -/

#guard cnt 0 (start 4) == 1
#guard cnt 1 (start 4) == 0
-- worker 0 拿线程 0 来跑、spawn 线程 1 到 worker 0、worker 1 偷走线程 1、线程 0 被抢占
def e1 : S := doPick (start 2) 0 0 []
def e2 : S := doSpawn e1 0 1
def e3 : S := doSteal e2 1 0 1 []
def e4 : S := doPreempt e3 0 0
#guard (e1.ws 0).run == some 0
#guard (e3.ws 1).q == [1] && (e3.ws 0).q == []
#guard (e4.ws 0).q == [0]
#guard cnt 0 e4 == 1 && cnt 1 e4 == 1
-- 线程 1 在 worker 1 上跑、要等，再被唤醒到 worker 0
def e5 : S := doBlock (doPick e4 1 1 []) 1 1
def e6 : S := doWake e5 0 [] [] 1
#guard e5.blocked == [1] && e6.blocked == [] && (e6.ws 0).q == [0, 1]
#guard cnt 1 e6 == 1
-- 通道
#guard (doRecv (send (send ⟨[], [], []⟩ 1) 2) 1 [2]).got == [1]

end VmSched
end Lark
