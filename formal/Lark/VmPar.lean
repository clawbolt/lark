/-
apps/lvm 的证明 · 阶段 4：一次偷一半、有界通道、每个 worker 一把锁（按顺序拿锁，不会死锁）
先证明，再改 apps/lvm/vm/sched.lark。

1. 一次偷一半（stealN）：闲着、队列空了的 worker，把别人队列前面的一段 a（别人的队列是 a ++ b）整段拿过来，
   别人留下 b。实际上 a 是前一半（`half`）。线程多的时候偷的次数少很多。
   证明了 `stealN_cnt`：偷一段时每个线程出现的次数也不变；加上 VmSched 的那几步（Step2），
   `reach2_inv`、`no_double2` 照样成立；`steal_half_ok`：别人队列不空时，偷前一半总能偷到至少一个。
2. 有界通道（BCh）：缓冲最多 cap 个。
   - 有空位时 send 放进缓冲（bsend）；满了 send 的线程等着，它要发的值排在 waitS 里（bwait）；
   - recv 从缓冲头上拿：没人等着发时就是拿走（brecv），有人等着发时顺手把等着的第一个值放进缓冲、
     叫醒那个线程（brefill）；
   - 缓冲是空的、有人在等着收时，send 直接交给它（handoff）；cap 是 0 时（没有缓冲，一手交钱一手交货）
     收的线程直接从等着发的那里拿（takeW）。
   不变式 BInv：收到的 ++ 缓冲 = 发进去的；缓冲不超过 cap；有人等着发时缓冲正好是满的。
   证明了每一步都保持 BInv（`bsend_inv`、`bwait_inv`、`brecv_inv`、`brefill_inv`、`handoff_inv`、`takeW_inv`），
   所以收到的总是发出的那串的开头（`bprefix`）、缓冲不超过 cap（`bbound`）；等着发的值按等的先后进缓冲。
3. 每个 worker 一把锁：共用的状态（等着的线程、通道、结束了的）一把锁，编号 0；worker w 的队列一把，编号 w + 1。
   规定拿着锁时只能再去拿编号更大的锁（实现里：先拿共用的锁再拿某个队列的锁；偷的时候先在别人的锁里拿出来、
   放开以后再拿自己的锁，从来不同时拿两个队列的锁）。
   `no_deadlock`：这样就不会有一圈任务互相等（任务 i 拿着锁 h i、等着下一个任务拿着的锁 h (i + 1)，
   一圈 n 个回到开头 h n = h 0），所以不会死锁。
例子（#guard）里检查了：偷一半、有界通道满了等着、收的时候补上等着的值、没有缓冲的通道。
-/
import Lark.VmSched

namespace Lark
namespace VmPar

open VmSched

/-! ## 一次偷一段 -/

def doStealN (s : S) (w v : Nat) (a b : List Nat) : S :=
  { s with ws := upd (upd s.ws v ⟨(s.ws v).run, b⟩) w ⟨none, a⟩ }

theorem stealN_cnt {s : S} {w v : Nat} {a b : List Nat} (t : Nat) (hw : w < s.W) (hv : v < s.W) (hwv : w ≠ v)
    (hr : (s.ws w).run = none) (hq : (s.ws w).q = []) (hx : (s.ws v).q = a ++ b) :
    cnt t (doStealN s w v a b) = cnt t s := by
  show sumW (upd (upd s.ws v ⟨(s.ws v).run, b⟩) w ⟨none, a⟩) t s.W + cnt1 t s.blocked + cnt1 t s.done = _
  have h1 := sum_upd (upd s.ws v ⟨(s.ws v).run, b⟩) w ⟨none, a⟩ t s.W hw
  have h2 := sum_upd s.ws v ⟨(s.ws v).run, b⟩ t s.W hv
  have e : upd s.ws v ⟨(s.ws v).run, b⟩ w = s.ws w := upd_ne s.ws _ hwv
  rw [e] at h1
  have h3 : cntW t (s.ws w) = 0 := by
    simp only [cntW, hr, hq, ofRun, cnt1] <;> omega
  have h4 : cntW t (s.ws v) = cntW t ⟨(s.ws v).run, b⟩ + cnt1 t a := by
    simp only [cntW, hx, cnt1_app] <;> omega
  have h5 : cntW t ⟨none, a⟩ = cnt1 t a := by
    simp only [cntW, ofRun] <;> omega
  unfold cnt
  omega

inductive Step2 : S → S → Prop
  | base {s s' : S} : Step s s' → Step2 s s'
  | stealN {s : S} {w v : Nat} {a b : List Nat} :
      w < s.W → v < s.W → w ≠ v → (s.ws w).run = none → (s.ws w).q = [] → (s.ws v).q = a ++ b → a ≠ [] →
      Step2 s (doStealN s w v a b)

theorem step2_cnt {s s' : S} (h : Step2 s s') (t : Nat) : cnt t s' = cnt t s := by
  cases h with
  | base h => exact step_cnt h t
  | stealN hw hv hwv hr hq hx _ => exact stealN_cnt t hw hv hwv hr hq hx

inductive Reach2 : S → Prop
  | init (W : Nat) : Reach2 (start W)
  | step {s s' : S} : Reach2 s → Step2 s s' → Reach2 s'
  | spawn {s : S} {w x : Nat} : Reach2 s → w < s.W → cnt x s = 0 → Reach2 (doSpawn s w x)

theorem reach2_inv {s : S} (h : Reach2 s) : Inv s := by
  induction h with
  | init W => exact start_inv W
  | step _ hs ih =>
    intro t
    rw [step2_cnt hs t]
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

theorem no_double2 {s : S} (h : Reach2 s) {w v t : Nat} (hw : w < s.W) (hv : v < s.W) (hwv : w ≠ v)
    (h1 : (s.ws w).run = some t) (h2 : (s.ws v).run = some t) : False :=
  no_double (reach2_inv h) hw hv hwv h1 h2

/-- 偷几个：一半（向上取整） -/
def half (q : List Nat) : Nat := (q.length + 1) / 2

theorem steal_half_ok {s : S} {w v x : Nat} {r : List Nat} (hw : w < s.W) (hv : v < s.W) (hwv : w ≠ v)
    (hr : (s.ws w).run = none) (hq : (s.ws w).q = []) (hx : (s.ws v).q = x :: r) :
    Step2 s (doStealN s w v ((s.ws v).q.take (half (s.ws v).q)) ((s.ws v).q.drop (half (s.ws v).q))) := by
  apply Step2.stealN hw hv hwv hr hq (List.take_append_drop _ _).symm
  rw [hx]
  have e : half (x :: r) = (half (x :: r) - 1) + 1 := by
    simp only [half, List.length_cons]
    omega
  rw [e]
  first
  | exact List.cons_ne_nil _ _
  | simp

/-! ## 有界通道 -/

structure BCh where
  cap : Nat
  sent : List Int
  buf : List Int
  got : List Int
  waitS : List Int
  deriving DecidableEq, Repr

def BInv (c : BCh) : Prop :=
  c.got ++ c.buf = c.sent ∧ c.buf.length ≤ c.cap ∧ (c.waitS ≠ [] → c.buf.length = c.cap)

/-- 有空位：放进缓冲 -/
def bsend (c : BCh) (v : Int) : BCh := { c with sent := c.sent ++ [v], buf := c.buf ++ [v] }
/-- 满了：发的线程等着 -/
def bwait (c : BCh) (v : Int) : BCh := { c with waitS := c.waitS ++ [v] }
/-- 收：没人等着发 -/
def brecv (c : BCh) (x : Int) (r : List Int) : BCh := { c with buf := r, got := c.got ++ [x] }
/-- 收：有人等着发，把它的值补进缓冲 -/
def brefill (c : BCh) (x : Int) (r : List Int) (v : Int) (ws : List Int) : BCh :=
  { c with buf := r ++ [v], sent := c.sent ++ [v], got := c.got ++ [x], waitS := ws }
/-- 缓冲是空的、有人等着收：直接交给它 -/
def handoff (c : BCh) (v : Int) : BCh := { c with sent := c.sent ++ [v], got := c.got ++ [v] }
/-- 缓冲是空的、有人等着发（只有 cap 是 0 时）：收的直接拿 -/
def takeW (c : BCh) (v : Int) (ws : List Int) : BCh :=
  { c with sent := c.sent ++ [v], got := c.got ++ [v], waitS := ws }

theorem bsend_inv {c : BCh} (h : BInv c) (v : Int) (hl : c.buf.length < c.cap) : BInv (bsend c v) := by
  obtain ⟨h1, _, h3⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · show c.got ++ (c.buf ++ [v]) = c.sent ++ [v]
    rw [← List.append_assoc, h1]
  · show (c.buf ++ [v]).length ≤ c.cap
    simp only [List.length_append, List.length_singleton]
    omega
  · intro hw
    have := h3 hw
    omega

theorem bwait_inv {c : BCh} (h : BInv c) (v : Int) (hf : c.buf.length = c.cap) : BInv (bwait c v) :=
  ⟨h.1, h.2.1, fun _ => hf⟩

theorem brecv_inv {c : BCh} (h : BInv c) {x : Int} {r : List Int} (hb : c.buf = x :: r) (hw : c.waitS = []) :
    BInv (brecv c x r) := by
  obtain ⟨h1, h2, _⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · show (c.got ++ [x]) ++ r = c.sent
    rw [List.append_assoc, List.singleton_append, ← hb, h1]
  · show r.length ≤ c.cap
    rw [hb] at h2
    simp only [List.length_cons] at h2
    omega
  · intro hn
    exact absurd hw hn

theorem brefill_inv {c : BCh} (h : BInv c) {x v : Int} {r ws : List Int} (hb : c.buf = x :: r)
    (hw : c.waitS = v :: ws) : BInv (brefill c x r v ws) := by
  obtain ⟨h1, _, h3⟩ := h
  have hc : c.buf.length = c.cap := h3 (by rw [hw]; exact List.cons_ne_nil _ _)
  rw [hb] at hc h1
  simp only [List.length_cons] at hc
  refine ⟨?_, ?_, ?_⟩
  · show (c.got ++ [x]) ++ (r ++ [v]) = c.sent ++ [v]
    rw [← h1]
    simp
  · show (r ++ [v]).length ≤ c.cap
    simp only [List.length_append, List.length_singleton]
    omega
  · intro _
    show (r ++ [v]).length = c.cap
    simp only [List.length_append, List.length_singleton]
    omega

theorem handoff_inv {c : BCh} (h : BInv c) (v : Int) (h0 : c.buf = []) : BInv (handoff c v) := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨?_, h2, h3⟩
  show (c.got ++ [v]) ++ c.buf = c.sent ++ [v]
  rw [h0] at h1 ⊢
  simp only [List.append_nil] at h1 ⊢
  rw [h1]

theorem takeW_inv {c : BCh} (h : BInv c) {v : Int} {ws : List Int} (h0 : c.buf = []) (hw : c.waitS = v :: ws) :
    BInv (takeW c v ws) := by
  obtain ⟨h1, h2, h3⟩ := h
  have hc : c.buf.length = c.cap := h3 (by rw [hw]; exact List.cons_ne_nil _ _)
  refine ⟨?_, h2, fun _ => hc⟩
  show (c.got ++ [v]) ++ c.buf = c.sent ++ [v]
  rw [h0] at h1 ⊢
  simp only [List.append_nil] at h1 ⊢
  rw [h1]

theorem bprefix {c : BCh} (h : BInv c) : ∃ rest, c.got ++ rest = c.sent := ⟨c.buf, h.1⟩

theorem bbound {c : BCh} (h : BInv c) : c.buf.length ≤ c.cap := h.2.1

/-! ## 按顺序拿锁：不会死锁 -/

theorem lock_up (h : Nat → Nat) (hinc : ∀ i, h i < h (i + 1)) : ∀ i, h 0 + i ≤ h i
  | 0 => by omega
  | i + 1 => by
    have := lock_up h hinc i
    have := hinc i
    omega

/-- 一圈 n 个任务，任务 i 拿着锁 h i、等着锁 h (i + 1)（比拿着的大），回到开头：不可能 -/
theorem no_deadlock (h : Nat → Nat) (n : Nat) (hn : 0 < n) (hinc : ∀ i, h i < h (i + 1)) (hcyc : h n = h 0) :
    False := by
  have h1 := lock_up h hinc n
  rw [hcyc] at h1
  exact Nat.lt_irrefl 0 (Nat.lt_of_lt_of_le hn (by omega))

/-! ## 例子 -/

-- worker 0 在跑线程 0，队列里是 1、2、3；worker 1 偷前一半（2 个）
def f1 : S := doSpawn (doSpawn (doSpawn (doPick (start 2) 0 0 []) 0 1) 0 2) 0 3
def f2 : S := doStealN f1 1 0 ((f1.ws 0).q.take (half (f1.ws 0).q)) ((f1.ws 0).q.drop (half (f1.ws 0).q))
#guard (f1.ws 0).q == [1, 2, 3]
#guard (f2.ws 1).q == [1, 2] && (f2.ws 0).q == [3]
#guard cnt 0 f2 == 1 && cnt 1 f2 == 1 && cnt 2 f2 == 1 && cnt 3 f2 == 1

-- 容量 1：发 5 放进缓冲，发 6 满了要等；收到 5 时把 6 补进缓冲
def b0 : BCh := ⟨1, [], [], [], []⟩
def b1 : BCh := bwait (bsend b0 5) 6
def b2 : BCh := brefill b1 5 [] 6 []
#guard b1.buf == [5] && b1.waitS == [6]
#guard b2.got == [5] && b2.buf == [6] && b2.waitS == [] && b2.sent == [5, 6]
-- 容量 0：发 7 的线程等着，收的直接拿
def z1 : BCh := takeW (bwait ⟨0, [], [], [], []⟩ 7) 7 []
#guard z1.got == [7] && z1.sent == [7] && z1.buf == []

end VmPar
end Lark
