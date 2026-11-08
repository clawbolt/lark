/-
Lark 可靠性证明 · 第六部分：Chan（design/soundness.md 第 6 节）

Task.lean 用分叉—汇合的结构证了 shared 和 Mutex，但 Chan 是运行时转移所有权：
任务 A send 一个盒子，任务 B 什么时候 recv 到取决于调度。这里换成交错执行的语义：
每一步挑一个任务，执行它的下一条指令；recv 时通道是空的就等着（这一步走不了）。

为了看清检查做了什么，运行时故意不清零：send、mov 只复制地址，原来的变量里还留着（像 C 里的指针）。
另外记一个“所有者”（own）：每个盒子属于哪个任务，或者在哪个通道里排队，或者已经释放。
所有者只在 new、send、recv、drop 时改变，send / recv 是同步点（recv 一定发生在对应的 send 之后）。

定理 `chan_race_free`：每个任务的程序都通过检查时，任何调度下任何时刻，任务碰（use、send、drop）的盒子都属于它自己。
所以同一个盒子被两个任务碰到的话，中间一定隔着把它转过去的 send 和 recv，两次访问有先后，不会同时发生。
不检查的话，send 之后还用原来的变量，就和收到它的任务同时碰同一个盒子（例子）。
-/
import Lark.Core

namespace Lark
namespace Chan

inductive Ins where
  | new (x : Var)
  | use (x : Var)
  | mov (y x : Var)
  | send (c : Nat) (x : Var)
  | recv (c : Nat) (x : Var)
  | drop (x : Var)
  deriving Repr

inductive Loc where
  | task (i : Nat)
  | chan (c : Nat)
  | free
  deriving DecidableEq, Repr

structure S where
  prog : Nat → List Ins
  st : Nat → Var → Option Nat
  q : Nat → List Nat
  own : Nat → Loc
  next : Nat

def put {α : Type} (f : Nat → α) (k : Nat) (v : α) : Nat → α := fun j => if j = k then v else f j

def step (i : Nat) (s : S) : Option S :=
  match s.prog i with
  | [] => none
  | .new x :: p => some { s with prog := put s.prog i p, st := put s.st i (put (s.st i) x (some s.next)), own := put s.own s.next (.task i), next := s.next + 1 }
  | .use x :: p =>
    match s.st i x with
    | none => none
    | some _ => some { s with prog := put s.prog i p }
  | .mov y x :: p => some { s with prog := put s.prog i p, st := put s.st i (put (s.st i) y (s.st i x)) }
  | .send c x :: p =>
    match s.st i x with
    | none => none
    | some a => some { s with prog := put s.prog i p, q := put s.q c (s.q c ++ [a]), own := put s.own a (.chan c) }
  | .recv c x :: p =>
    match s.q c with
    | [] => none
    | a :: r => some { s with prog := put s.prog i p, st := put s.st i (put (s.st i) x (some a)), q := put s.q c r, own := put s.own a (.task i) }
  | .drop x :: p =>
    match s.st i x with
    | none => none
    | some a => some { s with prog := put s.prog i p, own := put s.own a .free }

/-- 哪些指令碰盒子 -/
def touch : Ins → Option Var
  | .use x => some x
  | .send _ x => some x
  | .drop x => some x
  | _ => none

/-- 任务 i 下一条指令碰的盒子属于它自己 -/
def safe (i : Nat) (s : S) : Bool :=
  match s.prog i with
  | [] => true
  | ins :: _ =>
    match touch ins with
    | none => true
    | some x =>
      match s.st i x with
      | none => false
      | some a => decide (s.own a = .task i)

/-! ## 检查：F x 表示 x 现在有值（和 own.lark 一样，按顺序记哪些变量被移走了） -/

def setF (F : Var → Bool) (x : Var) (b : Bool) : Var → Bool := fun y => if y = x then b else F y

def chk (F : Var → Bool) : List Ins → Bool
  | [] => true
  | .new x :: p => !F x && chk (setF F x true) p
  | .use x :: p => F x && chk F p
  | .mov y x :: p => F x && !F y && chk (setF (setF F x false) y true) p
  | .send _ x :: p => F x && chk (setF F x false) p          -- send 把 x 移走
  | .recv _ x :: p => !F x && chk (setF F x true) p
  | .drop x :: p => F x && chk (setF F x false) p

def init (P : Nat → List Ins) : S := ⟨P, fun _ _ => none, fun _ => [], fun _ => .free, 0⟩

inductive Reach (s0 : S) : S → Prop
  | refl : Reach s0 s0
  | go {s s' : S} (i : Nat) : Reach s0 s → Lark.Chan.step i s = some s' → Reach s0 s'

/-! ## 不变量

- tasks：每个任务剩下的程序能通过检查，检查认为有值的变量装的盒子属于这个任务，而且各装各的
- chans：通道里排队的盒子属于这个通道，同一个盒子不会排两次
- fresh：没释放的盒子地址都小于 next -/

theorem put_same {α : Type} (f : Nat → α) (k : Nat) (v : α) : put f k v k = v := by simp [put]

theorem put_ne {α : Type} (f : Nat → α) {k j : Nat} (v : α) (h : j ≠ k) : put f k v j = f j := by
  simp [put, h]

theorem setF_false {F : Var → Bool} {x z : Var} (h : setF F x false z = true) : z ≠ x ∧ F z = true := by
  by_cases hzx : z = x
  · simp [setF, hzx] at h
  · exact ⟨hzx, by simpa [setF, hzx] using h⟩

theorem setF_true {F : Var → Bool} {x z : Var} (h : setF F x true z = true) (hzx : z ≠ x) : F z = true := by
  simpa [setF, hzx] using h

def Dist : List Nat → Prop
  | [] => True
  | a :: l => a ∉ l ∧ Dist l

theorem dist_snoc : ∀ (l : List Nat) (a : Nat), Dist l → a ∉ l → Dist (l ++ [a])
  | [], a, _, _ => by simp [Dist]
  | b :: l, a, h, ha => by
    simp only [Dist] at h
    simp only [List.cons_append, Dist]
    refine ⟨?_, dist_snoc l a h.2 (fun hm => ha (by simp [hm]))⟩
    intro hm
    simp only [List.mem_append, List.mem_singleton] at hm
    rcases hm with hm | hm
    · exact h.1 hm
    · exact ha (by simp [hm])

abbrev TaskOk (s : S) (i : Nat) (F : Var → Bool) : Prop :=
  (∀ x, F x = true → ∃ a, s.st i x = some a ∧ s.own a = .task i) ∧
  (∀ x y a, F x = true → F y = true → s.st i x = some a → s.st i y = some a → x = y)

structure Inv (s : S) : Prop where
  tasks : ∀ i, ∃ F, chk F (s.prog i) = true ∧ TaskOk s i F
  chans : ∀ c a, a ∈ s.q c → s.own a = .chan c
  dist : ∀ c, Dist (s.q c)
  fresh : ∀ a, s.own a ≠ .free → a < s.next

theorem other_ok {s s' : S} {j : Nat} {F : Var → Bool} (hst : s'.st j = s.st j)
    (hown : ∀ b, s.own b = .task j → s'.own b = .task j) (h : TaskOk s j F) : TaskOk s' j F := by
  refine ⟨fun x hx => ?_, fun x y a hx hy h1 h2 => ?_⟩
  · obtain ⟨a, h1, h2⟩ := h.1 x hx
    exact ⟨a, by rw [hst]; exact h1, hown a h2⟩
  · rw [hst] at h1 h2
    exact h.2 x y a hx hy h1 h2

theorem keep {own : Nat → Loc} {a j : Nat} (L : Loc) (ha : own a ≠ .task j) :
    ∀ b, own b = .task j → put own a L b = .task j := by
  intro b hb
  by_cases hba : b = a
  · rw [hba] at hb
    exact absurd hb ha
  · rw [put_ne _ _ hba]
    exact hb

/-- 走一步以后的不变量：执行的任务 i 单独证，别的任务只要它们的变量没变、它们的盒子还归它们 -/
theorem inv_of {s s' : S} {i : Nat} {p : List Ins} {F' : Var → Bool} (hI : Inv s)
    (hp : s'.prog = put s.prog i p) (hc : chk F' p = true) (hi : TaskOk s' i F')
    (hst : ∀ j, j ≠ i → s'.st j = s.st j)
    (hown : ∀ j b, j ≠ i → s.own b = .task j → s'.own b = .task j)
    (hch : ∀ c a, a ∈ s'.q c → s'.own a = .chan c) (hd : ∀ c, Dist (s'.q c))
    (hf : ∀ a, s'.own a ≠ .free → a < s'.next) : Inv s' := by
  refine ⟨fun j => ?_, hch, hd, hf⟩
  by_cases hj : j = i
  · rw [hj]
    exact ⟨F', by rw [hp, put_same]; exact hc, hi⟩
  · obtain ⟨F, h1, h2⟩ := hI.tasks j
    exact ⟨F, by rw [hp, put_ne _ _ hj]; exact h1,
      other_ok (hst j hj) (fun b hb => hown j b hj hb) h2⟩

theorem inv_init (P : Nat → List Ins) (h : ∀ i, chk (fun _ => false) (P i) = true) : Inv (init P) :=
  ⟨fun i => ⟨fun _ => false, h i, fun x hx => by simp at hx, fun x _ _ hx => by simp at hx⟩,
   fun c a ha => by simp [init] at ha, fun c => by simp [init, Dist], fun a ha => by simp [init] at ha⟩

/-- 不变量成立时，每个任务下一条指令碰的盒子都属于它 -/
theorem inv_safe {s : S} (hI : Inv s) (i : Nat) : safe i s = true := by
  obtain ⟨F, hc, hT⟩ := hI.tasks i
  unfold safe
  cases hp : s.prog i with
  | nil => rfl
  | cons ins p =>
    rw [hp] at hc
    cases ins with
    | use x =>
      simp only [chk, Bool.and_eq_true] at hc
      obtain ⟨a, hx, ho⟩ := hT.1 x hc.1
      simp [touch, hx, ho]
    | send c x =>
      simp only [chk, Bool.and_eq_true] at hc
      obtain ⟨a, hx, ho⟩ := hT.1 x hc.1
      simp [touch, hx, ho]
    | drop x =>
      simp only [chk, Bool.and_eq_true] at hc
      obtain ⟨a, hx, ho⟩ := hT.1 x hc.1
      simp [touch, hx, ho]
    | new x => rfl
    | mov y x => rfl
    | recv c x => rfl

/-! ## 每条指令保持不变量 -/

theorem inv_new {s : S} {i x : Nat} {p : List Ins} {F : Var → Bool} (hI : Inv s)
    (hc : chk (setF F x true) p = true) (hT : TaskOk s i F) :
    Inv { s with prog := put s.prog i p, st := put s.st i (put (s.st i) x (some s.next)), own := put s.own s.next (.task i), next := s.next + 1 } := by
  have hfree : s.own s.next = .free := by
    by_cases h : s.own s.next = .free
    · exact h
    · exact absurd (hI.fresh _ h) (Nat.lt_irrefl _)
  have hlt : ∀ b, s.own b ≠ .free → b ≠ s.next := fun b hb e => hb (by rw [e]; exact hfree)
  have nonext : ∀ w, F w = true → s.st i w ≠ some s.next := by
    intro w hw h
    obtain ⟨a', h1', h2'⟩ := hT.1 w hw
    rw [h] at h1'
    injection h1' with e
    rw [← e, hfree] at h2'
    cases h2'
  refine inv_of (i := i) (p := p) (F' := setF F x true) hI rfl hc ⟨?_, ?_⟩ ?_ ?_ ?_ ?_ ?_
  · intro z hz
    by_cases hzx : z = x
    · exact ⟨s.next, by simp [put, hzx], by simp [put]⟩
    · obtain ⟨b, h1, h2⟩ := hT.1 z (setF_true hz hzx)
      have hb : b ≠ s.next := hlt b (by rw [h2]; simp)
      exact ⟨b, by simp [put, hzx, h1], by simp [put, hb, h2]⟩
  · intro z w b hz hw h1 h2
    by_cases hzx : z = x
    · by_cases hwx : w = x
      · exact hzx.trans hwx.symm
      · simp [put, hzx] at h1
        simp [put, hwx] at h2
        rw [← h1] at h2
        exact absurd h2 (nonext w (setF_true hw hwx))
    · by_cases hwx : w = x
      · simp [put, hwx] at h2
        simp [put, hzx] at h1
        rw [← h2] at h1
        exact absurd h1 (nonext z (setF_true hz hzx))
      · simp [put, hzx] at h1
        simp [put, hwx] at h2
        exact hT.2 z w b (setF_true hz hzx) (setF_true hw hwx) h1 h2
  · intro j hj
    simp [put, hj]
  · intro j b hj hb
    show put s.own s.next (.task i) b = .task j
    exact keep (.task i) (by rw [hfree]; simp) b hb
  · intro c a ha
    have ho := hI.chans c a ha
    have hne : a ≠ s.next := hlt a (by rw [ho]; simp)
    show put s.own s.next (.task i) a = .chan c
    rw [put_ne _ _ hne]
    exact ho
  · exact hI.dist
  · intro a ha
    show a < s.next + 1
    by_cases hn : a = s.next
    · omega
    · have := hI.fresh a (by simpa [put, hn] using ha)
      omega

theorem inv_use {s : S} {i : Nat} {p : List Ins} {F : Var → Bool} (hI : Inv s)
    (hc : chk F p = true) (hT : TaskOk s i F) : Inv { s with prog := put s.prog i p } :=
  inv_of (i := i) (p := p) (F' := F) hI rfl hc hT (fun _ _ => rfl) (fun _ _ _ hb => hb)
    hI.chans hI.dist hI.fresh

theorem inv_mov {s : S} {i x y : Nat} {p : List Ins} {F : Var → Bool} (hI : Inv s)
    (hFx : F x = true) (hc : chk (setF (setF F x false) y true) p = true) (hT : TaskOk s i F) :
    Inv { s with prog := put s.prog i p, st := put s.st i (put (s.st i) y (s.st i x)) } := by
  refine inv_of (i := i) (p := p) (F' := setF (setF F x false) y true) hI rfl hc ⟨?_, ?_⟩ ?_
    (fun _ _ _ hb => hb) hI.chans hI.dist hI.fresh
  · intro z hz
    by_cases hzy : z = y
    · obtain ⟨a, h1, h2⟩ := hT.1 x hFx
      exact ⟨a, by simp [put, hzy, h1], h2⟩
    · obtain ⟨-, hz'⟩ := setF_false (setF_true hz hzy)
      obtain ⟨b, h1, h2⟩ := hT.1 z hz'
      exact ⟨b, by simp [put, hzy, h1], h2⟩
  · intro z w b hz hw h1 h2
    by_cases hzy : z = y
    · by_cases hwy : w = y
      · exact hzy.trans hwy.symm
      · obtain ⟨hwx, hw'⟩ := setF_false (setF_true hw hwy)
        simp [put, hzy] at h1
        simp [put, hwy] at h2
        exact absurd (hT.2 x w b hFx hw' h1 h2).symm hwx
    · obtain ⟨hzx, hz'⟩ := setF_false (setF_true hz hzy)
      by_cases hwy : w = y
      · simp [put, hzy] at h1
        simp [put, hwy] at h2
        exact absurd (hT.2 z x b hz' hFx h1 h2) hzx
      · obtain ⟨-, hw'⟩ := setF_false (setF_true hw hwy)
        simp [put, hzy] at h1
        simp [put, hwy] at h2
        exact hT.2 z w b hz' hw' h1 h2
  · intro j hj
    simp [put, hj]

/-- send、drop 碰的盒子属于执行的任务 -/
theorem own_of {s : S} {i x a : Nat} {F : Var → Bool} (hT : TaskOk s i F) (hFx : F x = true)
    (hx : s.st i x = some a) : s.own a = .task i := by
  obtain ⟨a', h1, h2⟩ := hT.1 x hFx
  rw [hx] at h1
  injection h1 with e
  rw [e]
  exact h2

/-- 任务 i 里别的有值的变量装的不是 x 的盒子 -/
theorem other_box {s : S} {i x a z b : Nat} {F : Var → Bool} (hT : TaskOk s i F) (hFx : F x = true)
    (hx : s.st i x = some a) (hzx : z ≠ x) (hz : F z = true) (h1 : s.st i z = some b) : b ≠ a := by
  intro e
  rw [e] at h1
  exact hzx (hT.2 z x a hz hFx h1 hx)

theorem inv_send {s : S} {i c x a : Nat} {p : List Ins} {F : Var → Bool} (hI : Inv s)
    (hFx : F x = true) (hc : chk (setF F x false) p = true) (hT : TaskOk s i F)
    (hx : s.st i x = some a) :
    Inv { s with prog := put s.prog i p, q := put s.q c (s.q c ++ [a]), own := put s.own a (.chan c) } := by
  have hoa := own_of hT hFx hx
  have nq : ∀ d b, s.own b = .chan d → b ≠ a := fun d b hb e => by
    rw [e, hoa] at hb
    cases hb
  refine inv_of (i := i) (p := p) (F' := setF F x false) hI rfl hc ⟨?_, ?_⟩ (fun _ _ => rfl) ?_ ?_ ?_ ?_
  · intro z hz
    obtain ⟨hzx, hz'⟩ := setF_false hz
    obtain ⟨b, h1, h2⟩ := hT.1 z hz'
    have hba := other_box hT hFx hx hzx hz' h1
    exact ⟨b, h1, by show put s.own a (.chan c) b = .task i; rw [put_ne _ _ hba]; exact h2⟩
  · intro z w b hz hw h1 h2
    exact hT.2 z w b (setF_false hz).2 (setF_false hw).2 h1 h2
  · intro j b hj hb
    exact keep (.chan c) (by rw [hoa]; simp [Ne.symm hj]) b hb
  · intro d b hb
    show put s.own a (.chan c) b = .chan d
    by_cases hdc : d = c
    · rw [hdc] at hb ⊢
      have hb' : b ∈ s.q c ++ [a] := by simpa [put] using hb
      simp only [List.mem_append, List.mem_singleton] at hb'
      rcases hb' with hb' | hb'
      · have ho := hI.chans c b hb'
        rw [put_ne _ _ (nq c b ho)]
        exact ho
      · rw [hb', put_same]
    · have hb' : b ∈ s.q d := by simpa [put, hdc] using hb
      have ho := hI.chans d b hb'
      rw [put_ne _ _ (nq d b ho)]
      exact ho
  · intro d
    show Dist (put s.q c (s.q c ++ [a]) d)
    by_cases hdc : d = c
    · rw [hdc, put_same]
      exact dist_snoc _ _ (hI.dist c) (fun hm => nq c a (hI.chans c a hm) rfl)
    · rw [put_ne _ _ hdc]
      exact hI.dist d
  · intro b hb
    show b < s.next
    by_cases hba : b = a
    · rw [hba]
      exact hI.fresh a (by rw [hoa]; simp)
    · have e : put s.own a (.chan c) b = s.own b := put_ne _ _ hba
      exact hI.fresh b (by rw [← e]; exact hb)

theorem inv_recv {s : S} {i c x a : Nat} {r : List Nat} {p : List Ins} {F : Var → Bool} (hI : Inv s)
    (hc : chk (setF F x true) p = true) (hT : TaskOk s i F) (hq : s.q c = a :: r) :
    Inv { s with prog := put s.prog i p, st := put s.st i (put (s.st i) x (some a)), q := put s.q c r, own := put s.own a (.task i) } := by
  have hoa : s.own a = .chan c := hI.chans c a (by rw [hq]; simp)
  have hdist : a ∉ r ∧ Dist r := by
    have := hI.dist c
    rw [hq] at this
    exact this
  have nb : ∀ b, s.own b = .task i → b ≠ a := fun b hb e => by
    rw [e, hoa] at hb
    cases hb
  have noa : ∀ w, F w = true → s.st i w ≠ some a := fun w hw h => by
    obtain ⟨b', h1', h2'⟩ := hT.1 w hw
    rw [h] at h1'
    injection h1' with e
    exact nb b' h2' e.symm
  refine inv_of (i := i) (p := p) (F' := setF F x true) hI rfl hc ⟨?_, ?_⟩ ?_ ?_ ?_ ?_ ?_
  · intro z hz
    by_cases hzx : z = x
    · exact ⟨a, by simp [put, hzx], by simp [put]⟩
    · obtain ⟨b, h1, h2⟩ := hT.1 z (setF_true hz hzx)
      exact ⟨b, by simp [put, hzx, h1], by simp [put, nb b h2, h2]⟩
  · intro z w b hz hw h1 h2
    by_cases hzx : z = x
    · by_cases hwx : w = x
      · exact hzx.trans hwx.symm
      · simp [put, hzx] at h1
        simp [put, hwx] at h2
        rw [← h1] at h2
        exact absurd h2 (noa w (setF_true hw hwx))
    · by_cases hwx : w = x
      · simp [put, hwx] at h2
        simp [put, hzx] at h1
        rw [← h2] at h1
        exact absurd h1 (noa z (setF_true hz hzx))
      · simp [put, hzx] at h1
        simp [put, hwx] at h2
        exact hT.2 z w b (setF_true hz hzx) (setF_true hw hwx) h1 h2
  · intro j hj
    simp [put, hj]
  · intro j b hj hb
    exact keep (.task i) (by rw [hoa]; simp) b hb
  · intro d b hb
    show put s.own a (.task i) b = .chan d
    by_cases hdc : d = c
    · rw [hdc] at hb ⊢
      have hb' : b ∈ r := by simpa [put] using hb
      have hba : b ≠ a := fun e => hdist.1 (by rw [← e]; exact hb')
      rw [put_ne _ _ hba]
      exact hI.chans c b (by rw [hq]; simp [hb'])
    · have hb' : b ∈ s.q d := by simpa [put, hdc] using hb
      have ho := hI.chans d b hb'
      have hba : b ≠ a := fun e => by
        rw [e, hoa] at ho
        injection ho with e2
        exact hdc e2.symm
      rw [put_ne _ _ hba]
      exact ho
  · intro d
    show Dist (put s.q c r d)
    by_cases hdc : d = c
    · rw [hdc, put_same]
      exact hdist.2
    · rw [put_ne _ _ hdc]
      exact hI.dist d
  · intro b hb
    show b < s.next
    by_cases hba : b = a
    · rw [hba]
      exact hI.fresh a (by rw [hoa]; simp)
    · have e : put s.own a (.task i) b = s.own b := put_ne _ _ hba
      exact hI.fresh b (by rw [← e]; exact hb)

theorem inv_drop {s : S} {i x a : Nat} {p : List Ins} {F : Var → Bool} (hI : Inv s)
    (hFx : F x = true) (hc : chk (setF F x false) p = true) (hT : TaskOk s i F)
    (hx : s.st i x = some a) : Inv { s with prog := put s.prog i p, own := put s.own a .free } := by
  have hoa := own_of hT hFx hx
  refine inv_of (i := i) (p := p) (F' := setF F x false) hI rfl hc ⟨?_, ?_⟩ (fun _ _ => rfl) ?_ ?_
    hI.dist ?_
  · intro z hz
    obtain ⟨hzx, hz'⟩ := setF_false hz
    obtain ⟨b, h1, h2⟩ := hT.1 z hz'
    have hba := other_box hT hFx hx hzx hz' h1
    exact ⟨b, h1, by show put s.own a .free b = .task i; rw [put_ne _ _ hba]; exact h2⟩
  · intro z w b hz hw h1 h2
    exact hT.2 z w b (setF_false hz).2 (setF_false hw).2 h1 h2
  · intro j b hj hb
    exact keep .free (by rw [hoa]; simp [Ne.symm hj]) b hb
  · intro c b hb
    have ho := hI.chans c b hb
    have hba : b ≠ a := fun e => by
      rw [e, hoa] at ho
      cases ho
    show put s.own a .free b = .chan c
    rw [put_ne _ _ hba]
    exact ho
  · intro b hb
    by_cases hba : b = a
    · rw [hba] at hb
      simp [put] at hb
    · have e : put s.own a .free b = s.own b := put_ne _ _ hba
      exact hI.fresh b (by rw [← e]; exact hb)

theorem step_inv {s s' : S} {i : Nat} (hI : Inv s) (h : step i s = some s') : Inv s' := by
  obtain ⟨F, hc, hT⟩ := hI.tasks i
  unfold step at h
  cases hp : s.prog i with
  | nil => simp [hp] at h
  | cons ins p =>
    simp only [hp] at h
    rw [hp] at hc
    cases ins with
    | new x =>
      simp only [chk, Bool.and_eq_true] at hc
      simp only [Option.some.injEq] at h
      subst h
      exact inv_new hI hc.2 hT
    | use x =>
      simp only [chk, Bool.and_eq_true] at hc
      cases hx : s.st i x with
      | none => simp [hx] at h
      | some a =>
        simp only [hx, Option.some.injEq] at h
        subst h
        exact inv_use hI hc.2 hT
    | mov y x =>
      simp only [chk, Bool.and_eq_true] at hc
      simp only [Option.some.injEq] at h
      subst h
      exact inv_mov hI hc.1.1 hc.2 hT
    | send c x =>
      simp only [chk, Bool.and_eq_true] at hc
      cases hx : s.st i x with
      | none => simp [hx] at h
      | some a =>
        simp only [hx, Option.some.injEq] at h
        subst h
        exact inv_send hI hc.1 hc.2 hT hx
    | recv c x =>
      simp only [chk, Bool.and_eq_true] at hc
      cases hq : s.q c with
      | nil => simp [hq] at h
      | cons a r =>
        simp only [hq, Option.some.injEq] at h
        subst h
        exact inv_recv hI hc.2 hT hq
    | drop x =>
      simp only [chk, Bool.and_eq_true] at hc
      cases hx : s.st i x with
      | none => simp [hx] at h
      | some a =>
        simp only [hx, Option.some.injEq] at h
        subst h
        exact inv_drop hI hc.1 hc.2 hT hx

theorem reach_inv {P : Nat → List Ins} (h : ∀ i, chk (fun _ => false) (P i) = true) :
    ∀ {s : S}, Reach (init P) s → Inv s
  | _, .refl => inv_init P h
  | _, .go _ hr hs => step_inv (reach_inv h hr) hs

/-- 定理：每个任务的程序都通过检查时，任何调度下走到的任何状态里，每个任务下一步碰的盒子都属于它自己 -/
theorem chan_race_free (P : Nat → List Ins) (h : ∀ i, chk (fun _ => false) (P i) = true)
    {s : S} (hr : Reach (init P) s) (i : Nat) : safe i s = true :=
  inv_safe (reach_inv h hr) i

/-! ## 例子 -/

/-- 任务 0：x0 = new；send(c0, x0)；use x0。任务 1：x0 = recv(c0)；use x0 -/
def racy : Nat → List Ins
  | 0 => [.new 0, .send 0 0, .use 0]
  | 1 => [.recv 0 0, .use 0]
  | _ => []

-- 检查不通过：send 以后 x0 已经移走了
example : chk (fun _ => false) (racy 0) = false := by decide
example : chk (fun _ => false) (racy 1) = true := by decide
-- 不检查的话：任务 0 走两步、任务 1 收到以后，任务 0 的下一步碰的盒子已经属于任务 1 了
example : ((step 0 (init racy)).bind (step 0) |>.bind (step 1) |>.map (safe 0)) = some false := by decide
-- send 以后重新赋值再用：可以
example : chk (fun _ => false) [.new 0, .send 0 0, .new 0, .use 0, .drop 0] = true := by decide
-- 收到以后转给别的变量再发出去：可以
example : chk (fun _ => false) [.recv 0 0, .mov 1 0, .send 1 1] = true := by decide

end Chan
end Lark
