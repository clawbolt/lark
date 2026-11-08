/-
Lark 可靠性证明 · 第四部分：释放和冻结（design/soundness.md 的 R2、R11、R16，代码生成约定 A2、A4）

变量里装的是盒子的地址（some a）或者空位（none，移走以后留下的，A2 的“清零”）。堆上每个地址要么有值，要么没有
（还没分配，或者已经释放）。会出错的情况：读一个已经释放的盒子（释放以后再用），释放一个已经释放的盒子（重复释放）。
赋值 x = e 先算 e，再释放 x 原来的值（空位什么也不做），再存进去。借用的 match / for 写成 bor x s：
s 里经由借用读 x 的盒子（peekB），x 冻结（R11），不能移走、不能重新赋值。程序结束时释放每个变量（A4）。

定理 `drop_exactly_once`：通过检查的程序运行时不会读到释放了的盒子、不会重复释放，结束时堆是空的，
即每个分配的值恰好释放一次。不冻结的话，bor 里给 x 重新赋值会释放借出去的盒子，之后的 peekB 读到释放了的值（例子）。
-/
import Lark.Core

namespace Lark
namespace Drop

/-- 整数表达式：peek x 读 x 的盒子里的数，peekB k 经由第 k 层借用（0 是最里面的）读 -/
inductive IE where
  | num (k : Int)
  | peek (x : Var)
  | peekB (k : Nat)
  | add (a b : IE)
  deriving Repr

/-- 产生一个盒子的表达式 -/
inductive OE where
  | move (x : Var)
  | mk (e : IE)
  deriving Repr

inductive DS where
  | skip
  | assign (x : Var) (o : OE)
  | seq (s t : DS)
  | ite (c : IE) (s t : DS)
  | bor (x : Var) (s : DS)
  deriving Repr

structure M where
  st : Var → Option Nat
  heap : Nat → Option Int
  next : Nat

def nth : List Nat → Nat → Option Nat
  | [], _ => none
  | a :: _, 0 => some a
  | _ :: l, k + 1 => nth l k

def setSt (μ : M) (x : Var) (v : Option Nat) : M :=
  { μ with st := fun y => if y = x then v else μ.st y }

def setHeap (μ : M) (a : Nat) (v : Option Int) : M :=
  { μ with heap := fun b => if b = a then v else μ.heap b }

def IE.eval (bs : List Nat) (μ : M) : IE → Option Int
  | .num k => some k
  | .peek x =>
    match μ.st x with
    | none => none
    | some a => μ.heap a
  | .peekB k =>
    match nth bs k with
    | none => none
    | some a => μ.heap a
  | .add a b =>
    match a.eval bs μ, b.eval bs μ with
    | some u, some v => some (u + v)
    | _, _ => none

def OE.eval (bs : List Nat) (μ : M) : OE → Option (Nat × M)
  | .move x =>
    match μ.st x with
    | none => none
    | some a => some (a, setSt μ x none)
  | .mk e =>
    match e.eval bs μ with
    | none => none
    | some n => some (μ.next, { setHeap μ μ.next (some n) with next := μ.next + 1 })

/-- 释放一个变量里的值：空位什么也不做，已经释放的盒子是重复释放 -/
def free (μ : M) : Option Nat → Option M
  | none => some μ
  | some a =>
    match μ.heap a with
    | none => none
    | some _ => some (setHeap μ a none)

def DS.eval : List Nat → DS → M → Option M
  | _, .skip, μ => some μ
  | bs, .assign x o, μ =>
    match o.eval bs μ with
    | none => none
    | some (a, μ1) =>
      match free μ1 (μ1.st x) with
      | none => none
      | some μ2 => some (setSt μ2 x (some a))
  | bs, .seq s t, μ =>
    match DS.eval bs s μ with
    | none => none
    | some μ1 => DS.eval bs t μ1
  | bs, .ite c s t, μ =>
    match c.eval bs μ with
    | none => none
    | some n => if n = 0 then DS.eval bs t μ else DS.eval bs s μ
  | bs, .bor x s, μ =>
    match μ.st x with
    | none => none
    | some a => DS.eval (a :: bs) s μ

/-- 程序结束时按顺序释放每个变量 -/
def dropAll : List Var → M → Option M
  | [], μ => some μ
  | x :: l, μ =>
    match free μ (μ.st x) with
    | none => none
    | some μ1 => dropAll l (setSt μ1 x none)

/-! ## 检查：vs 是程序的变量，f 是冻结的变量（最里面的借用在前），m 是可能没有值的变量 -/

def chkI (vs f m : List Var) : IE → Bool
  | .num _ => true
  | .peek x => decide (x ∈ vs) && !decide (x ∈ m)                        -- R1
  | .peekB k => decide (k < f.length)
  | .add a b => chkI vs f m a && chkI vs f m b

def chkO (vs f m : List Var) : OE → Option (List Var)
  | .move x => if x ∈ vs ∧ x ∉ m ∧ x ∉ f then some (x :: m) else none   -- R2：冻结的不能移走
  | .mk e => if chkI vs f m e then some m else none

def chkD (vs : List Var) : List Var → DS → List Var → Option (List Var)
  | _, .skip, m => some m
  | f, .assign x o, m =>                                                 -- R16：冻结的不能重新赋值
    if x ∈ vs ∧ x ∉ f then
      match chkO vs f m o with
      | none => none
      | some m1 => some (m1.filter (fun y => y != x))
    else none
  | f, .seq s t, m =>
    match chkD vs f s m with
    | none => none
    | some m1 => chkD vs f t m1
  | f, .ite c s t, m =>                                                  -- R10
    if chkI vs f m c then
      match chkD vs f s m, chkD vs f t m with
      | some ms, some mt => some (ms ++ mt)
      | _, _ => none
    else none
  | f, .bor x s, m => if x ∈ vs ∧ x ∉ m then chkD vs (x :: f) s m else none  -- R11

/-! ## 不变量（soundness.md 第 5 节）

- live：变量里的地址都还没释放
- uniq：一个盒子只有一个主人（没有两个变量装同一个地址）
- noleak：没释放的盒子都有一个程序变量是它的主人（结束时释放得到）
- fresh：没释放的地址都小于 next（新分配的地址没人用过）
- full：不在 m 里的变量有值
- pins：第 k 层借用的地址由一个冻结的变量拥有 -/

def Pins (st : Var → Option Nat) (f : List Var) (bs : List Nat) : Prop :=
  ∀ k, k < f.length → ∃ a y, nth bs k = some a ∧ y ∈ f ∧ st y = some a

structure Own (vs f m : List Var) (bs : List Nat) (μ : M) : Prop where
  live : ∀ x a, μ.st x = some a → μ.heap a ≠ none
  uniq : ∀ x y a, μ.st x = some a → μ.st y = some a → x = y
  noleak : ∀ a, μ.heap a ≠ none → ∃ x, x ∈ vs ∧ μ.st x = some a
  fresh : ∀ a, μ.heap a ≠ none → a < μ.next
  full : ∀ x, x ∈ vs → x ∉ m → μ.st x ≠ none
  pins : Pins μ.st f bs

theorem pins_congr {st st' : Var → Option Nat} {f : List Var} {bs : List Nat}
    (h : ∀ y, y ∈ f → st' y = st y) (hp : Pins st f bs) : Pins st' f bs := by
  intro k hk
  obtain ⟨a, y, hn, hy, hs⟩ := hp k hk
  exact ⟨a, y, hn, hy, by rw [h y hy]; exact hs⟩

theorem pins_cons {st : Var → Option Nat} {f : List Var} {bs : List Nat} {x : Var} {a : Nat}
    (hx : st x = some a) (hp : Pins st f bs) : Pins st (x :: f) (a :: bs) := by
  intro k hk
  cases k with
  | zero => exact ⟨a, x, rfl, by simp, hx⟩
  | succ k =>
    have hk' : k < f.length := by simp at hk; omega
    obtain ⟨b, y, hn, hy, hs⟩ := hp k hk'
    exact ⟨b, y, hn, by simp [hy], hs⟩

theorem free_ok (μ : M) (o : Option Nat) (h : ∀ b, o = some b → μ.heap b ≠ none) :
    ∃ μ2, free μ o = some μ2 ∧ μ2.st = μ.st ∧ μ2.next = μ.next ∧
      ∀ c, (μ2.heap c ≠ none ↔ (μ.heap c ≠ none ∧ o ≠ some c)) := by
  cases o with
  | none => exact ⟨μ, rfl, rfl, rfl, fun c => by simp⟩
  | some b =>
    cases hb : μ.heap b with
    | none => exact absurd hb (h b rfl)
    | some v =>
      refine ⟨setHeap μ b none, by simp [free, hb], rfl, rfl, ?_⟩
      intro c
      by_cases hcb : c = b
      · subst hcb
        simp [setHeap]
      · simp [setHeap, hcb, Ne.symm hcb]

theorem chkI_sound {vs f m : List Var} {bs : List Nat} {μ : M} (hO : Own vs f m bs μ) :
    ∀ e : IE, chkI vs f m e = true → ∃ n, e.eval bs μ = some n
  | .num k, _ => ⟨k, rfl⟩
  | .peek x, h => by
    simp [chkI] at h
    cases hx : μ.st x with
    | none => exact absurd hx (hO.full x h.1 h.2)
    | some a =>
      cases ha : μ.heap a with
      | none => exact absurd ha (hO.live x a hx)
      | some n => exact ⟨n, by simp [IE.eval, hx, ha]⟩
  | .peekB k, h => by
    simp [chkI] at h
    obtain ⟨a, y, hn, -, hy⟩ := hO.pins k h
    cases ha : μ.heap a with
    | none => exact absurd ha (hO.live y a hy)
    | some n => exact ⟨n, by simp [IE.eval, hn, ha]⟩
  | .add a b, h => by
    simp [chkI] at h
    obtain ⟨u, hu⟩ := chkI_sound hO a h.1
    obtain ⟨v, hv⟩ := chkI_sound hO b h.2
    exact ⟨u + v, by simp [IE.eval, hu, hv]⟩

theorem st_setSt (μ : M) (x : Var) (v : Option Nat) (y : Var) :
    (setSt μ x v).st y = if y = x then v else μ.st y := rfl

/-- 算完右边、还没存进去的时候：盒子 a 没有主人（在路上），其余同 Own -/
structure Fly (vs f m : List Var) (bs : List Nat) (a : Nat) (μ : M) : Prop where
  live : ∀ x b, μ.st x = some b → μ.heap b ≠ none
  uniq : ∀ x y b, μ.st x = some b → μ.st y = some b → x = y
  noleak : ∀ b, μ.heap b ≠ none → b = a ∨ ∃ x, x ∈ vs ∧ μ.st x = some b
  fresh : ∀ b, μ.heap b ≠ none → b < μ.next
  full : ∀ x, x ∈ vs → x ∉ m → μ.st x ≠ none
  pins : Pins μ.st f bs
  alive : μ.heap a ≠ none
  alone : ∀ y, μ.st y ≠ some a

theorem chkO_sound {vs f m : List Var} {bs : List Nat} {μ : M} (hO : Own vs f m bs μ) :
    ∀ (o : OE) (m1 : List Var), chkO vs f m o = some m1 →
      ∃ a μ1, o.eval bs μ = some (a, μ1) ∧ Fly vs f m1 bs a μ1 ∧ (∀ y, y ∈ f → μ1.st y = μ.st y)
  | .move x, m1, h => by
    simp only [chkO] at h
    split at h
    · rename_i hc
      obtain ⟨hv, hm, hf⟩ := hc
      simp only [Option.some.injEq] at h
      subst h
      cases hx : μ.st x with
      | none => exact absurd hx (hO.full x hv hm)
      | some a =>
        refine ⟨a, setSt μ x none, by simp [OE.eval, hx], ?_, ?_⟩
        · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
          · intro y b hy
            by_cases hyx : y = x
            · simp [st_setSt, hyx] at hy
            · simp [st_setSt, hyx] at hy
              exact hO.live y b hy
          · intro y z b hy hz
            by_cases hyx : y = x
            · simp [st_setSt, hyx] at hy
            by_cases hzx : z = x
            · simp [st_setSt, hzx] at hz
            simp [st_setSt, hyx, hzx] at hy hz
            exact hO.uniq y z b hy hz
          · intro b hb
            obtain ⟨z, hz, hzb⟩ := hO.noleak b hb
            by_cases hzx : z = x
            · left
              rw [hzx, hx] at hzb
              exact (Option.some.inj hzb).symm
            · right
              exact ⟨z, hz, by simp [st_setSt, hzx, hzb]⟩
          · exact hO.fresh
          · intro y hy hym
            simp only [List.mem_cons, not_or] at hym
            simp only [st_setSt, hym.1, ↓reduceIte]
            exact hO.full y hy hym.2
          · exact pins_congr (fun y hy => by
              have hyx : y ≠ x := fun e => hf (e ▸ hy)
              simp [st_setSt, hyx]) hO.pins
          · exact hO.live x a hx
          · intro y hy
            by_cases hyx : y = x
            · simp [st_setSt, hyx] at hy
            · simp [st_setSt, hyx] at hy
              exact hyx (hO.uniq y x a hy hx)
        · intro y hy
          have hyx : y ≠ x := fun e => hf (e ▸ hy)
          simp [st_setSt, hyx]
    · simp at h
  | .mk e, m1, h => by
    simp only [chkO] at h
    split at h
    · rename_i hc
      simp only [Option.some.injEq] at h
      subst h
      obtain ⟨n, hn⟩ := chkI_sound hO e hc
      refine ⟨μ.next, ⟨μ.st, fun b => if b = μ.next then some n else μ.heap b, μ.next + 1⟩,
        by simp only [OE.eval, hn] <;> rfl, ?_, fun _ _ => rfl⟩
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro y b hy
        have hl := hO.live y b hy
        have hb : b ≠ μ.next := fun e => by
          have := hO.fresh b hl
          omega
        simpa [hb] using hl
      · exact hO.uniq
      · intro b hb
        by_cases hbn : b = μ.next
        · exact Or.inl hbn
        · exact Or.inr (hO.noleak b (by simpa [hbn] using hb))
      · intro b hb
        show b < μ.next + 1
        by_cases hbn : b = μ.next
        · omega
        · have := hO.fresh b (by simpa [hbn] using hb)
          omega
      · exact hO.full
      · exact hO.pins
      · simp
      · intro y hy
        have := hO.fresh _ (hO.live y _ hy)
        omega
    · simp at h

theorem own_mono {vs f m m' : List Var} {bs : List Nat} {μ : M}
    (hs : ∀ x, x ∈ m → x ∈ m') (hO : Own vs f m bs μ) : Own vs f m' bs μ :=
  { hO with full := fun x hx hm => hO.full x hx (fun h => hm (hs x h)) }

/-- 检查通过就能运行，不变量保持，冻结的变量不变 -/
theorem chkD_sound (vs : List Var) (s : DS) : ∀ (f m m' : List Var) (bs : List Nat) (μ : M),
    chkD vs f s m = some m' → Own vs f m bs μ →
    ∃ μ', DS.eval bs s μ = some μ' ∧ Own vs f m' bs μ' ∧ ∀ y, y ∈ f → μ'.st y = μ.st y := by
  induction s with
  | skip =>
    intro f m m' bs μ h hO
    simp only [chkD, Option.some.injEq] at h
    subst h
    exact ⟨μ, rfl, hO, fun _ _ => rfl⟩
  | assign x o =>
    intro f m m' bs μ h hO
    simp only [chkD] at h
    split at h
    · rename_i hc
      cases ho : chkO vs f m o with
      | none => simp [ho] at h
      | some m1 =>
        simp only [ho, Option.some.injEq] at h
        subst h
        obtain ⟨a, μ1, he, hF, hfr⟩ := chkO_sound hO o m1 ho
        obtain ⟨μ2, hfree, hst, hnx, hheap⟩ := free_ok μ1 (μ1.st x) (fun b hb => hF.live x b hb)
        have hs3 : ∀ y, (setSt μ2 x (some a)).st y = if y = x then some a else μ1.st y :=
          fun y => by simp [st_setSt, hst]
        refine ⟨setSt μ2 x (some a), by simp [DS.eval, he, hfree], ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
        · intro y c hy
          rw [hs3] at hy
          show μ2.heap c ≠ none
          rw [hheap]
          by_cases hyx : y = x
          · simp [hyx] at hy
            subst hy
            exact ⟨hF.alive, hF.alone x⟩
          · simp [hyx] at hy
            exact ⟨hF.live y c hy, fun hxc => hyx (hF.uniq y x c hy hxc)⟩
        · intro y z c hy hz
          rw [hs3] at hy hz
          by_cases hyx : y = x
          · by_cases hzx : z = x
            · exact hyx.trans hzx.symm
            · simp [hyx] at hy
              simp [hzx] at hz
              subst hy
              exact absurd hz (hF.alone z)
          · by_cases hzx : z = x
            · simp [hzx] at hz
              simp [hyx] at hy
              subst hz
              exact absurd hy (hF.alone y)
            · simp [hyx] at hy
              simp [hzx] at hz
              exact hF.uniq y z c hy hz
        · intro c hcl
          have hc' : μ2.heap c ≠ none := hcl
          rw [hheap] at hc'
          rcases hF.noleak c hc'.1 with hca | ⟨z, hz, hzc⟩
          · exact ⟨x, hc.1, by rw [hs3]; simp [hca]⟩
          · have hzx : z ≠ x := fun e => hc'.2 (e ▸ hzc)
            exact ⟨z, hz, by rw [hs3]; simp [hzx, hzc]⟩
        · intro c hc
          have hc' : μ2.heap c ≠ none := hc
          rw [hheap] at hc'
          show c < μ2.next
          rw [hnx]
          exact hF.fresh c hc'.1
        · intro y hy hym
          rw [hs3]
          by_cases hyx : y = x
          · simp [hyx]
          · have hm1 : y ∉ m1 := fun hm => hym (by simp [List.mem_filter, hm, hyx])
            simp only [hyx, ↓reduceIte]
            exact hF.full y hy hm1
        · exact pins_congr (fun y hy => by
            have hyx : y ≠ x := fun e => hc.2 (e ▸ hy)
            rw [hs3]
            simp [hyx]) hF.pins
        · intro y hy
          have hyx : y ≠ x := fun e => hc.2 (e ▸ hy)
          rw [hs3]
          simp only [hyx, ↓reduceIte]
          exact hfr y hy
    · simp at h
  | seq s t ihs iht =>
    intro f m m' bs μ h hO
    simp only [chkD] at h
    cases hs : chkD vs f s m with
    | none => simp [hs] at h
    | some m1 =>
      simp only [hs] at h
      obtain ⟨μ1, e1, o1, fr1⟩ := ihs f m m1 bs μ hs hO
      obtain ⟨μ2, e2, o2, fr2⟩ := iht f m1 m' bs μ1 h o1
      exact ⟨μ2, by simp [DS.eval, e1, e2], o2, fun y hy => (fr2 y hy).trans (fr1 y hy)⟩
  | ite c s t ihs iht =>
    intro f m m' bs μ h hO
    simp only [chkD] at h
    split at h
    · rename_i hc
      cases hs : chkD vs f s m with
      | none => simp [hs] at h
      | some ms =>
        cases ht : chkD vs f t m with
        | none => simp [hs, ht] at h
        | some mt =>
          simp only [hs, ht, Option.some.injEq] at h
          subst h
          obtain ⟨n, hn⟩ := chkI_sound hO c hc
          by_cases hz : n = 0
          · obtain ⟨μ', e', o', fr'⟩ := iht f m mt bs μ ht hO
            exact ⟨μ', by simp [DS.eval, hn, hz, e'], own_mono (fun x hx => by simp [hx]) o', fr'⟩
          · obtain ⟨μ', e', o', fr'⟩ := ihs f m ms bs μ hs hO
            exact ⟨μ', by simp [DS.eval, hn, hz, e'], own_mono (fun x hx => by simp [hx]) o', fr'⟩
    · simp at h
  | bor x s ih =>
    intro f m m' bs μ h hO
    simp only [chkD] at h
    split at h
    · rename_i hc
      cases hx : μ.st x with
      | none => exact absurd hx (hO.full x hc.1 hc.2)
      | some a =>
        have hO' : Own vs (x :: f) m (a :: bs) μ := { hO with pins := pins_cons hx hO.pins }
        obtain ⟨μ', e', o', fr'⟩ := ih (x :: f) m m' (a :: bs) μ h hO'
        have hpin : ∀ y, y ∈ f → μ'.st y = μ.st y := fun y hy => fr' y (by simp [hy])
        exact ⟨μ', by simp [DS.eval, hx, e'], { o' with pins := pins_congr hpin hO.pins }, hpin⟩
    · simp at h

/-- 结束时释放：每个变量的值释放一次，不会重复释放，释放完堆是空的 -/
theorem drop_all_ok : ∀ (l : List Var) (μ : M),
    (∀ x a, μ.st x = some a → μ.heap a ≠ none) →
    (∀ x y a, μ.st x = some a → μ.st y = some a → x = y) →
    (∀ a, μ.heap a ≠ none → ∃ x, x ∈ l ∧ μ.st x = some a) →
    ∃ μ', dropAll l μ = some μ' ∧ ∀ a, μ'.heap a = none
  | [], μ, _, _, hn => ⟨μ, rfl, fun a => by
      cases h : μ.heap a with
      | none => rfl
      | some v =>
        obtain ⟨x, hx, -⟩ := hn a (by simp [h])
        simp at hx⟩
  | x :: l, μ, hl, hu, hn => by
    obtain ⟨μ2, hfree, hst, -, hheap⟩ := free_ok μ (μ.st x) (fun b hb => hl x b hb)
    have hs3 : ∀ y, (setSt μ2 x none).st y = if y = x then none else μ.st y :=
      fun y => by simp [st_setSt, hst]
    have h1 : ∀ y c, (setSt μ2 x none).st y = some c → (setSt μ2 x none).heap c ≠ none := by
      intro y c hy
      rw [hs3] at hy
      by_cases hyx : y = x
      · simp [hyx] at hy
      · simp [hyx] at hy
        show μ2.heap c ≠ none
        rw [hheap]
        exact ⟨hl y c hy, fun hxc => hyx (hu y x c hy hxc)⟩
    have h2 : ∀ y z c, (setSt μ2 x none).st y = some c → (setSt μ2 x none).st z = some c → y = z := by
      intro y z c hy hz
      rw [hs3] at hy hz
      by_cases hyx : y = x
      · simp [hyx] at hy
      · by_cases hzx : z = x
        · simp [hzx] at hz
        · simp [hyx] at hy
          simp [hzx] at hz
          exact hu y z c hy hz
    have h3 : ∀ c, (setSt μ2 x none).heap c ≠ none → ∃ z, z ∈ l ∧ (setSt μ2 x none).st z = some c := by
      intro c hc
      have hc' : μ2.heap c ≠ none := hc
      rw [hheap] at hc'
      obtain ⟨z, hz, hzc⟩ := hn c hc'.1
      have hzx : z ≠ x := fun e => hc'.2 (e ▸ hzc)
      simp only [List.mem_cons] at hz
      rcases hz with hz | hz
      · exact absurd hz hzx
      · exact ⟨z, hz, by rw [hs3]; simp [hzx, hzc]⟩
    obtain ⟨μ', e', h'⟩ := drop_all_ok l (setSt μ2 x none) h1 h2 h3
    exact ⟨μ', by simp [dropAll, hfree, e'], h'⟩

/-- 定理：通过检查的程序运行时不会读到释放了的盒子、不会重复释放；结束时释放所有变量以后堆是空的。
    合起来就是每个分配的值恰好释放一次 -/
theorem drop_exactly_once (vs : List Var) (s : DS) (m m' : List Var) (μ : M)
    (h : chkD vs [] s m = some m') (hO : Own vs [] m [] μ) :
    ∃ μ' μ'', DS.eval [] s μ = some μ' ∧ dropAll vs μ' = some μ'' ∧ ∀ a, μ''.heap a = none := by
  obtain ⟨μ', e', o', -⟩ := chkD_sound vs s [] m m' [] μ h hO
  obtain ⟨μ'', d, hz⟩ := drop_all_ok vs μ' o'.live o'.uniq o'.noleak
  exact ⟨μ', μ'', e', d, hz⟩

/-! ## 例子 -/

def start : M := ⟨fun _ => none, fun _ => none, 0⟩

/-- 开始时什么都没分配，每个变量都没有值，满足不变量；所以任何通过检查的程序都适用 drop_exactly_once -/
theorem own_start (vs : List Var) : Own vs [] vs [] start :=
  ⟨fun _ _ h => by simp [start] at h, fun _ _ _ h => by simp [start] at h,
   fun _ h => by simp [start] at h, fun _ h => by simp [start] at h,
   fun _ hx hm => absurd hx hm, fun _ hk => by simp at hk⟩

/-- x0 = box(1)；借用 x0 { x0 = box(2)；x1 = box(借来的值) } -/
def reborrow : DS :=
  .seq (.assign 0 (.mk (.num 1))) (.bor 0 (.seq (.assign 0 (.mk (.num 2))) (.assign 1 (.mk (.peekB 0)))))

-- 检查不通过：借用期间 x0 冻结，不能重新赋值（R11）
example : chkD [0, 1] [] reborrow [0, 1] = none := by decide
-- 不检查的话，重新赋值释放了借出去的盒子，之后经由借用读到释放了的值
example : (DS.eval [] reborrow start).isNone = true := by decide
-- 只读借用可以
example : chkD [0, 1] [] (.seq (.assign 0 (.mk (.num 1))) (.bor 0 (.assign 1 (.mk (.peekB 0))))) [0, 1]
    = some [] := by decide
-- 移走两次：不通过
example : chkD [0, 1, 2] [] (.seq (.assign 0 (.mk (.num 1)))
    (.seq (.assign 1 (.move 0)) (.assign 2 (.move 0)))) [0, 1, 2] = none := by decide

end Drop
end Lark
