/-
Lark 可靠性证明 · 第八部分：闭包（design/soundness.md 的 R18–R20）

两种闭包：
- 借来的闭包（fn 参数）：按引用读外面的变量，只在一次调用期间存在，被调用的函数可能调用它任意多次，也可能一次都不调用。
  这里写成 apply x b k：闭包体 b 按引用读 x，执行 k 次。
- Fn 闭包：创建时把捕获的值复制一份，自己拥有这份副本，可以存起来、活得比原来的变量久。
  这里写成 mkFn c x b（闭包 c 复制 x，体是 b）、call c、dropFn c（释放闭包和它的副本）。
为了简单，每个闭包只捕获一个变量。闭包体里只能读（rd）或者移走（mv）捕获的值。

检查（own.lark 的 clo_base）：闭包体不能移走捕获的变量（R18），因为闭包可能被调用多次，第二次就读到空位。
程序是直线的（分支、循环、跳出在前面几个文件里证过），检查精确地记录哪些变量有值、哪些闭包还活着，结束时都要释放掉
（真实的编译器自动插入释放，Exit.lean 证过这一步）。

定理 `clo_sound`：通过检查的程序运行时不会读到空位或释放了的盒子、不会重复释放，结束时堆是空的。
例子里，Fn 闭包在原来的变量释放以后还能调用（它有自己的副本），这就是 R20 要求 Fn 复制的原因。
R19（闭包里不能 return、break 等）和 R20 的“不能捕获 fn 参数”在这个模型里是结构上的：闭包体没有这些语句，
借来的闭包也不是能被捕获的值。
-/
import Lark.Core

namespace Lark
namespace Clo

inductive BI where
  | rd
  | mv
  deriving Repr

inductive Ins where
  | new (x : Var)
  | use (x : Var)
  | mov (y x : Var)
  | drop (x : Var)
  | mkFn (c : Nat) (x : Var) (b : List BI)
  | call (c : Nat)
  | dropFn (c : Nat)
  | apply (x : Var) (b : List BI) (k : Nat)
  deriving Repr

/-- 盒子的地址装在哪里：一个变量，或者一个 Fn 闭包的副本 -/
inductive Loc where
  | var (x : Var)
  | clo (c : Nat)
  deriving DecidableEq, Repr

structure M where
  st : Loc → Option Nat
  heap : Nat → Bool
  fns : Nat → Option (List BI)
  next : Nat

def put {κ α : Type} [DecidableEq κ] (f : κ → α) (k : κ) (v : α) : κ → α := fun j => if j = k then v else f j

def alloc (μ : M) (l : Loc) : M :=
  { μ with st := put μ.st l (some μ.next), heap := put μ.heap μ.next true, next := μ.next + 1 }

/-- 释放 l 里的盒子：空位或者已经释放的盒子是错误 -/
def freeAt (μ : M) (l : Loc) : Option M :=
  match μ.st l with
  | none => none
  | some a => if μ.heap a then some { μ with st := put μ.st l none, heap := put μ.heap a false } else none

/-- 执行一次闭包体，捕获的值在 l：rd 读，mv 移走（拿出来释放掉） -/
def runBody (l : Loc) : List BI → M → Option M
  | [], μ => some μ
  | .rd :: b, μ =>
    match μ.st l with
    | none => none
    | some a => if μ.heap a then runBody l b μ else none
  | .mv :: b, μ =>
    match freeAt μ l with
    | none => none
    | some μ' => runBody l b μ'

def runK (l : Loc) (b : List BI) : Nat → M → Option M
  | 0, μ => some μ
  | k + 1, μ =>
    match runBody l b μ with
    | none => none
    | some μ' => runK l b k μ'

def exec (μ : M) : Ins → Option M
  | .new x => some (alloc μ (.var x))
  | .use x =>
    match μ.st (.var x) with
    | none => none
    | some a => if μ.heap a then some μ else none
  | .mov y x =>
    match μ.st (.var x) with
    | none => none
    | some a => some { μ with st := put (put μ.st (.var x) none) (.var y) (some a) }
  | .drop x => freeAt μ (.var x)
  | .mkFn c x b =>
    match μ.st (.var x) with
    | none => none
    | some a => if μ.heap a then some { alloc μ (.clo c) with fns := put μ.fns c (some b) } else none
  | .call c =>
    match μ.fns c with
    | none => none
    | some b => runBody (.clo c) b μ
  | .dropFn c =>
    match μ.fns c with
    | none => none
    | some _ =>
      match freeAt μ (.clo c) with
      | none => none
      | some μ' => some { μ' with fns := put μ'.fns c none }
  | .apply x b k => runK (.var x) b k μ

def run : List Ins → M → Option M
  | [], μ => some μ
  | i :: p, μ =>
    match exec μ i with
    | none => none
    | some μ' => run p μ'

/-! ## 检查：F 是有值的变量，G 是活着的 Fn 闭包 -/

/-- R18：闭包体只读捕获的值 -/
def bodyOk : List BI → Bool
  | [] => true
  | .rd :: b => bodyOk b
  | .mv :: _ => false

def chk : List Var → List Nat → List Ins → Bool
  | F, G, [] => decide (F = []) && decide (G = [])
  | F, G, .new x :: p => if x ∉ F then chk (x :: F) G p else false
  | F, G, .use x :: p => if x ∈ F then chk F G p else false
  | F, G, .mov y x :: p => if x ∈ F ∧ y ∉ F then chk (y :: F.filter (fun z => z != x)) G p else false
  | F, G, .drop x :: p => if x ∈ F then chk (F.filter (fun z => z != x)) G p else false
  | F, G, .mkFn c x b :: p => if c ∉ G ∧ x ∈ F ∧ bodyOk b = true then chk F (c :: G) p else false
  | F, G, .call c :: p => if c ∈ G then chk F G p else false
  | F, G, .dropFn c :: p => if c ∈ G then chk F (G.filter (fun d => d != c)) p else false
  | F, G, .apply x b _ :: p => if x ∈ F ∧ bodyOk b = true then chk F G p else false

def start : M := ⟨fun _ => none, fun _ => false, fun _ => none, 0⟩

/-! ## 不变量

Heap：地址都没释放、一个盒子一个主人（变量或者闭包的副本）、没释放的盒子有主人、新地址没人用过。
Book：检查记的和运行时一致：F 里的变量有值，G 里的闭包活着，活着的闭包有副本，闭包体只读。 -/

structure Heap (st : Loc → Option Nat) (heap : Nat → Bool) (next : Nat) : Prop where
  live : ∀ l a, st l = some a → heap a = true
  uniq : ∀ l l' a, st l = some a → st l' = some a → l = l'
  noleak : ∀ a, heap a = true → ∃ l, st l = some a
  fresh : ∀ a, heap a = true → a < next

structure Book (F : List Var) (G : List Nat) (μ : M) : Prop where
  vars : ∀ x, x ∈ F ↔ μ.st (.var x) ≠ none
  fns : ∀ c, c ∈ G ↔ μ.fns c ≠ none
  slots : ∀ c, μ.st (.clo c) ≠ none ↔ μ.fns c ≠ none
  bodies : ∀ c b, μ.fns c = some b → bodyOk b = true

theorem put_same {κ α : Type} [DecidableEq κ] (f : κ → α) (k : κ) (v : α) : put f k v k = v := by
  simp [put]

theorem put_ne {κ α : Type} [DecidableEq κ] (f : κ → α) {k j : κ} (v : α) (h : j ≠ k) : put f k v j = f j := by
  simp [put, h]

theorem some_of {α : Type} {o : Option α} (h : o ≠ none) : ∃ a, o = some a := by
  cases o with
  | none => exact absurd rfl h
  | some a => exact ⟨a, rfl⟩

theorem none_of {α : Type} {o : Option α} {P : Prop} (h : o ≠ none → P) (hp : ¬P) : o = none := by
  cases o with
  | none => rfl
  | some a => exact absurd (h (by simp)) hp

theorem heap_alloc {st : Loc → Option Nat} {heap : Nat → Bool} {next : Nat} {l : Loc}
    (hH : Heap st heap next) (hl : st l = none) :
    Heap (put st l (some next)) (put heap next true) (next + 1) := by
  have nn : ∀ l' a, st l' = some a → a ≠ next := fun l' a h e => by
    have := hH.fresh a (hH.live l' a h)
    omega
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro l' a h
    by_cases e : l' = l
    · rw [e, put_same] at h
      injection h with h
      rw [← h, put_same]
    · rw [put_ne _ _ e] at h
      rw [put_ne _ _ (nn l' a h)]
      exact hH.live l' a h
  · intro l1 l2 a h1 h2
    by_cases e1 : l1 = l
    · by_cases e2 : l2 = l
      · exact e1.trans e2.symm
      · rw [e1, put_same] at h1
        rw [put_ne _ _ e2] at h2
        injection h1 with h1
        exact absurd h1.symm (nn l2 a h2)
    · by_cases e2 : l2 = l
      · rw [e2, put_same] at h2
        rw [put_ne _ _ e1] at h1
        injection h2 with h2
        exact absurd h2.symm (nn l1 a h1)
      · rw [put_ne _ _ e1] at h1
        rw [put_ne _ _ e2] at h2
        exact hH.uniq l1 l2 a h1 h2
  · intro a h
    by_cases ha : a = next
    · exact ⟨l, by rw [put_same, ha]⟩
    · rw [put_ne _ _ ha] at h
      obtain ⟨l', hl'⟩ := hH.noleak a h
      have e : l' ≠ l := fun e => by
        rw [e, hl] at hl'
        cases hl'
      exact ⟨l', by rw [put_ne _ _ e]; exact hl'⟩
  · intro a h
    by_cases ha : a = next
    · omega
    · rw [put_ne _ _ ha] at h
      have := hH.fresh a h
      omega

theorem heap_free {st : Loc → Option Nat} {heap : Nat → Bool} {next : Nat} {l : Loc} {a : Nat}
    (hH : Heap st heap next) (hl : st l = some a) : Heap (put st l none) (put heap a false) next := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro l' b h
    by_cases e : l' = l
    · rw [e, put_same] at h
      cases h
    · rw [put_ne _ _ e] at h
      have hb : b ≠ a := fun eb => by
        rw [eb] at h
        exact e (hH.uniq l' l a h hl)
      rw [put_ne _ _ hb]
      exact hH.live l' b h
  · intro l1 l2 b h1 h2
    by_cases e1 : l1 = l
    · rw [e1, put_same] at h1
      cases h1
    · by_cases e2 : l2 = l
      · rw [e2, put_same] at h2
        cases h2
      · rw [put_ne _ _ e1] at h1
        rw [put_ne _ _ e2] at h2
        exact hH.uniq l1 l2 b h1 h2
  · intro b h
    by_cases hb : b = a
    · rw [hb, put_same] at h
      cases h
    · rw [put_ne _ _ hb] at h
      obtain ⟨l', hl'⟩ := hH.noleak b h
      have e : l' ≠ l := fun e => by
        rw [e, hl] at hl'
        injection hl' with hl'
        exact hb hl'.symm
      exact ⟨l', by rw [put_ne _ _ e]; exact hl'⟩
  · intro b h
    by_cases hb : b = a
    · rw [hb, put_same] at h
      cases h
    · rw [put_ne _ _ hb] at h
      exact hH.fresh b h

theorem heap_mov {st : Loc → Option Nat} {heap : Nat → Bool} {next : Nat} {x y : Loc} {a : Nat}
    (hH : Heap st heap next) (hx : st x = some a) (hy : st y = none) :
    Heap (put (put st x none) y (some a)) heap next := by
  have hxy : x ≠ y := fun e => by
    rw [e, hy] at hx
    cases hx
  have sY : put (put st x none) y (some a) y = some a := put_same _ _ _
  have sX : put (put st x none) y (some a) x = none := by rw [put_ne _ _ hxy, put_same]
  have so : ∀ l, l ≠ x → l ≠ y → put (put st x none) y (some a) l = st l := fun l h1 h2 => by
    rw [put_ne _ _ h2, put_ne _ _ h1]
  have key : ∀ l b, l ≠ y → put (put st x none) y (some a) l = some b → l ≠ x ∧ st l = some b := by
    intro l b ey h
    by_cases ex : l = x
    · rw [ex, sX] at h
      cases h
    · rw [so l ex ey] at h
      exact ⟨ex, h⟩
  refine ⟨?_, ?_, ?_, hH.fresh⟩
  · intro l b h
    by_cases ey : l = y
    · rw [ey, sY] at h
      injection h with h
      rw [← h]
      exact hH.live x a hx
    · exact hH.live l b (key l b ey h).2
  · intro l1 l2 b h1 h2
    by_cases e1 : l1 = y
    · by_cases e2 : l2 = y
      · exact e1.trans e2.symm
      · rw [e1, sY] at h1
        injection h1 with h1
        obtain ⟨ex, h2'⟩ := key l2 b e2 h2
        rw [← h1] at h2'
        exact absurd (hH.uniq l2 x a h2' hx) ex
    · by_cases e2 : l2 = y
      · rw [e2, sY] at h2
        injection h2 with h2
        obtain ⟨ex, h1'⟩ := key l1 b e1 h1
        rw [← h2] at h1'
        exact absurd (hH.uniq l1 x a h1' hx) ex
      · exact hH.uniq l1 l2 b (key l1 b e1 h1).2 (key l2 b e2 h2).2
  · intro b h
    obtain ⟨l, hl⟩ := hH.noleak b h
    by_cases ex : l = x
    · rw [ex, hx] at hl
      injection hl with hl
      exact ⟨y, by rw [sY, hl]⟩
    · have ey : l ≠ y := fun e => by
        rw [e, hy] at hl
        cases hl
      exact ⟨l, by rw [so l ex ey]; exact hl⟩

/-- 只读的闭包体：执行一次什么也不改变 -/
theorem body_read {μ : M} {l : Loc} {a : Nat} (hl : μ.st l = some a) (ha : μ.heap a = true) :
    ∀ b, bodyOk b = true → runBody l b μ = some μ
  | [], _ => rfl
  | .rd :: b, h => by
    simp only [bodyOk] at h
    simp [runBody, hl, ha]
    exact body_read hl ha b h
  | .mv :: _, h => by simp [bodyOk] at h

theorem runK_read {μ : M} {l : Loc} {a : Nat} (hl : μ.st l = some a) (ha : μ.heap a = true)
    {b : List BI} (hb : bodyOk b = true) : ∀ k, runK l b k μ = some μ
  | 0 => rfl
  | k + 1 => by
    show (match runBody l b μ with
      | none => none
      | some μ' => runK l b k μ') = some μ
    rw [body_read hl ha b hb]
    exact runK_read hl ha hb k

theorem finish {i : Ins} {p : List Ins} {μ μ1 : M} (he : exec μ i = some μ1) :
    run (i :: p) μ = run p μ1 := by
  simp [run, he]

/-- 通过检查的程序走完，堆是空的 -/
theorem run_sound : ∀ (p : List Ins) (F : List Var) (G : List Nat) (μ : M),
    Book F G μ → Heap μ.st μ.heap μ.next → chk F G p = true →
    ∃ μ', run p μ = some μ' ∧ ∀ a, μ'.heap a = false
  | [], F, G, μ, hB, hH, h => by
    simp only [chk, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨hF, hG⟩ := h
    refine ⟨μ, rfl, fun a => ?_⟩
    cases ha : μ.heap a with
    | false => rfl
    | true =>
      obtain ⟨l, hl⟩ := hH.noleak a ha
      have hne : μ.st l ≠ none := by
        rw [hl]
        simp
      cases l with
      | var x =>
        have hm := (hB.vars x).mpr hne
        rw [hF] at hm
        cases hm
      | clo c =>
        have hm := (hB.fns c).mpr ((hB.slots c).mp hne)
        rw [hG] at hm
        cases hm
  | .new x :: p, F, G, μ, hB, hH, h => by
    simp only [chk] at h
    split at h
    · rename_i hc
      have hx : μ.st (.var x) = none := none_of (hB.vars x).mpr hc
      have hB1 : Book (x :: F) G (alloc μ (.var x)) := by
        refine ⟨fun y => ?_, hB.fns, fun c => ?_, hB.bodies⟩
        · show y ∈ x :: F ↔ put μ.st (.var x) (some μ.next) (.var y) ≠ none
          by_cases hyx : y = x
          · rw [hyx]
            simp [put]
          · rw [put_ne _ _ (fun e => hyx (Loc.var.inj e)), ← hB.vars y]
            simp [hyx]
        · show put μ.st (.var x) (some μ.next) (.clo c) ≠ none ↔ μ.fns c ≠ none
          rw [put_ne _ _ (by simp)]
          exact hB.slots c
      obtain ⟨μ', e', hz⟩ := run_sound p (x :: F) G (alloc μ (.var x)) hB1 (heap_alloc hH hx) h
      have he : exec μ (.new x) = some (alloc μ (.var x)) := rfl
      exact ⟨μ', (finish he).trans e', hz⟩
    · simp at h
  | .use x :: p, F, G, μ, hB, hH, h => by
    simp only [chk] at h
    split at h
    · rename_i hc
      obtain ⟨a, hx⟩ := some_of ((hB.vars x).mp hc)
      have he : exec μ (.use x) = some μ := by simp [exec, hx, hH.live _ a hx]
      obtain ⟨μ', e', hz⟩ := run_sound p F G μ hB hH h
      exact ⟨μ', (finish he).trans e', hz⟩
    · simp at h
  | .mov y x :: p, F, G, μ, hB, hH, h => by
    simp only [chk] at h
    split at h
    · rename_i hc
      obtain ⟨hxF, hyF⟩ := hc
      obtain ⟨a, hx⟩ := some_of ((hB.vars x).mp hxF)
      have hy : μ.st (.var y) = none := none_of (hB.vars y).mpr hyF
      have hyx : y ≠ x := fun e => hyF (e ▸ hxF)
      have he : exec μ (.mov y x) = some { μ with st := put (put μ.st (.var x) none) (.var y) (some a) } := by
        simp [exec, hx]
      have hB1 : Book (y :: F.filter (fun z => z != x)) G { μ with st := put (put μ.st (.var x) none) (.var y) (some a) } := by
        refine ⟨fun z => ?_, hB.fns, fun c => ?_, hB.bodies⟩
        · show z ∈ y :: F.filter (fun z => z != x) ↔ put (put μ.st (.var x) none) (.var y) (some a) (.var z) ≠ none
          by_cases hzy : z = y
          · rw [hzy]
            simp [put]
          · by_cases hzx : z = x
            · rw [hzx]
              simp [put, Ne.symm hyx]
            · rw [put_ne _ _ (fun e => hzy (Loc.var.inj e)), put_ne _ _ (fun e => hzx (Loc.var.inj e)), ← hB.vars z]
              simp [hzy, hzx]
        · show put (put μ.st (.var x) none) (.var y) (some a) (.clo c) ≠ none ↔ μ.fns c ≠ none
          rw [put_ne _ _ (by simp), put_ne _ _ (by simp)]
          exact hB.slots c
      obtain ⟨μ', e', hz⟩ := run_sound p _ G _ hB1 (heap_mov hH hx hy) h
      exact ⟨μ', (finish he).trans e', hz⟩
    · simp at h
  | .drop x :: p, F, G, μ, hB, hH, h => by
    simp only [chk] at h
    split at h
    · rename_i hc
      obtain ⟨a, hx⟩ := some_of ((hB.vars x).mp hc)
      have ha := hH.live _ a hx
      have he : exec μ (.drop x) = some { μ with st := put μ.st (.var x) none, heap := put μ.heap a false } := by
        simp [exec, freeAt, hx, ha]
      have hB1 : Book (F.filter (fun z => z != x)) G { μ with st := put μ.st (.var x) none, heap := put μ.heap a false } := by
        refine ⟨fun z => ?_, hB.fns, fun c => ?_, hB.bodies⟩
        · show z ∈ F.filter (fun z => z != x) ↔ put μ.st (.var x) none (.var z) ≠ none
          by_cases hzx : z = x
          · rw [hzx]
            simp [put]
          · rw [put_ne _ _ (fun e => hzx (Loc.var.inj e)), ← hB.vars z]
            simp [hzx]
        · show put μ.st (.var x) none (.clo c) ≠ none ↔ μ.fns c ≠ none
          rw [put_ne _ _ (by simp)]
          exact hB.slots c
      obtain ⟨μ', e', hz⟩ := run_sound p _ G _ hB1 (heap_free hH hx) h
      exact ⟨μ', (finish he).trans e', hz⟩
    · simp at h
  | .mkFn c x b :: p, F, G, μ, hB, hH, h => by
    simp only [chk] at h
    split at h
    · rename_i hc
      obtain ⟨hcG, hxF, hb⟩ := hc
      obtain ⟨a, hx⟩ := some_of ((hB.vars x).mp hxF)
      have ha := hH.live _ a hx
      have hfc : μ.fns c = none := none_of (hB.fns c).mpr hcG
      have hcl : μ.st (.clo c) = none := none_of (hB.slots c).mp (by rw [hfc]; simp)
      have he : exec μ (.mkFn c x b) = some { alloc μ (.clo c) with fns := put μ.fns c (some b) } := by
        simp [exec, hx, ha]
      have hB1 : Book F (c :: G) { alloc μ (.clo c) with fns := put μ.fns c (some b) } := by
        refine ⟨fun z => ?_, fun d => ?_, fun d => ?_, fun d b' hd => ?_⟩
        · show z ∈ F ↔ put μ.st (.clo c) (some μ.next) (.var z) ≠ none
          rw [put_ne _ _ (by simp)]
          exact hB.vars z
        · show d ∈ c :: G ↔ put μ.fns c (some b) d ≠ none
          by_cases hdc : d = c
          · rw [hdc]
            simp [put]
          · rw [put_ne _ _ hdc, ← hB.fns d]
            simp [hdc]
        · show put μ.st (.clo c) (some μ.next) (.clo d) ≠ none ↔ put μ.fns c (some b) d ≠ none
          by_cases hdc : d = c
          · rw [hdc]
            simp [put]
          · rw [put_ne _ _ (fun e => hdc (Loc.clo.inj e)), put_ne _ _ hdc]
            exact hB.slots d
        · have hd' : put μ.fns c (some b) d = some b' := hd
          by_cases hdc : d = c
          · rw [hdc, put_same] at hd'
            injection hd' with hd'
            rw [← hd']
            exact hb
          · rw [put_ne _ _ hdc] at hd'
            exact hB.bodies d b' hd'
      obtain ⟨μ', e', hz⟩ := run_sound p F _ _ hB1 (heap_alloc hH hcl) h
      exact ⟨μ', (finish he).trans e', hz⟩
    · simp at h
  | .call c :: p, F, G, μ, hB, hH, h => by
    simp only [chk] at h
    split at h
    · rename_i hc
      obtain ⟨b, hfb⟩ := some_of ((hB.fns c).mp hc)
      obtain ⟨a, hca⟩ := some_of ((hB.slots c).mpr (by rw [hfb]; simp))
      have he : exec μ (.call c) = some μ := by
        simp only [exec, hfb]
        exact body_read hca (hH.live _ a hca) b (hB.bodies c b hfb)
      obtain ⟨μ', e', hz⟩ := run_sound p F G μ hB hH h
      exact ⟨μ', (finish he).trans e', hz⟩
    · simp at h
  | .dropFn c :: p, F, G, μ, hB, hH, h => by
    simp only [chk] at h
    split at h
    · rename_i hc
      obtain ⟨b, hfb⟩ := some_of ((hB.fns c).mp hc)
      obtain ⟨a, hca⟩ := some_of ((hB.slots c).mpr (by rw [hfb]; simp))
      have ha := hH.live _ a hca
      have he : exec μ (.dropFn c) = some { μ with st := put μ.st (.clo c) none, heap := put μ.heap a false, fns := put μ.fns c none } := by
        simp [exec, hfb, freeAt, hca, ha] <;> rfl
      have hB1 : Book F (G.filter (fun d => d != c)) { μ with st := put μ.st (.clo c) none, heap := put μ.heap a false, fns := put μ.fns c none } := by
        refine ⟨fun z => ?_, fun d => ?_, fun d => ?_, fun d b' hd => ?_⟩
        · show z ∈ F ↔ put μ.st (.clo c) none (.var z) ≠ none
          rw [put_ne _ _ (by simp)]
          exact hB.vars z
        · show d ∈ G.filter (fun d => d != c) ↔ put μ.fns c none d ≠ none
          by_cases hdc : d = c
          · rw [hdc]
            simp [put]
          · rw [put_ne _ _ hdc, ← hB.fns d]
            simp [hdc]
        · show put μ.st (.clo c) none (.clo d) ≠ none ↔ put μ.fns c none d ≠ none
          by_cases hdc : d = c
          · rw [hdc]
            simp [put]
          · rw [put_ne _ _ (fun e => hdc (Loc.clo.inj e)), put_ne _ _ hdc]
            exact hB.slots d
        · have hd' : put μ.fns c none d = some b' := hd
          by_cases hdc : d = c
          · rw [hdc, put_same] at hd'
            cases hd'
          · rw [put_ne _ _ hdc] at hd'
            exact hB.bodies d b' hd'
      obtain ⟨μ', e', hz⟩ := run_sound p F _ _ hB1 (heap_free hH hca) h
      exact ⟨μ', (finish he).trans e', hz⟩
    · simp at h
  | .apply x b k :: p, F, G, μ, hB, hH, h => by
    simp only [chk] at h
    split at h
    · rename_i hc
      obtain ⟨hxF, hb⟩ := hc
      obtain ⟨a, hx⟩ := some_of ((hB.vars x).mp hxF)
      have he : exec μ (.apply x b k) = some μ := runK_read hx (hH.live _ a hx) hb k
      obtain ⟨μ', e', hz⟩ := run_sound p F G μ hB hH h
      exact ⟨μ', (finish he).trans e', hz⟩
    · simp at h

/-- 定理：通过检查的程序（有借来的闭包、Fn 闭包）运行时不会读到空位或释放了的盒子、不会重复释放，结束时堆是空的 -/
theorem clo_sound (p : List Ins) (h : chk [] [] p = true) :
    ∃ μ', run p start = some μ' ∧ ∀ a, μ'.heap a = false :=
  run_sound p [] [] start
    ⟨fun _ => by simp [start], fun _ => by simp [start], fun _ => by simp [start],
     fun _ _ h => by simp [start] at h⟩
    ⟨fun _ _ h => by simp [start] at h, fun _ _ _ h => by simp [start] at h,
     fun _ h => by simp [start] at h, fun _ h => by simp [start] at h⟩
    h

/-! ## 例子 -/

-- 借来的闭包移走捕获的值、被调用两次：检查不通过；不检查的话第二次读到空位
example : chk [] [] [.new 0, .apply 0 [.mv] 2, .drop 0] = false := by decide
example : (run [.new 0, .apply 0 [.mv] 2] start).isNone = true := by decide
-- Fn 闭包移走副本、被调用两次：一样
example : chk [] [] [.new 0, .mkFn 1 0 [.mv], .call 1, .call 1, .dropFn 1, .drop 0] = false := by decide
example : (run [.new 0, .mkFn 1 0 [.mv], .call 1, .call 1] start).isNone = true := by decide
-- 原来的变量释放以后 Fn 闭包还能调用：它读的是自己的副本
example : chk [] [] [.new 0, .mkFn 1 0 [.rd], .drop 0, .call 1, .call 1, .dropFn 1] = true := by decide
example : (run [.new 0, .mkFn 1 0 [.rd], .drop 0, .call 1, .call 1, .dropFn 1] start).isSome = true := by decide
-- 借来的闭包只读：调用多少次都可以
example : chk [] [] [.new 0, .apply 0 [.rd, .rd] 3, .drop 0] = true := by decide

end Clo
end Lark
