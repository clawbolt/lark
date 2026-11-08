/-
标准库的证明 · 字符串（std/str.lark）

照着 std/str.lark 写查找和切开的部分，字符串写成字节的 List Nat，下标按字节算。

- at(s, i, sub) 逐字节比较，写成 atL (s.drop i) sub；index_from 的循环写成带燃料的递归 idx（先比第一个字节）。
- Occ s sub k：sub 正好出现在 s 的第 k 个字节处。
- slice(s, a, b) 是 (s.drop a).take (b - a)；split 最后的 slice(s, start, len(s)) 写成 s.drop start。

证明：
- index_from / find 找到的是从 from 起第一次出现的位置，找不到时后面确实没有（`find_ok`）；
- split：用 sep 接回去就是原来的字符串，切出来的每一段里都没有 sep（`split_join_ok`、`split_free_ok`）；
  sep 只有一个字节时走的逐字节那条路，和一般的那条路结果一样（`split1_eq`）；
- replace_all 就是 split 以后用 rep 接起来（`replaceAll_ok`）；count 是 split 的段数减 1（`count_ok`）；
- cut 在第一个 sep 处切开（`cut_ok`）。
-/

namespace Lark
namespace Str

/-! ## 逐字节比较和出现的位置 -/

/-- sub 是不是 t 的开头（at(s, i, sub) 是 atL (s.drop i) sub） -/
def atL : List Nat → List Nat → Bool
  | _, [] => true
  | [], _ :: _ => false
  | x :: t, y :: sub => x == y && atL t sub

/-- sub 正好出现在 s 的第 k 个字节处 -/
def Occ (s sub : List Nat) (k : Nat) : Prop := ∃ u v, s = u ++ sub ++ v ∧ u.length = k

theorem dropl : ∀ (u w : List Nat), (u ++ w).drop u.length = w
  | [], w => by simp
  | _ :: u, w => by simp [dropl u w]

theorem takel : ∀ (u w : List Nat), (u ++ w).take u.length = u
  | [], w => by simp
  | _ :: u, w => by simp [takel u w]

theorem drop_app_le : ∀ (u w : List Nat) (n : Nat), n ≤ u.length → (u ++ w).drop n = u.drop n ++ w
  | u, w, 0, _ => by simp
  | [], w, n + 1, h => by simp at h
  | _ :: u, w, n + 1, h => by
    simp only [List.cons_append, List.drop_succ_cons]
    exact drop_app_le u w n (by simp at h; omega)

theorem atL_app : ∀ (sub v : List Nat), atL (sub ++ v) sub = true
  | [], v => by simp [atL]
  | y :: sub, v => by simp [atL, atL_app sub v]

theorem atL_eq : ∀ (t sub : List Nat), atL t sub = true → t = sub ++ t.drop sub.length
  | t, [] => by simp
  | [], _ :: _ => by simp [atL]
  | x :: t, y :: sub => by
    intro h
    simp only [atL, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨rfl, h2⟩ := h
    have := atL_eq t sub h2
    simp only [List.length_cons, List.drop_succ_cons, List.cons_append]
    rw [← this]

theorem atL_head : ∀ (t sub : List Nat), sub ≠ [] → atL t sub = true → (t.head? == sub.head?) = true
  | _, [], h, _ => absurd rfl h
  | [], _ :: _, _, h => by simp [atL] at h
  | x :: t, y :: sub, _, h => by
    simp only [atL, Bool.and_eq_true, beq_iff_eq] at h
    simp [h.1]

theorem occ_iff (s sub : List Nat) (k : Nat) :
    Occ s sub k ↔ k + sub.length ≤ s.length ∧ atL (s.drop k) sub = true := by
  constructor
  · rintro ⟨u, v, rfl, rfl⟩
    refine ⟨by simp only [List.length_append]; omega, ?_⟩
    rw [List.append_assoc, dropl u (sub ++ v)]
    exact atL_app sub v
  · rintro ⟨hk, h⟩
    refine ⟨s.take k, (s.drop k).drop sub.length, ?_, ?_⟩
    · rw [List.append_assoc, ← atL_eq _ _ h, List.take_append_drop]
    · simp only [List.length_take]
      omega

/-! ## index_from、find -/

/-- index_from 的循环（sub 不空）：从 i 起，先比第一个字节，对上了才比后面的 -/
def idx (s sub : List Nat) : Nat → Nat → Option Nat
  | 0, _ => none
  | f + 1, i =>
    if i + sub.length ≤ s.length then
      if ((s.drop i).head? == sub.head? && atL (s.drop i) sub) = true then some i else idx s sub f (i + 1)
    else none

/-- index_from(s, sub, i)：sub 为空时是 i（i 不超过长度时）；没有是 none（Lark 里是 -1） -/
def indexFrom (s sub : List Nat) (i : Nat) : Option Nat :=
  if sub = [] then (if i ≤ s.length then some i else none) else idx s sub (s.length + 1) i

#guard indexFrom [97, 98, 97, 98] [97, 98] 1 == some 2
#guard indexFrom [97, 98] [98, 99] 0 == none
#guard indexFrom [97] [] 1 == some 1

theorem idx_some (s sub : List Nat) (hne : sub ≠ []) : ∀ f i j, idx s sub f i = some j →
    i ≤ j ∧ Occ s sub j ∧ ∀ k, i ≤ k → k < j → ¬Occ s sub k
  | 0, i, j, h => by simp [idx] at h
  | f + 1, i, j, h => by
    unfold idx at h
    by_cases hb : i + sub.length ≤ s.length
    · rw [ite_eq_left hb] at h
      by_cases hc : ((s.drop i).head? == sub.head? && atL (s.drop i) sub) = true
      · rw [ite_eq_left hc] at h
        simp only [Option.some.injEq] at h
        subst h
        simp only [Bool.and_eq_true] at hc
        exact ⟨Nat.le_refl _, (occ_iff s sub i).2 ⟨hb, hc.2⟩, fun k h1 h2 => absurd h2 (by omega)⟩
      · rw [ite_eq_right hc] at h
        obtain ⟨h1, h2, h3⟩ := idx_some s sub hne f (i + 1) j h
        refine ⟨by omega, h2, fun k hk1 hk2 hk => ?_⟩
        by_cases hki : k = i
        · rw [hki] at hk
          obtain ⟨_, ha⟩ := (occ_iff s sub i).1 hk
          exact hc (by rw [Bool.and_eq_true]; exact ⟨atL_head _ _ hne ha, ha⟩)
        · exact h3 k (by omega) hk2 hk
    · rw [ite_eq_right hb] at h
      simp at h

theorem idx_none (s sub : List Nat) (hne : sub ≠ []) : ∀ f i, s.length + 1 ≤ f + i → idx s sub f i = none →
    ∀ k, i ≤ k → ¬Occ s sub k
  | 0, i, hf, _, k, hk, ho => by
    have := ((occ_iff s sub k).1 ho).1
    omega
  | f + 1, i, hf, h, k, hk, ho => by
    have hb' := (occ_iff s sub k).1 ho
    unfold idx at h
    by_cases hb : i + sub.length ≤ s.length
    · rw [ite_eq_left hb] at h
      by_cases hc : ((s.drop i).head? == sub.head? && atL (s.drop i) sub) = true
      · rw [ite_eq_left hc] at h
        simp at h
      · rw [ite_eq_right hc] at h
        by_cases hki : k = i
        · rw [hki] at hb'
          exact hc (by rw [Bool.and_eq_true]; exact ⟨atL_head _ _ hne hb'.2, hb'.2⟩)
        · exact idx_none s sub hne f (i + 1) (by omega) h k (by omega) ho
    · have := hb'.1
      omega

/-- index_from / find：找到的是从 i 起第一次出现的位置；找不到时从 i 起都没有 -/
theorem find_ok (s sub : List Nat) (i : Nat) :
    (∀ j, indexFrom s sub i = some j → i ≤ j ∧ Occ s sub j ∧ ∀ k, i ≤ k → k < j → ¬Occ s sub k) ∧
    (indexFrom s sub i = none → ∀ k, i ≤ k → ¬Occ s sub k) := by
  unfold indexFrom
  by_cases he : sub = []
  · subst he
    rw [ite_eq_left (rfl : ([] : List Nat) = [])]
    by_cases hi : i ≤ s.length
    · rw [ite_eq_left hi]
      refine ⟨fun j hj => ?_, fun h => by simp at h⟩
      simp only [Option.some.injEq] at hj
      subst hj
      exact ⟨Nat.le_refl _, (occ_iff s [] i).2 ⟨by simpa using hi, by simp [atL]⟩,
        fun k h1 h2 => absurd h2 (by omega)⟩
    · rw [ite_eq_right hi]
      refine ⟨fun j hj => by simp at hj, fun _ k hk ho => ?_⟩
      have := ((occ_iff s [] k).1 ho).1
      simp at this
      omega
  · rw [ite_eq_right he]
    exact ⟨idx_some s sub he _ i, idx_none s sub he _ i (by omega)⟩

/-! ## split：一般的那条路 -/

def slice (s : List Nat) (a b : Nat) : List Nat := (s.drop a).take (b - a)

/-- 用 sep 把几段接起来（split 的反过来） -/
def join (sep : List Nat) : List (List Nat) → List Nat
  | [] => []
  | [p] => p
  | p :: q :: ps => p ++ sep ++ join sep (q :: ps)

/-- split 的循环：找到下一个 sep 就切一段，找不到时剩下的是最后一段 -/
def splitL (s sep : List Nat) : Nat → Nat → List (List Nat)
  | 0, start => [s.drop start]
  | f + 1, start =>
    match indexFrom s sep start with
    | some i => slice s start i :: splitL s sep f (i + sep.length)
    | none => [s.drop start]

theorem join_cons (sep p : List Nat) : ∀ L : List (List Nat), L ≠ [] → join sep (p :: L) = p ++ sep ++ join sep L
  | [], h => absurd rfl h
  | _ :: _, _ => rfl

theorem splitL_ne (s sep : List Nat) : ∀ f start, splitL s sep f start ≠ []
  | 0, _ => by simp [splitL]
  | f + 1, start => by
    cases h : indexFrom s sep start with
    | none => simp [splitL, h]
    | some i => simp [splitL, h]

/-- 在 i 处出现 sep：从 start 起的部分是 [start, i) 这一段、sep、后面剩下的 -/
theorem cut_at (s sep : List Nat) (start i : Nat) (hs : start ≤ i) (ho : Occ s sep i) :
    s.drop start = slice s start i ++ sep ++ s.drop (i + sep.length) := by
  obtain ⟨u, v, rfl, rfl⟩ := ho
  have e1 : (u ++ sep ++ v).drop start = u.drop start ++ (sep ++ v) := by
    rw [List.append_assoc]
    exact drop_app_le u _ start hs
  have e2 : (u ++ sep ++ v).drop (u.length + sep.length) = v := by
    rw [← List.length_append]
    exact dropl (u ++ sep) v
  have e3 : u.length - start = (u.drop start).length := by simp
  unfold slice
  rw [e1, e2, e3, takel]
  simp

theorem occ_app (a b sub : List Nat) (k : Nat) : Occ a sub k → Occ (a ++ b) sub k := by
  rintro ⟨u, v, rfl, rfl⟩
  exact ⟨u, v ++ b, by simp, rfl⟩

theorem occ_drop (s sub : List Nat) (start k : Nat) (hs : start ≤ s.length) :
    Occ (s.drop start) sub k → Occ s sub (start + k) := by
  rintro ⟨u, v, h, rfl⟩
  refine ⟨s.take start ++ u, v, ?_, ?_⟩
  · simp only [List.append_assoc] at h ⊢
    rw [← h, List.take_append_drop]
  · simp only [List.length_append, List.length_take]
    omega

/-- 用 sep 接回去就是从 start 起的部分 -/
theorem splitL_join (s sep : List Nat) : ∀ f start, join sep (splitL s sep f start) = s.drop start
  | 0, _ => rfl
  | f + 1, start => by
    cases h : indexFrom s sep start with
    | none => simp [splitL, h, join]
    | some i =>
      obtain ⟨h1, h2, _⟩ := (find_ok s sep start).1 i h
      simp only [splitL, h]
      rw [join_cons _ _ _ (splitL_ne s sep f _), splitL_join s sep f, ← cut_at s sep start i h1 h2]

/-- 切出来的每一段里都没有 sep -/
theorem splitL_free (s sep : List Nat) (hne : sep ≠ []) : ∀ f start, start ≤ s.length →
    s.length + 1 ≤ f + start → ∀ p ∈ splitL s sep f start, ∀ k, ¬Occ p sep k
  | 0, _, hs, hf => absurd hf (by omega)
  | f + 1, start, hs, hf => by
    intro p hp k ho
    have hn : 0 < sep.length := by
      cases sep with
      | nil => exact absurd rfl hne
      | cons _ _ => simp
    cases h : indexFrom s sep start with
    | none =>
      simp only [splitL, h, List.mem_singleton] at hp
      subst hp
      exact (find_ok s sep start).2 h (start + k) (by omega) (occ_drop s sep start k hs ho)
    | some i =>
      simp only [splitL, h] at hp
      obtain ⟨h1, h2, h3⟩ := (find_ok s sep start).1 i h
      have hb := ((occ_iff s sep i).1 h2).1
      rcases List.mem_cons.1 hp with rfl | hp
      · have hd := cut_at s sep start i h1 h2
        have ho2 : Occ (s.drop start) sep k := by
          rw [hd, List.append_assoc]
          exact occ_app _ _ _ _ ho
        have hk := ((occ_iff _ sep k).1 ho).1
        have hl : (slice s start i).length = i - start := by
          simp only [slice, List.length_take, List.length_drop]
          omega
        exact h3 (start + k) (by omega) (by omega) (occ_drop s sep start k hs ho2)
      · exact splitL_free s sep hne f (i + sep.length) hb (by omega) p hp k ho

/-! ## split：sep 只有一个字节时逐字节比较的那条路 -/

/-- cur 是当前这一段已经走过的字节（Lark 里是 slice(s, start, i)） -/
def split1 (b : Nat) : List Nat → List Nat → List (List Nat)
  | cur, [] => [cur]
  | cur, x :: s => if x = b then cur :: split1 b [] s else split1 b (cur ++ [x]) s

theorem split1_ne (b : Nat) : ∀ s cur, split1 b cur s ≠ []
  | [], _ => by simp [split1]
  | x :: s, cur => by
    simp only [split1]
    split
    · simp
    · exact split1_ne b s _

theorem split1_join (b : Nat) : ∀ s cur, join [b] (split1 b cur s) = cur ++ s
  | [], cur => by simp [split1, join]
  | x :: s, cur => by
    simp only [split1]
    by_cases hx : x = b
    · rw [ite_eq_left hx, join_cons _ _ _ (split1_ne b s []), split1_join b s [], hx]
      simp
    · rw [ite_eq_right hx, split1_join b s (cur ++ [x])]
      simp

theorem split1_free (b : Nat) : ∀ s cur, b ∉ cur → ∀ p ∈ split1 b cur s, b ∉ p
  | [], cur, hc, p, hp => by
    simp [split1] at hp
    rw [hp]
    exact hc
  | x :: s, cur, hc, p, hp => by
    simp only [split1] at hp
    by_cases hx : x = b
    · rw [ite_eq_left hx] at hp
      rcases List.mem_cons.1 hp with rfl | hp
      · exact hc
      · exact split1_free b s [] (by simp) p hp
    · rw [ite_eq_right hx] at hp
      exact split1_free b s (cur ++ [x]) (by simp [hc, Ne.symm hx]) p hp

/-- 两边都不含 b 时，在第一个 b 处切开是唯一的 -/
theorem cut1 (b : Nat) : ∀ (p q x y : List Nat), b ∉ p → b ∉ q → p ++ b :: x = q ++ b :: y → p = q ∧ x = y
  | [], [], x, y, _, _, h => by simpa using h
  | [], c :: q, x, y, _, hq, h => by
    simp only [List.nil_append, List.cons_append, List.cons.injEq] at h
    obtain ⟨rfl, _⟩ := h
    simp at hq
  | c :: p, [], x, y, hp, _, h => by
    simp only [List.nil_append, List.cons_append, List.cons.injEq] at h
    obtain ⟨rfl, _⟩ := h
    simp at hp
  | c :: p, d :: q, x, y, hp, hq, h => by
    simp only [List.cons_append, List.cons.injEq] at h
    obtain ⟨rfl, h2⟩ := h
    have := cut1 b p q x y (fun m => hp (List.mem_cons_of_mem _ m)) (fun m => hq (List.mem_cons_of_mem _ m)) h2
    exact ⟨by rw [this.1], this.2⟩

/-- 用 [b] 接起来一样、每段都不含 b 的两种切法是同一种 -/
theorem join_uniq (b : Nat) : ∀ (P Q : List (List Nat)), P ≠ [] → Q ≠ [] → (∀ p ∈ P, b ∉ p) →
    (∀ q ∈ Q, b ∉ q) → join [b] P = join [b] Q → P = Q
  | [], _, h, _, _, _, _ => absurd rfl h
  | _ :: _, [], _, h, _, _, _ => absurd rfl h
  | [p], [q], _, _, _, _, e => by
    simp only [join] at e
    rw [e]
  | [p], q :: q2 :: qs, _, _, hP, _, e => by
    simp only [join] at e
    exact absurd (by rw [e]; simp) (hP p (List.mem_singleton_self _))
  | p :: p2 :: ps, [q], _, _, _, hQ, e => by
    simp only [join] at e
    exact absurd (by rw [← e]; simp) (hQ q (List.mem_singleton_self _))
  | p :: p2 :: ps, q :: q2 :: qs, _, _, hP, hQ, e => by
    simp only [join, List.append_assoc, List.singleton_append] at e
    obtain ⟨h1, h2⟩ := cut1 b p q _ _ (hP p (List.mem_cons_self ..)) (hQ q (List.mem_cons_self ..)) e
    rw [h1, join_uniq b (p2 :: ps) (q2 :: qs) (by simp) (by simp)
      (fun x hx => hP x (List.mem_cons_of_mem _ hx)) (fun x hx => hQ x (List.mem_cons_of_mem _ hx)) h2]

theorem mem_occ : ∀ (p : List Nat) (b : Nat), b ∈ p → ∃ k, Occ p [b] k
  | [], b, h => by simp at h
  | x :: p, b, h => by
    by_cases hx : x = b
    · exact ⟨0, [], p, by simp [hx], rfl⟩
    · have h' : b ∈ p := by
        rcases List.mem_cons.1 h with h | h
        · exact absurd h.symm hx
        · exact h
      obtain ⟨k, u, v, e, hk⟩ := mem_occ p b h'
      exact ⟨k + 1, x :: u, v, by subst e; simp, by simp [hk]⟩

/-- 逐字节的那条路和一般的那条路切出来一样 -/
theorem split1_eq (s : List Nat) (b : Nat) : split1 b [] s = splitL s [b] (s.length + 1) 0 := by
  apply join_uniq b _ _ (split1_ne b s []) (splitL_ne s [b] _ 0)
    (split1_free b s [] (by simp))
  · intro q hq hb
    obtain ⟨k, hk⟩ := mem_occ q b hb
    exact splitL_free s [b] (by simp) _ 0 (Nat.zero_le _) (by omega) q hq k hk
  · rw [split1_join, splitL_join]
    simp

/-! ## split、replace_all、count、cut -/

/-- split：sep 为空时整个是一段；只有一个字节时逐字节比较 -/
def split (s sep : List Nat) : List (List Nat) :=
  if sep = [] then [s]
  else if sep.length = 1 then split1 (sep.headD 0) [] s
  else splitL s sep (s.length + 1) 0

#guard split [97, 44, 98, 44] [44] == [[97], [98], []]
#guard split [97, 58, 58, 98] [58, 58] == [[97], [98]]
#guard split [97, 98] [] == [[97, 98]]

theorem split_ok (s sep : List Nat) (hne : sep ≠ []) : split s sep = splitL s sep (s.length + 1) 0 := by
  unfold split
  rw [ite_eq_right hne]
  by_cases h1 : sep.length = 1
  · rw [ite_eq_left h1]
    cases sep with
    | nil => exact absurd rfl hne
    | cons b t =>
      cases t with
      | nil =>
        show split1 b [] s = _
        exact split1_eq s b
      | cons _ _ => simp at h1
  · rw [ite_eq_right h1]

/-- split 以后用 sep 接回去，就是原来的字符串 -/
theorem split_join_ok (s sep : List Nat) (hne : sep ≠ []) : join sep (split s sep) = s := by
  rw [split_ok s sep hne, splitL_join, List.drop_zero]

/-- split 切出来的每一段里都没有 sep -/
theorem split_free_ok (s sep : List Nat) (hne : sep ≠ []) : ∀ p ∈ split s sep, ∀ k, ¬Occ p sep k := by
  rw [split_ok s sep hne]
  exact splitL_free s sep hne _ 0 (Nat.zero_le _) (by omega)

/-- replace_all 的循环：out += slice(s, start, i); out += rep，最后接上剩下的 -/
def replL (s pat rep : List Nat) : Nat → Nat → List Nat
  | 0, start => s.drop start
  | f + 1, start =>
    match indexFrom s pat start with
    | some i => slice s start i ++ rep ++ replL s pat rep f (i + pat.length)
    | none => s.drop start

/-- replace_all：pat 为空、或者一个都没有时原样返回 -/
def replaceAll (s pat rep : List Nat) : List Nat :=
  if pat = [] then s
  else match indexFrom s pat 0 with
    | none => s
    | some _ => replL s pat rep (s.length + 1) 0

-- "aaa" 里的 "aa" 换成 "x"：从左到右、不重叠，是 "xa"
#guard replaceAll [97, 97, 97] [97, 97] [120] == [120, 97]

theorem replL_eq (s pat rep : List Nat) : ∀ f start, replL s pat rep f start = join rep (splitL s pat f start)
  | 0, _ => rfl
  | f + 1, start => by
    cases h : indexFrom s pat start with
    | none => simp [replL, splitL, h, join]
    | some i =>
      simp only [replL, splitL, h]
      rw [join_cons _ _ _ (splitL_ne s pat f _), replL_eq s pat rep f]

/-- replace_all 就是按 pat 切开再用 rep 接起来 -/
theorem replaceAll_ok (s pat rep : List Nat) (hne : pat ≠ []) : replaceAll s pat rep = join rep (split s pat) := by
  unfold replaceAll
  rw [ite_eq_right hne, split_ok s pat hne]
  cases h : indexFrom s pat 0 with
  | none => simp [splitL, h, join]
  | some i =>
    simp only
    rw [replL_eq]

/-- count 的循环：从 i 起不重叠地数 -/
def cntL (s sub : List Nat) : Nat → Nat → Nat
  | 0, _ => 0
  | f + 1, i =>
    match indexFrom s sub i with
    | some j => cntL s sub f (j + sub.length) + 1
    | none => 0

/-- count：sub 为空时是 0 -/
def count (s sub : List Nat) : Nat := if sub = [] then 0 else cntL s sub (s.length + 1) 0

#guard count [97, 97, 97] [97, 97] == 1
#guard count [97, 98, 97, 98] [98] == 2

theorem cntL_eq (s sub : List Nat) : ∀ f start, cntL s sub f start + 1 = (splitL s sub f start).length
  | 0, _ => rfl
  | f + 1, start => by
    cases h : indexFrom s sub start with
    | none => simp [cntL, splitL, h]
    | some j =>
      simp only [cntL, splitL, h, List.length_cons]
      have := cntL_eq s sub f (j + sub.length)
      omega

/-- count 是 split 的段数减 1 -/
theorem count_ok (s sub : List Nat) (hne : sub ≠ []) : count s sub + 1 = (split s sub).length := by
  unfold count
  rw [ite_eq_right hne, split_ok s sub hne]
  exact cntL_eq s sub _ 0

/-- cut：在第一个 sep 处切成两半 -/
def cut (s sep : List Nat) : Option (List Nat × List Nat) :=
  match indexFrom s sep 0 with
  | none => none
  | some i => some (slice s 0 i, s.drop (i + sep.length))

#guard cut [107, 61, 118, 61] [61] == some ([107], [118, 61])

/-- cut 得到 (a, b) 时，s 是 a ++ sep ++ b，并且 a 里面没有更早的 sep -/
theorem cut_ok (s sep a b : List Nat) : cut s sep = some (a, b) →
    s = a ++ sep ++ b ∧ ∀ k, k < a.length → ¬Occ s sep k := by
  unfold cut
  cases h : indexFrom s sep 0 with
  | none => simp
  | some i =>
    simp only [Option.some.injEq, Prod.mk.injEq]
    rintro ⟨rfl, rfl⟩
    obtain ⟨_, h2, h3⟩ := (find_ok s sep 0).1 i h
    have hb := ((occ_iff s sep i).1 h2).1
    refine ⟨by rw [← cut_at s sep 0 i (Nat.zero_le _) h2, List.drop_zero], fun k hk => h3 k (Nat.zero_le _) ?_⟩
    simp only [slice, List.length_take, List.length_drop] at hk
    omega

/-- cut 是 none 时，s 里没有 sep -/
theorem cut_none (s sep : List Nat) : cut s sep = none → ∀ k, ¬Occ s sep k := by
  unfold cut
  cases h : indexFrom s sep 0 with
  | none => exact fun _ k => (find_ok s sep 0).2 h k (Nat.zero_le _)
  | some i => simp

end Str
end Lark
