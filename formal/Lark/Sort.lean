/-
标准库的证明 · 排序（std/sort.lark）

照着 std/sort.lark 写一份（Sort 是 Lean 的关键字，名字空间叫 Msort）。元素写成 (键, 标记)：比较只看键，标记用来看稳定性。比较函数是 sorted 用的那个
（a < b 时 -1，b < a 时 1，否则 0）。msort_by、merge_by 写成带燃料的递归（燃料给长度就够）。

merge_by 从两个列表的末尾往前合并、每次取较大的、相等时先取 b 的，最后倒一次：写成 merge a b =
(mergeF a.reverse b.reverse).reverse，mergeF 合并两个从大到小的列表，相等时先取第二个。

要证的（分几步）：
- 排好的结果从小到大；
- 稳定、不多不少：对每个键 k，结果里键是 k 的元素，和原来列表里键是 k 的元素一模一样、先后也一样
  （所以结果是原来的一个排列）；
- lower_bound、upper_bound、binary_search、dedup 照说明的那样。
-/

namespace Lark
namespace Msort

/-- (键, 标记) -/
abbrev Item := Nat × Nat

/-- sorted 用的比较 -/
def cmp (a b : Item) : Int := if a.1 < b.1 then -1 else if b.1 < a.1 then 1 else 0

/-- 合并两个从大到小的列表（merge_by 的循环）：前一个更大时取前一个，否则取后一个 -/
def mergeF : Nat → List Item → List Item → List Item
  | 0, xs, ys => xs ++ ys
  | _ + 1, [], ys => ys
  | _ + 1, x :: xs, [] => x :: xs
  | n + 1, x :: xs, y :: ys =>
    if cmp x y > 0 then x :: mergeF n xs (y :: ys) else y :: mergeF n (x :: xs) ys

/-- merge_by：从末尾往前合并，最后倒一次 -/
def merge (a b : List Item) : List Item := (mergeF (a.length + b.length) a.reverse b.reverse).reverse

/-- msort_by：前 n / 2 个和剩下的分别排好再合并 -/
def msortF : Nat → List Item → List Item
  | 0, xs => xs
  | n + 1, xs =>
    if xs.length ≤ 1 then xs
    else merge (msortF n (xs.take (xs.length / 2))) (msortF n (xs.drop (xs.length / 2)))

def sorted (xs : List Item) : List Item := msortF xs.length xs

/-! ## 例子：和 tests/unit/sort.lark 对上 -/

example : sorted [(3, 0), (1, 1), (3, 2), (2, 3), (1, 4)] = [(1, 1), (1, 4), (2, 3), (3, 0), (3, 2)] := by decide
example : sorted [] = [] := by decide
example : sorted [(5, 0), (4, 1), (3, 2), (2, 3), (1, 4), (0, 5)] =
    [(0, 5), (1, 4), (2, 3), (3, 2), (4, 1), (5, 0)] := by decide

/-! ## 合并 -/

abbrev Desc (l : List Item) : Prop := l.Pairwise (fun x y => y.1 ≤ x.1)
abbrev Asc (l : List Item) : Prop := l.Pairwise (fun x y => x.1 ≤ y.1)

theorem cmp_pos (a b : Item) : cmp a b > 0 ↔ b.1 < a.1 := by
  unfold cmp
  by_cases h1 : a.1 < b.1
  · rw [ite_eq_left h1]
    constructor <;> intro h <;> omega
  · rw [ite_eq_right h1]
    by_cases h2 : b.1 < a.1
    · rw [ite_eq_left h2]
      constructor <;> intro _ <;> omega
    · rw [ite_eq_right h2]
      constructor <;> intro h <;> omega

theorem mem_merge : ∀ (n : Nat) (xs ys : List Item) (z : Item), z ∈ mergeF n xs ys → z ∈ xs ∨ z ∈ ys
  | 0, xs, ys, z, h => by simpa [mergeF] using h
  | _ + 1, [], ys, z, h => Or.inr (by simpa [mergeF] using h)
  | _ + 1, x :: xs, [], z, h => Or.inl (by simpa [mergeF] using h)
  | n + 1, x :: xs, y :: ys, z, h => by
    simp only [mergeF] at h
    split at h
    · rcases List.mem_cons.mp h with e | h
      · rw [e]; exact Or.inl (List.mem_cons_self ..)
      · rcases mem_merge n xs (y :: ys) z h with h | h
        · exact Or.inl (List.mem_cons_of_mem _ h)
        · exact Or.inr h
    · rcases List.mem_cons.mp h with e | h
      · rw [e]; exact Or.inr (List.mem_cons_self ..)
      · rcases mem_merge n (x :: xs) ys z h with h | h
        · exact Or.inl h
        · exact Or.inr (List.mem_cons_of_mem _ h)

/-- 合并两个从大到小的列表，结果也从大到小 -/
theorem desc_merge : ∀ (n : Nat) (xs ys : List Item), xs.length + ys.length ≤ n → Desc xs → Desc ys →
    Desc (mergeF n xs ys)
  | 0, xs, ys, hn, _, _ => by
    have h1 : xs = [] := List.eq_nil_of_length_eq_zero (by omega)
    have h2 : ys = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst h1 h2
    exact List.Pairwise.nil
  | _ + 1, [], ys, _, _, hy => by simpa [mergeF] using hy
  | _ + 1, x :: xs, [], _, hx, _ => by simpa [mergeF] using hx
  | n + 1, x :: xs, y :: ys, hn, hx, hy => by
    have hx' := List.pairwise_cons.mp hx
    have hy' := List.pairwise_cons.mp hy
    simp only [mergeF]
    split
    · rename_i hc
      have hlt := (cmp_pos x y).mp hc
      refine List.pairwise_cons.mpr ⟨fun z hz => ?_, desc_merge n xs (y :: ys) (by simp at hn ⊢; omega) hx'.2 hy⟩
      show z.1 ≤ x.1
      rcases mem_merge n xs (y :: ys) z hz with h | h
      · exact hx'.1 z h
      · rcases List.mem_cons.mp h with e | h
        · rw [e]; omega
        · have : z.1 ≤ y.1 := hy'.1 z h
          omega
    · rename_i hc
      have hle : ¬ y.1 < x.1 := fun h => hc ((cmp_pos x y).mpr h)
      refine List.pairwise_cons.mpr ⟨fun z hz => ?_, desc_merge n (x :: xs) ys (by simp at hn ⊢; omega) hx hy'.2⟩
      show z.1 ≤ y.1
      rcases mem_merge n (x :: xs) ys z hz with h | h
      · rcases List.mem_cons.mp h with e | h
        · rw [e]; omega
        · have : z.1 ≤ x.1 := hx'.1 z h
          omega
      · exact hy'.1 z h

theorem nil_filter (k : Nat) : ∀ l : List Item, (∀ z ∈ l, z.1 < k) → l.filter (fun z => z.1 == k) = []
  | [], _ => rfl
  | z :: l, h => by
    have hz := h z (List.mem_cons_self ..)
    have ih := nil_filter k l (fun w hw => h w (List.mem_cons_of_mem _ hw))
    have h1 : z.1 ≠ k := by omega
    simp [h1, ih]

theorem fc_pos {x : Item} {k : Nat} (h : x.1 = k) (l : List Item) :
    (x :: l).filter (fun z => z.1 == k) = x :: l.filter (fun z => z.1 == k) := by
  simp [h]

theorem fc_neg {x : Item} {k : Nat} (h : x.1 ≠ k) (l : List Item) :
    (x :: l).filter (fun z => z.1 == k) = l.filter (fun z => z.1 == k) := by
  simp [h]

/-- 合并时键是 k 的元素：先是第二个列表里的，再是第一个列表里的，各自的先后不变 -/
theorem filter_merge (k : Nat) : ∀ (n : Nat) (xs ys : List Item), xs.length + ys.length ≤ n → Desc xs → Desc ys →
    (mergeF n xs ys).filter (fun z => z.1 == k) = ys.filter (fun z => z.1 == k) ++ xs.filter (fun z => z.1 == k)
  | 0, xs, ys, hn, _, _ => by
    have h1 : xs = [] := List.eq_nil_of_length_eq_zero (by omega)
    have h2 : ys = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst h1 h2
    rfl
  | _ + 1, [], ys, _, _, _ => by simp [mergeF]
  | _ + 1, x :: xs, [], _, _, _ => by simp [mergeF]
  | n + 1, x :: xs, y :: ys, hn, hx, hy => by
    have hx' := List.pairwise_cons.mp hx
    have hy' := List.pairwise_cons.mp hy
    simp only [mergeF]
    split
    · rename_i hc
      have hlt := (cmp_pos x y).mp hc
      have ih := filter_merge k n xs (y :: ys) (by simp at hn ⊢; omega) hx'.2 hy
      by_cases hk : x.1 = k
      · have hnil : (y :: ys).filter (fun z => z.1 == k) = [] := by
          apply nil_filter
          intro z hz
          rcases List.mem_cons.mp hz with e | hz
          · rw [e]; omega
          · have : z.1 ≤ y.1 := hy'.1 z hz
            omega
        rw [fc_pos hk (mergeF n xs (y :: ys)), ih, hnil, fc_pos hk xs]
        all_goals simp
      · rw [fc_neg hk (mergeF n xs (y :: ys)), ih, fc_neg hk xs]
    · have ih := filter_merge k n (x :: xs) ys (by simp at hn ⊢; omega) hx hy'.2
      by_cases hk : y.1 = k
      · rw [fc_pos hk (mergeF n (x :: xs) ys), ih, fc_pos hk ys]
        all_goals simp
      · rw [fc_neg hk (mergeF n (x :: xs) ys), ih, fc_neg hk ys]

/-! ## merge_by 和 msort_by：从小到大、稳定 -/

theorem filt_rev (p : Item → Bool) : ∀ l : List Item, l.reverse.filter p = (l.filter p).reverse
  | [] => rfl
  | x :: l => by
    rw [List.reverse_cons, List.filter_append, filt_rev p l]
    by_cases h : p x = true
    · simp [h]
    · simp [h]

theorem asc_merge (a b : List Item) (ha : Asc a) (hb : Asc b) : Asc (merge a b) := by
  unfold merge
  apply List.pairwise_reverse.mpr
  exact desc_merge _ _ _ (by simp) (List.pairwise_reverse.mpr ha) (List.pairwise_reverse.mpr hb)

/-- merge_by 后键是 k 的元素：先是 a 里的，再是 b 里的，各自的先后不变 -/
theorem filter_merge2 (k : Nat) (a b : List Item) (ha : Asc a) (hb : Asc b) :
    (merge a b).filter (fun z => z.1 == k) = a.filter (fun z => z.1 == k) ++ b.filter (fun z => z.1 == k) := by
  unfold merge
  rw [filt_rev, filter_merge k _ _ _ (by simp) (List.pairwise_reverse.mpr ha) (List.pairwise_reverse.mpr hb),
    filt_rev, filt_rev, List.reverse_append, List.reverse_reverse, List.reverse_reverse]

theorem asc_small : ∀ xs : List Item, xs.length ≤ 1 → Asc xs
  | [], _ => List.Pairwise.nil
  | [_], _ => by simp
  | _ :: _ :: _, h => by simp at h

theorem half_len {xs : List Item} {n : Nat} (h : xs.length ≤ n + 1) (h1 : ¬ xs.length ≤ 1) :
    (xs.take (xs.length / 2)).length ≤ n ∧ (xs.drop (xs.length / 2)).length ≤ n := by
  simp only [List.length_take, List.length_drop]
  omega

theorem asc_msort : ∀ (n : Nat) (xs : List Item), xs.length ≤ n → Asc (msortF n xs)
  | 0, xs, h => by
    have : xs = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst this
    exact List.Pairwise.nil
  | n + 1, xs, h => by
    simp only [msortF]
    split
    · rename_i h1
      exact asc_small xs h1
    · rename_i h1
      exact asc_merge _ _ (asc_msort n _ (half_len h h1).1) (asc_msort n _ (half_len h h1).2)

theorem filter_msort (k : Nat) : ∀ (n : Nat) (xs : List Item), xs.length ≤ n →
    (msortF n xs).filter (fun z => z.1 == k) = xs.filter (fun z => z.1 == k)
  | 0, xs, _ => by simp only [msortF]
  | n + 1, xs, h => by
    simp only [msortF]
    split
    · rfl
    · rename_i h1
      rw [filter_merge2 k _ _ (asc_msort n _ (half_len h h1).1) (asc_msort n _ (half_len h h1).2),
        filter_msort k n _ (half_len h h1).1, filter_msort k n _ (half_len h h1).2, ← List.filter_append,
        List.take_append_drop]

/-- sorted 的结果从小到大 -/
theorem sorted_asc (xs : List Item) : Asc (sorted xs) := asc_msort _ _ (Nat.le_refl _)

/-- 稳定、不多不少：对每个键 k，结果里键是 k 的元素和原来的一模一样、先后也一样。
    所有的键合起来，结果就是原来的一个排列 -/
theorem sorted_stable (xs : List Item) (k : Nat) :
    (sorted xs).filter (fun z => z.1 == k) = xs.filter (fun z => z.1 == k) :=
  filter_msort k _ _ (Nat.le_refl _)

/-! ## 二分查找：lower_bound、upper_bound、binary_search

列表写成下标到键的函数 a（a i 是 xs[i]），len 是 len(xs)。燃料给 hi - lo 就够：每一步 hi - lo 至少少 1。 -/

/-- 排好了：前面的不比后面的大 -/
abbrev Mono (a : Nat → Nat) (len : Nat) : Prop := ∀ i j, i ≤ j → j < len → a i ≤ a j

def lbF : Nat → (Nat → Nat) → Nat → Nat → Nat → Nat
  | 0, _, _, lo, _ => lo
  | n + 1, a, x, lo, hi =>
    if lo < hi then
      if a (lo + (hi - lo) / 2) < x then lbF n a x (lo + (hi - lo) / 2 + 1) hi else lbF n a x lo (lo + (hi - lo) / 2)
    else lo

def ubF : Nat → (Nat → Nat) → Nat → Nat → Nat → Nat
  | 0, _, _, lo, _ => lo
  | n + 1, a, x, lo, hi =>
    if lo < hi then
      if x < a (lo + (hi - lo) / 2) then ubF n a x lo (lo + (hi - lo) / 2) else ubF n a x (lo + (hi - lo) / 2 + 1) hi
    else lo

def lowerBound (a : Nat → Nat) (len x : Nat) : Nat := lbF len a x 0 len
def upperBound (a : Nat → Nat) (len x : Nat) : Nat := ubF len a x 0 len

def bsearch (a : Nat → Nat) (len x : Nat) : Option Nat :=
  if lowerBound a len x < len ∧ ¬ x < a (lowerBound a len x) then some (lowerBound a len x) else none

/-- r 是第一个不小于 x 的下标 -/
abbrev LB (a : Nat → Nat) (len x r : Nat) : Prop :=
  r ≤ len ∧ (∀ i, i < r → a i < x) ∧ (∀ i, r ≤ i → i < len → x ≤ a i)

/-- r 是第一个比 x 大的下标 -/
abbrev UB (a : Nat → Nat) (len x r : Nat) : Prop :=
  r ≤ len ∧ (∀ i, i < r → a i ≤ x) ∧ (∀ i, r ≤ i → i < len → x < a i)

example : lowerBound (fun i => [1, 2, 2, 3].getD i 0) 4 2 = 1 := by decide
example : upperBound (fun i => [1, 2, 2, 3].getD i 0) 4 2 = 3 := by decide
example : bsearch (fun i => [1, 2, 2, 3].getD i 0) 4 2 = some 1 := by decide
example : bsearch (fun i => [1, 3].getD i 0) 2 2 = none := by decide

theorem lb_inv (a : Nat → Nat) (len x : Nat) (hm : Mono a len) : ∀ (n lo hi : Nat), hi - lo ≤ n → lo ≤ hi → hi ≤ len →
    (∀ i, i < lo → a i < x) → (∀ i, hi ≤ i → i < len → x ≤ a i) → LB a len x (lbF n a x lo hi)
  | 0, lo, hi, hn, h1, h2, h3, h4 => by
    show LB a len x lo
    exact ⟨by omega, h3, fun i h5 h6 => h4 i (by omega) h6⟩
  | n + 1, lo, hi, hn, h1, h2, h3, h4 => by
    simp only [lbF]
    split
    · split
      · rename_i hax
        refine lb_inv a len x hm n _ hi (by omega) (by omega) h2 (fun i h5 => ?_) h4
        have := hm i (lo + (hi - lo) / 2) (by omega) (by omega)
        omega
      · rename_i hax
        refine lb_inv a len x hm n lo _ (by omega) (by omega) (by omega) h3 (fun i h5 h6 => ?_)
        rcases Nat.lt_or_ge i hi with h7 | h7
        · have := hm (lo + (hi - lo) / 2) i h5 h6
          omega
        · exact h4 i h7 h6
    · exact ⟨by omega, h3, fun i h5 h6 => h4 i (by omega) h6⟩

theorem ub_inv (a : Nat → Nat) (len x : Nat) (hm : Mono a len) : ∀ (n lo hi : Nat), hi - lo ≤ n → lo ≤ hi → hi ≤ len →
    (∀ i, i < lo → a i ≤ x) → (∀ i, hi ≤ i → i < len → x < a i) → UB a len x (ubF n a x lo hi)
  | 0, lo, hi, hn, h1, h2, h3, h4 => by
    show UB a len x lo
    exact ⟨by omega, h3, fun i h5 h6 => h4 i (by omega) h6⟩
  | n + 1, lo, hi, hn, h1, h2, h3, h4 => by
    simp only [ubF]
    split
    · split
      · rename_i hax
        refine ub_inv a len x hm n lo _ (by omega) (by omega) (by omega) h3 (fun i h5 h6 => ?_)
        rcases Nat.lt_or_ge i hi with h7 | h7
        · have := hm (lo + (hi - lo) / 2) i h5 h6
          omega
        · exact h4 i h7 h6
      · rename_i hax
        refine ub_inv a len x hm n _ hi (by omega) (by omega) h2 (fun i h5 => ?_) h4
        have := hm i (lo + (hi - lo) / 2) (by omega) (by omega)
        omega
    · exact ⟨by omega, h3, fun i h5 h6 => h4 i (by omega) h6⟩

/-- lower_bound：第一个不小于 x 的下标，都比 x 小时是 len -/
theorem lower_bound_spec (a : Nat → Nat) (len x : Nat) (hm : Mono a len) : LB a len x (lowerBound a len x) :=
  lb_inv a len x hm len 0 len (by omega) (by omega) (Nat.le_refl _) (fun _ h => absurd h (Nat.not_lt_zero _))
    (fun _ h1 h2 => absurd h2 (by omega))

/-- upper_bound：第一个比 x 大的下标 -/
theorem upper_bound_spec (a : Nat → Nat) (len x : Nat) (hm : Mono a len) : UB a len x (upperBound a len x) :=
  ub_inv a len x hm len 0 len (by omega) (by omega) (Nat.le_refl _) (fun _ h => absurd h (Nat.not_lt_zero _))
    (fun _ h1 h2 => absurd h2 (by omega))

/-- upper_bound - lower_bound 是等于 x 的个数：[lower_bound, upper_bound) 里正好是等于 x 的那些下标 -/
theorem bounds_eq (a : Nat → Nat) (len x : Nat) (hm : Mono a len) (i : Nat) (hi : i < len) :
    (lowerBound a len x ≤ i ∧ i < upperBound a len x) ↔ a i = x := by
  obtain ⟨_, L1, L2⟩ := lower_bound_spec a len x hm
  obtain ⟨_, U1, U2⟩ := upper_bound_spec a len x hm
  constructor
  · intro ⟨h1, h2⟩
    have e1 := L2 i h1 hi
    have e2 := U1 i h2
    omega
  · intro he
    constructor
    · rcases Nat.lt_or_ge i (lowerBound a len x) with h | h
      · have := L1 i h
        omega
      · exact h
    · rcases Nat.lt_or_ge i (upperBound a len x) with h | h
      · exact h
      · have := U2 i h hi
        omega

theorem bs_some' {a : Nat → Nat} {len x r i : Nat} (L : LB a len x r)
    (h : (if r < len ∧ ¬ x < a r then some r else none) = some i) : i < len ∧ a i = x ∧ ∀ j, j < i → a j ≠ x := by
  obtain ⟨_, L1, L2⟩ := L
  split at h
  · rename_i hc
    simp only [Option.some.injEq] at h
    subst h
    have := L2 r (Nat.le_refl _) hc.1
    exact ⟨hc.1, by omega, fun j hj => by have := L1 j hj; omega⟩
  · simp at h

theorem bs_none' {a : Nat → Nat} {len x r : Nat} (hm : Mono a len) (L : LB a len x r)
    (h : (if r < len ∧ ¬ x < a r then some r else none) = none) : ∀ j, j < len → a j ≠ x := by
  obtain ⟨_, L1, _⟩ := L
  split at h
  · simp at h
  · rename_i hc
    intro j hj he
    rcases Nat.lt_or_ge j r with h1 | h1
    · have := L1 j h1
      omega
    · have := hm r j h1 hj
      exact hc ⟨by omega, by omega⟩

/-- binary_search 给出 Some(i) 时，xs[i] 等于 x，而且是第一个 -/
theorem bsearch_some {a : Nat → Nat} {len x i : Nat} (hm : Mono a len) (h : bsearch a len x = some i) :
    i < len ∧ a i = x ∧ ∀ j, j < i → a j ≠ x :=
  bs_some' (lower_bound_spec a len x hm) h

/-- binary_search 给出 None 时，没有等于 x 的元素 -/
theorem bsearch_none {a : Nat → Nat} {len x : Nat} (hm : Mono a len) (h : bsearch a len x = none) :
    ∀ j, j < len → a j ≠ x :=
  bs_none' hm (lower_bound_spec a len x hm) h

/-! ## dedup：去掉相邻的重复，只留第一个 -/

/-- dedup 的循环：out 是已经留下的，结果为空或者最后一个不等于 v 时才放进 v -/
def ddF (out : List Nat) : List Nat → List Nat
  | [] => out
  | v :: r => if out = [] ∨ out.getLast? ≠ some v then ddF (out ++ [v]) r else ddF out r

def dedup (l : List Nat) : List Nat := ddF [] l

/-- 换个写法：last 是已经留下的最后一个 -/
def dd' (last : Option Nat) : List Nat → List Nat
  | [] => []
  | v :: r => if last = some v then dd' last r else v :: dd' (some v) r

/-- 相邻的不相同，第一个也不等于 last -/
def good (last : Option Nat) : List Nat → Prop
  | [] => True
  | x :: r => last ≠ some x ∧ good (some x) r

example : dedup [1, 1, 2, 1, 3, 3] = [1, 2, 1, 3] := by decide
example : dedup [] = [] := by decide

theorem last_snoc (l : List Nat) (v : Nat) : (l ++ [v]).getLast? = some v := by
  simp [List.getLast?_append]

theorem ddF_eq : ∀ (l out : List Nat), ddF out l = out ++ dd' out.getLast? l
  | [], out => by simp [ddF, dd']
  | v :: r, out => by
    by_cases hc : out = [] ∨ out.getLast? ≠ some v
    · have h1 : out.getLast? ≠ some v := by
        rcases hc with h | h
        · simp [h]
        · exact h
      rw [ddF, ite_eq_left hc, ddF_eq r (out ++ [v]), last_snoc, dd', ite_eq_right h1]
      simp
    · have h1 : out.getLast? = some v := Decidable.byContradiction fun h => hc (Or.inr h)
      rw [ddF, ite_eq_right hc, ddF_eq r out, dd', ite_eq_left h1]

theorem dedup_eq (l : List Nat) : dedup l = dd' none l := by
  simp [dedup, ddF_eq]

theorem good_dd : ∀ (l : List Nat) (last : Option Nat), good last (dd' last l)
  | [], _ => trivial
  | v :: r, last => by
    by_cases h : last = some v
    · rw [dd', ite_eq_left h]
      exact good_dd r last
    · rw [dd', ite_eq_right h]
      simp only [good]
      exact ⟨h, good_dd r (some v)⟩

theorem dd_sub : ∀ (l : List Nat) (last : Option Nat) (z : Nat), z ∈ dd' last l → z ∈ l
  | [], _, z, h => by simp [dd'] at h
  | v :: r, last, z, h => by
    by_cases hv : last = some v
    · rw [dd', ite_eq_left hv] at h
      exact List.mem_cons_of_mem _ (dd_sub r last z h)
    · rw [dd', ite_eq_right hv] at h
      rcases List.mem_cons.mp h with e | h
      · rw [e]; exact List.mem_cons_self ..
      · exact List.mem_cons_of_mem _ (dd_sub r (some v) z h)

theorem dd_sup : ∀ (l : List Nat) (last : Option Nat) (z : Nat), z ∈ l → z ∈ dd' last l ∨ last = some z
  | [], _, z, h => by simp at h
  | v :: r, last, z, h => by
    by_cases hv : last = some v
    · rw [dd', ite_eq_left hv]
      rcases List.mem_cons.mp h with e | h
      · right; rw [hv, e]
      · exact dd_sup r last z h
    · rw [dd', ite_eq_right hv]
      rcases List.mem_cons.mp h with e | h
      · left; rw [e]; exact List.mem_cons_self ..
      · rcases dd_sup r (some v) z h with h | h
        · exact Or.inl (List.mem_cons_of_mem _ h)
        · left
          simp only [Option.some.injEq] at h
          rw [← h]
          exact List.mem_cons_self ..

theorem dd_strict : ∀ (l : List Nat) (last : Option Nat), l.Pairwise (· ≤ ·) →
    (∀ x ∈ l, ∀ w, last = some w → w ≤ x) →
    (dd' last l).Pairwise (· < ·) ∧ (∀ x ∈ dd' last l, ∀ w, last = some w → w < x)
  | [], _, _, _ => ⟨List.Pairwise.nil, by simp [dd']⟩
  | v :: r, last, hp, hl => by
    have hp' := List.pairwise_cons.mp hp
    have hr : ∀ x ∈ r, ∀ w, last = some w → w ≤ x := fun x hx w hw => hl x (List.mem_cons_of_mem _ hx) w hw
    by_cases h : last = some v
    · rw [dd', ite_eq_left h]
      exact dd_strict r last hp'.2 hr
    · rw [dd', ite_eq_right h]
      have ih := dd_strict r (some v) hp'.2 (fun x hx w hw => by
        simp only [Option.some.injEq] at hw
        rw [← hw]
        exact hp'.1 x hx)
      refine ⟨List.pairwise_cons.mpr ⟨fun x hx => ih.2 x hx v rfl, ih.1⟩, fun x hx w hw => ?_⟩
      have hwv : w ≤ v := hl v (List.mem_cons_self ..) w hw
      rcases List.mem_cons.mp hx with e | hx
      · rw [e]
        have : w ≠ v := fun e2 => h (by rw [hw, e2])
        omega
      · have := ih.2 x hx v rfl
        omega

/-- 结果里相邻的元素都不相同 -/
theorem dedup_good (l : List Nat) : good none (dedup l) := by
  rw [dedup_eq]
  exact good_dd l none

/-- 一个元素也没丢、也没多：在结果里当且仅当在原来的列表里 -/
theorem dedup_mem (l : List Nat) (z : Nat) : z ∈ dedup l ↔ z ∈ l := by
  rw [dedup_eq]
  constructor
  · exact dd_sub l none z
  · intro h
    rcases dd_sup l none z h with h | h
    · exact h
    · exact absurd h (by simp)

/-- 先 sort 再 dedup 就是去重：排好的列表 dedup 以后严格从小到大，所以没有重复 -/
theorem dedup_sorted (l : List Nat) (h : l.Pairwise (· ≤ ·)) : (dedup l).Pairwise (· < ·) := by
  rw [dedup_eq]
  exact (dd_strict l none h (fun _ _ _ hw => absurd hw (by simp))).1

end Msort
end Lark
