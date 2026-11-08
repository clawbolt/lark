/-
标准库的证明 · 优先队列（std/heap.lark）

照着 std/heap.lark 写一份。元素写成 Nat（Lark 里只用到 Ord 的 <，按全序来看都一样），
items 写成 a : Nat → Nat 加上个数 m，items[i] = v 写成 upd。insert / pop_min 里的空位（None）
不单独记：空位上的值不算数，最后放 x 时盖掉。两个循环写成带燃料的递归，燃料给够（insert 给 m + 1，pop_min 给 m）。

- insert：末尾留空位，x < 父节点时父节点往下挪（相等不挪，和 lt_opt 一样）。
- pop_min：取出根，把最后一个元素 x 从根往下沉：两个孩子里小的那个（右边严格小才选右边）比 x 小就往上挪。

证明：
- 堆的性质 IsHeap（每个节点不小于父节点）在 insert 和 pop_min 后保持；
- 根是最小的（root_le），pop_min 取出来的就是它；
- 个数不变：任何值 v 在堆里出现的次数，insert 后多 x 那一次，pop_min 后少取出的那一次（insert_cnt、popMin_cnt）；
- 连着 pop 出来的不会变小（pop_mono），所以 into_sorted 是从小到大。
-/

namespace Lark
namespace Heap

def par (j : Nat) : Nat := (j - 1) / 2

/-- items[i] = v -/
def upd (a : Nat → Nat) (i v : Nat) : Nat → Nat := fun j => if j = i then v else a j

/-- 每个节点不小于父节点 -/
abbrev IsHeap (a : Nat → Nat) (m : Nat) : Prop := ∀ j, j < m → 0 < j → a (par j) ≤ a j

/-! ## 写：heap.lark 的 insert 和 pop_min -/

/-- insert 的循环：空位在 i，要放的是 x -/
def up : Nat → (Nat → Nat) → Nat → Nat → (Nat → Nat)
  | 0, a, i, x => upd a i x
  | f + 1, a, i, x =>
    if 0 < i ∧ x < a (par i) then up f (upd a i (a (par i))) (par i) x else upd a i x

def insert (a : Nat → Nat) (m x : Nat) : (Nat → Nat) × Nat := (up (m + 1) a m x, m + 1)

/-- 两个孩子里小的那个：右边严格小才选右边（less_at(items, r, l)） -/
def mc (a : Nat → Nat) (m i : Nat) : Nat := if 2 * i + 2 < m ∧ a (2 * i + 2) < a (2 * i + 1) then 2 * i + 2 else 2 * i + 1

/-- pop_min 的循环：空位在 i，要放的是 x，堆里有 m 个 -/
def down : Nat → (Nat → Nat) → Nat → Nat → Nat → (Nat → Nat)
  | 0, a, _, i, x => upd a i x
  | f + 1, a, m, i, x =>
    if 2 * i + 1 < m then
      if a (mc a m i) < x then down f (upd a i (a (mc a m i))) m (mc a m i) x else upd a i x
    else upd a i x

/-- 取出的值、新的 items、新的个数 -/
def popMin (a : Nat → Nat) (n : Nat) : Option Nat × (Nat → Nat) × Nat :=
  if n = 0 then (none, a, 0)
  else if n = 1 then (some (a 0), a, 0)
  else (some (a 0), down (n - 1) a (n - 1) 0 (a (n - 1)), n - 1)

/-! ## 例子 -/

def ofList (xs : List Nat) : (Nat → Nat) × Nat := xs.foldl (fun s x => insert s.1 s.2 x) (fun _ => 0, 0)

/-- 一直 pop 到空（燃料是个数） -/
def drain : Nat → (Nat → Nat) → Nat → List Nat
  | 0, _, _ => []
  | f + 1, a, n =>
    match popMin a n with
    | (some v, b, m) => v :: drain f b m
    | (none, _, _) => []

#guard (ofList [5, 1, 4, 1, 3]).2 == 5
#guard drain 5 (ofList [5, 1, 4, 1, 3]).1 5 == [1, 1, 3, 4, 5]
#guard drain 9 (ofList [9, 8, 7, 6, 5, 4, 3, 2, 1]).1 9 == [1, 2, 3, 4, 5, 6, 7, 8, 9]

/-! ## 堆的性质：insert -/

/-- 空位在 i 时的不变式：别处是堆；空位的孩子不小于空位的父节点；x 不大于空位的孩子 -/
abbrev UpInv (a : Nat → Nat) (m i x : Nat) : Prop :=
  i < m ∧
  (∀ j, j < m → 0 < j → j ≠ i → par j ≠ i → a (par j) ≤ a j) ∧
  (∀ c, c < m → 0 < c → par c = i → 0 < i → a (par i) ≤ a c) ∧
  (∀ c, c < m → 0 < c → par c = i → x ≤ a c)

theorem par_lt {j : Nat} (h : 0 < j) : par j < j := by unfold par; omega

theorem place_up {a : Nat → Nat} {m i x : Nat} (hI : UpInv a m i x) (hs : ¬(0 < i ∧ x < a (par i))) :
    IsHeap (upd a i x) m := by
  intro j hj hj0
  show (if par j = i then x else a (par j)) ≤ (if j = i then x else a j)
  by_cases h1 : j = i
  · have hp : par j ≠ i := by have := par_lt hj0; omega
    rw [ite_eq_right hp, ite_eq_left h1]
    subst h1
    omega
  · rw [ite_eq_right h1]
    by_cases h2 : par j = i
    · rw [ite_eq_left h2]
      exact hI.2.2.2 j hj hj0 h2
    · rw [ite_eq_right h2]
      exact hI.2.1 j hj hj0 h1 h2

theorem step_up {a : Nat → Nat} {m i x : Nat} (hI : UpInv a m i x) (h0 : 0 < i) (hx : x < a (par i)) :
    UpInv (upd a i (a (par i))) m (par i) x := by
  obtain ⟨him, hA, hB, _⟩ := hI
  have hpi : par i < i := par_lt h0
  refine ⟨by omega, ?_, ?_, ?_⟩
  · intro j hj hj0 hjp hpj
    have hji : j ≠ i := by intro h; exact hpj (by rw [h])
    show (if par j = i then a (par i) else a (par j)) ≤ (if j = i then a (par i) else a j)
    rw [ite_eq_right hji]
    by_cases h2 : par j = i
    · rw [ite_eq_left h2]
      exact hB j hj hj0 h2 h0
    · rw [ite_eq_right h2]
      exact hA j hj hj0 hji h2
  · intro c hc hc0 hcp hp0
    have hpp : par (par i) ≠ i := by have := par_lt hp0; omega
    have hAp := hA (par i) (by omega) hp0 (by omega) hpp
    show (if par (par i) = i then a (par i) else a (par (par i))) ≤ (if c = i then a (par i) else a c)
    rw [ite_eq_right hpp]
    by_cases hci : c = i
    · rw [ite_eq_left hci]
      exact hAp
    · rw [ite_eq_right hci]
      have h2 := hA c hc hc0 hci (by rw [hcp]; omega)
      rw [hcp] at h2
      omega
  · intro c hc hc0 hcp
    show x ≤ (if c = i then a (par i) else a c)
    by_cases hci : c = i
    · rw [ite_eq_left hci]
      omega
    · rw [ite_eq_right hci]
      have h2 := hA c hc hc0 hci (by rw [hcp]; omega)
      rw [hcp] at h2
      omega

theorem up_heap : ∀ (f : Nat) (a : Nat → Nat) (m i x : Nat), i < f + 1 → UpInv a m i x → IsHeap (up f a i x) m
  | 0, a, m, i, x, hf, hI => by
    unfold up
    exact place_up hI (by omega)
  | f + 1, a, m, i, x, hf, hI => by
    unfold up
    by_cases hc : 0 < i ∧ x < a (par i)
    · rw [ite_eq_left hc]
      have := par_lt hc.1
      exact up_heap f _ m (par i) x (by omega) (step_up hI hc.1 hc.2)
    · rw [ite_eq_right hc]
      exact place_up hI hc

/-- insert 后还是堆 -/
theorem insert_heap (a : Nat → Nat) (m x : Nat) (h : IsHeap a m) : IsHeap (insert a m x).1 (insert a m x).2 := by
  refine up_heap (m + 1) a (m + 1) m x (by omega) ⟨by omega, ?_, ?_, ?_⟩
  · intro j hj hj0 hjm _
    exact h j (by omega) hj0
  · intro c hc hc0 hcp _
    unfold par at hcp
    omega
  · intro c hc hc0 hcp
    unfold par at hcp
    omega

/-! ## 堆的性质：pop_min -/

theorem mc_ok (a : Nat → Nat) (m i : Nat) (h : 2 * i + 1 < m) :
    par (mc a m i) = i ∧ mc a m i < m ∧ 2 * i + 1 ≤ mc a m i ∧
    (∀ c, c < m → 0 < c → par c = i → a (mc a m i) ≤ a c) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold mc par
    split <;> omega
  · unfold mc
    split <;> omega
  · unfold mc
    split <;> omega
  · intro c hc hc0 hp
    have hc' : c = 2 * i + 1 ∨ c = 2 * i + 2 := by unfold par at hp; omega
    rcases hc' with rfl | rfl <;> (unfold mc; split <;> omega)

/-- 空位在 i 时的不变式：别处是堆；空位的孩子不小于空位的父节点；x 不小于空位的父节点 -/
abbrev DnInv (a : Nat → Nat) (m i x : Nat) : Prop :=
  i < m ∧
  (∀ j, j < m → 0 < j → j ≠ i → par j ≠ i → a (par j) ≤ a j) ∧
  (∀ c, c < m → 0 < c → par c = i → 0 < i → a (par i) ≤ a c) ∧
  (0 < i → a (par i) ≤ x)

theorem place_dn {a : Nat → Nat} {m i x : Nat} (hI : DnInv a m i x) (hs : 2 * i + 1 < m → x ≤ a (mc a m i)) :
    IsHeap (upd a i x) m := by
  intro j hj hj0
  show (if par j = i then x else a (par j)) ≤ (if j = i then x else a j)
  by_cases h1 : j = i
  · have hp : par j ≠ i := by have := par_lt hj0; omega
    rw [ite_eq_right hp, ite_eq_left h1]
    subst h1
    exact hI.2.2.2 hj0
  · rw [ite_eq_right h1]
    by_cases h2 : par j = i
    · rw [ite_eq_left h2]
      have hm : 2 * i + 1 < m := by unfold par at h2; omega
      have h3 := (mc_ok a m i hm).2.2.2 j hj hj0 h2
      have h4 := hs hm
      omega
    · rw [ite_eq_right h2]
      exact hI.2.1 j hj hj0 h1 h2

theorem step_dn {a : Nat → Nat} {m i x : Nat} (hI : DnInv a m i x) (hm : 2 * i + 1 < m) (hx : a (mc a m i) < x) :
    DnInv (upd a i (a (mc a m i))) m (mc a m i) x := by
  obtain ⟨hpc, hcm, hic, hmin⟩ := mc_ok a m i hm
  obtain ⟨_, hA, hB, _⟩ := hI
  refine ⟨hcm, ?_, ?_, ?_⟩
  · intro j hj hj0 hjc hpj
    show (if par j = i then a (mc a m i) else a (par j)) ≤ (if j = i then a (mc a m i) else a j)
    by_cases h1 : j = i
    · have hp : par j ≠ i := by have := par_lt hj0; omega
      rw [ite_eq_right hp, ite_eq_left h1, h1]
      exact hB _ hcm (by omega) hpc (by omega)
    · rw [ite_eq_right h1]
      by_cases h2 : par j = i
      · rw [ite_eq_left h2]
        exact hmin j hj hj0 h2
      · rw [ite_eq_right h2]
        exact hA j hj hj0 h1 h2
  · intro c hc hc0 hcp _
    have hci : c ≠ i := by have := par_lt hc0; omega
    show (if par (mc a m i) = i then a (mc a m i) else a (par (mc a m i))) ≤ (if c = i then a (mc a m i) else a c)
    rw [ite_eq_left hpc, ite_eq_right hci]
    have h2 := hA c hc hc0 hci (by rw [hcp]; omega)
    rw [hcp] at h2
    exact h2
  · intro _
    show (if par (mc a m i) = i then a (mc a m i) else a (par (mc a m i))) ≤ x
    rw [ite_eq_left hpc]
    omega

theorem down_heap : ∀ (f : Nat) (a : Nat → Nat) (m i x : Nat), m ≤ f + 2 * i + 1 → DnInv a m i x →
    IsHeap (down f a m i x) m
  | 0, a, m, i, x, hf, hI => by
    unfold down
    exact place_dn hI (fun _ => by omega)
  | f + 1, a, m, i, x, hf, hI => by
    unfold down
    by_cases hm : 2 * i + 1 < m
    · rw [ite_eq_left hm]
      by_cases hx : a (mc a m i) < x
      · rw [ite_eq_left hx]
        have hic := (mc_ok a m i hm).2.2.1
        exact down_heap f _ m _ x (by omega) (step_dn hI hm hx)
      · rw [ite_eq_right hx]
        exact place_dn hI (fun _ => by omega)
    · rw [ite_eq_right hm]
      exact place_dn hI (fun h => absurd h hm)

/-- pop_min 后还是堆 -/
theorem popMin_heap (a : Nat → Nat) (n : Nat) (h : IsHeap a n) : IsHeap (popMin a n).2.1 (popMin a n).2.2 := by
  unfold popMin
  by_cases h0 : n = 0
  · rw [ite_eq_left h0]
    intro j hj
    exact absurd hj (Nat.not_lt_zero _)
  · rw [ite_eq_right h0]
    by_cases h1 : n = 1
    · rw [ite_eq_left h1]
      intro j hj
      exact absurd hj (Nat.not_lt_zero _)
    · rw [ite_eq_right h1]
      refine down_heap (n - 1) a (n - 1) 0 (a (n - 1)) (by omega) ⟨by omega, ?_, ?_, ?_⟩
      · intro j hj hj0 _ _
        exact h j (by omega) hj0
      · intro _ _ _ _ h00
        exact absurd h00 (Nat.lt_irrefl 0)
      · intro h00
        exact absurd h00 (Nat.lt_irrefl 0)

/-- 根是最小的 -/
theorem root_le (a : Nat → Nat) (n : Nat) (h : IsHeap a n) : ∀ k j, j ≤ k → j < n → a 0 ≤ a j
  | 0, j, hj, _ => by
    have : j = 0 := by omega
    subst this
    exact Nat.le_refl _
  | k + 1, j, hj, hn => by
    by_cases j0 : j = 0
    · subst j0
      exact Nat.le_refl _
    · have hp := par_lt (j := j) (by omega)
      have h1 := root_le a n h k (par j) (by omega) (by omega)
      have h2 := h j hn (by omega)
      omega

/-! ## 个数不变：每个值出现的次数 -/

def sumR (g : Nat → Nat) : Nat → Nat
  | 0 => 0
  | m + 1 => sumR g m + g m

def ind (a : Nat → Nat) (v : Nat) : Nat → Nat := fun j => if a j = v then 1 else 0
/-- 不算空位 h -/
def hind (a : Nat → Nat) (h v : Nat) : Nat → Nat := fun j => if j = h then 0 else if a j = v then 1 else 0

/-- v 在前 m 个里出现的次数 -/
def cnt (a : Nat → Nat) (m v : Nat) : Nat := sumR (ind a v) m
/-- 空位在 h 时，v 在前 m 个里出现的次数 -/
def hcnt (a : Nat → Nat) (m h v : Nat) : Nat := sumR (hind a h v) m

theorem sum_congr (f g : Nat → Nat) : ∀ m, (∀ j, j < m → f j = g j) → sumR f m = sumR g m
  | 0, _ => rfl
  | m + 1, h => by
    show sumR f m + f m = sumR g m + g m
    rw [sum_congr f g m (fun j hj => h j (by omega)), h m (by omega)]

/-- 只有一处不同 -/
theorem sum_pt (f g : Nat → Nat) (p : Nat) : ∀ m, p < m → (∀ j, j ≠ p → f j = g j) →
    sumR f m + g p = sumR g m + f p
  | 0, hp, _ => absurd hp (Nat.not_lt_zero _)
  | m + 1, hp, e => by
    show sumR f m + f m + g p = sumR g m + g m + f p
    by_cases hpm : p = m
    · subst hpm
      have := sum_congr f g p (fun j hj => e j (by omega))
      omega
    · have ih := sum_pt f g p m (by omega) e
      have := e m (fun h => hpm h.symm)
      omega

/-- 有两处不同 -/
theorem sum_pt2 (f g : Nat → Nat) (i p m : Nat) (hi : i < m) (hp : p < m) (hip : i ≠ p)
    (e : ∀ j, j ≠ i → j ≠ p → f j = g j) : sumR f m + g i + g p = sumR g m + f i + f p := by
  have e1 := sum_pt f (upd f i (g i)) i m hi (fun j hj => by simp [upd, hj])
  have e2 := sum_pt (upd f i (g i)) g p m hp (fun j hj => by
    by_cases hji : j = i
    · subst hji
      simp [upd]
    · simp [upd, hji, e j hji hj])
  have u1 : upd f i (g i) i = g i := by simp [upd]
  have u2 : upd f i (g i) p = f p := by simp [upd, Ne.symm hip]
  omega

/-- 把 x 放进空位 -/
theorem cnt_place (a : Nat → Nat) (m i x v : Nat) (hi : i < m) :
    cnt (upd a i x) m v = hcnt a m i v + (if x = v then 1 else 0) := by
  have := sum_pt (ind (upd a i x) v) (hind a i v) i m hi (fun j hj => by simp [ind, hind, upd, hj])
  have f1 : hind a i v i = 0 := by simp [hind]
  have f2 : ind (upd a i x) v i = (if x = v then 1 else 0) := by simp [ind, upd]
  unfold cnt hcnt
  omega

/-- 空位从 i 挪到 p（p 上的值挪到 i） -/
theorem hcnt_step (a : Nat → Nat) (m i p v : Nat) (hi : i < m) (hp : p < m) (hip : i ≠ p) :
    hcnt (upd a i (a p)) m p v = hcnt a m i v := by
  have := sum_pt2 (hind (upd a i (a p)) p v) (hind a i v) i p m hi hp hip
    (fun j hji hjp => by simp [hind, upd, hji, hjp])
  have f1 : hind (upd a i (a p)) p v i = (if a p = v then 1 else 0) := by simp [hind, upd, hip]
  have f2 : hind (upd a i (a p)) p v p = 0 := by simp [hind]
  have f3 : hind a i v i = 0 := by simp [hind]
  have f4 : hind a i v p = (if a p = v then 1 else 0) := by simp [hind, Ne.symm hip]
  unfold hcnt
  omega

theorem up_cnt (m v : Nat) : ∀ (f : Nat) (a : Nat → Nat) (i x : Nat), i < m →
    cnt (up f a i x) m v = hcnt a m i v + (if x = v then 1 else 0)
  | 0, a, i, x, hi => by
    unfold up
    exact cnt_place a m i x v hi
  | f + 1, a, i, x, hi => by
    unfold up
    by_cases hc : 0 < i ∧ x < a (par i)
    · rw [ite_eq_left hc]
      have hp := par_lt hc.1
      rw [up_cnt m v f (upd a i (a (par i))) (par i) x (by omega),
        hcnt_step a m i (par i) v hi (by omega) (by omega)]
    · rw [ite_eq_right hc]
      exact cnt_place a m i x v hi

theorem down_cnt (m v : Nat) : ∀ (f : Nat) (a : Nat → Nat) (i x : Nat), i < m →
    cnt (down f a m i x) m v = hcnt a m i v + (if x = v then 1 else 0)
  | 0, a, i, x, hi => by
    unfold down
    exact cnt_place a m i x v hi
  | f + 1, a, i, x, hi => by
    unfold down
    by_cases hm : 2 * i + 1 < m
    · rw [ite_eq_left hm]
      obtain ⟨_, hcm, hic, _⟩ := mc_ok a m i hm
      by_cases hx : a (mc a m i) < x
      · rw [ite_eq_left hx, down_cnt m v f (upd a i (a (mc a m i))) (mc a m i) x hcm,
          hcnt_step a m i (mc a m i) v hi hcm (by omega)]
      · rw [ite_eq_right hx]
        exact cnt_place a m i x v hi
    · rw [ite_eq_right hm]
      exact cnt_place a m i x v hi

theorem hcnt_last (a : Nat → Nat) (m v : Nat) : hcnt a (m + 1) m v = cnt a m v := by
  unfold hcnt cnt
  show sumR (hind a m v) m + hind a m v m = sumR (ind a v) m
  rw [sum_congr (hind a m v) (ind a v) m (fun j hj => by simp [hind, ind, Nat.ne_of_lt hj])]
  simp [hind]

/-- insert 后，x 多出现一次，别的值次数不变 -/
theorem insert_cnt (a : Nat → Nat) (m x v : Nat) :
    cnt (insert a m x).1 (insert a m x).2 v = cnt a m v + (if x = v then 1 else 0) := by
  show cnt (up (m + 1) a m x) (m + 1) v = _
  rw [up_cnt (m + 1) v (m + 1) a m x (by omega), hcnt_last]

/-- pop_min 取出的是根；取出的那个少一次，别的值次数不变 -/
theorem popMin_cnt (a : Nat → Nat) (n v : Nat) (hn : 0 < n) :
    (popMin a n).1 = some (a 0) ∧ (popMin a n).2.2 = n - 1 ∧
    cnt a n v = cnt (popMin a n).2.1 (popMin a n).2.2 v + (if a 0 = v then 1 else 0) := by
  unfold popMin
  rw [ite_eq_right (by omega : ¬n = 0)]
  by_cases h1 : n = 1
  · rw [ite_eq_left h1]
    subst h1
    refine ⟨rfl, rfl, ?_⟩
    simp [cnt, sumR, ind]
  · rw [ite_eq_right h1]
    refine ⟨rfl, rfl, ?_⟩
    show cnt a n v = cnt (down (n - 1) a (n - 1) 0 (a (n - 1))) (n - 1) v + _
    rw [down_cnt (n - 1) v (n - 1) a 0 (a (n - 1)) (by omega)]
    have e1 : cnt a n v = cnt a (n - 1) v + (if a (n - 1) = v then 1 else 0) := by
      obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
      show cnt a (k + 1) v = cnt a (k + 1 - 1) v + (if a (k + 1 - 1) = v then 1 else 0)
      (rw [Nat.add_sub_cancel]) <;> rfl
    have e2 : cnt a (n - 1) v = hcnt a (n - 1) 0 v + (if a 0 = v then 1 else 0) := by
      have := sum_pt (ind a v) (hind a 0 v) 0 (n - 1) (by omega) (fun j hj => by simp [ind, hind, hj])
      have f1 : hind a 0 v 0 = 0 := by simp [hind]
      have f2 : ind a v 0 = (if a 0 = v then 1 else 0) := rfl
      unfold cnt hcnt
      omega
    omega

/-! ## 连着 pop 出来的不会变小 -/

theorem cnt_pos_of (a : Nat → Nat) (v j : Nat) : ∀ m, j < m → a j = v → 0 < cnt a m v
  | 0, hj, _ => absurd hj (Nat.not_lt_zero _)
  | m + 1, hj, hv => by
    show 0 < sumR (ind a v) m + ind a v m
    by_cases hjm : j = m
    · subst hjm
      have : ind a v j = 1 := by simp [ind, hv]
      omega
    · have := cnt_pos_of a v j m (by omega) hv
      unfold cnt at this
      omega

theorem cnt_pos (a : Nat → Nat) (v : Nat) : ∀ m, 0 < cnt a m v → ∃ j, j < m ∧ a j = v
  | 0, h => absurd h (Nat.lt_irrefl 0)
  | m + 1, h => by
    by_cases hv : a m = v
    · exact ⟨m, by omega, hv⟩
    · have h0 : ind a v m = 0 := by simp [ind, hv]
      have h1 : 0 < cnt a m v := by
        unfold cnt
        have : 0 < sumR (ind a v) m + ind a v m := h
        omega
      obtain ⟨j, hj, hjv⟩ := cnt_pos a v m h1
      exact ⟨j, by omega, hjv⟩

/-- 再 pop 一次，取出来的不比这次小 -/
theorem pop_mono (a : Nat → Nat) (n : Nat) (h : IsHeap a n) (hn : 2 ≤ n) : a 0 ≤ (popMin a n).2.1 0 := by
  obtain ⟨_, hm, _⟩ := popMin_cnt a n 0 (by omega)
  have hb := (popMin_cnt a n ((popMin a n).2.1 0) (by omega)).2.2
  have hpos := cnt_pos_of (popMin a n).2.1 ((popMin a n).2.1 0) 0 (popMin a n).2.2 (by omega) rfl
  obtain ⟨j, hj, hjv⟩ := cnt_pos a ((popMin a n).2.1 0) n (by omega)
  have := root_le a n h j j (Nat.le_refl _) hj
  rw [hjv] at this
  exact this

end Heap
end Lark
