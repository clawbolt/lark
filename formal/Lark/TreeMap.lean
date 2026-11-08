/-
标准库的证明 · 有序表（std/treemap.lark，先证明再写库）

AVL 树，每个节点存高度 h 和子树大小 s。键在这里是 Int；代码只用 `<` 比较键，
所以对任何满足严格全序的 cmp 都一样（两个键谁也不小于谁就当作同一个键）。

规格全部落到中序列表 toList 上（Nipkow《Functional Algorithms, Verified!》的做法）：
- 不变式 Inv：avl（左右高度差 ≤ 1，存的高度和大小都对）且 toList 按键严格递增（Srt）。
- 旋转和 bal 不改变 toList（`toList_bal`），所以有序性只要在列表上证。
- insert：toList 变成 insL（列表上的插入）；get 等于列表上的查找 lookL；
  remove：toList 变成 delL（列表上删掉这个键）；at i 是 toList 的第 i 项。
- 平衡：insert 后高度不变或加 1，remove 后不变或减 1，结果仍是 AVL（`ins_avl`、`del_avl`）。
-/

namespace Lark
namespace TreeMap

inductive T (V : Type) where
  | leaf
  | node (l : T V) (k : Int) (v : V) (r : T V) (h : Nat) (s : Nat)

open T

variable {V : Type}

def ht : T V → Nat
  | leaf => 0
  | node _ _ _ _ h _ => h

def sz : T V → Nat
  | leaf => 0
  | node _ _ _ _ _ s => s

def mk (l : T V) (k : Int) (v : V) (r : T V) : T V :=
  node l k v r (max (ht l) (ht r) + 1) (sz l + sz r + 1)

/-- 右旋（左边高 2）：左孩子的左边不比右边矮时单旋，否则双旋 -/
def rotRL (ll : T V) (lk : Int) (lv : V) : T V → Int → V → T V → T V
  | node lrl lrk lrv lrr _ _, k, v, r => mk (mk ll lk lv lrl) lrk lrv (mk lrr k v r)
  | leaf, k, v, r => mk (mk ll lk lv leaf) k v r

def rotR : T V → Int → V → T V → T V
  | node ll lk lv lr _ _, k, v, r =>
    if ht lr ≤ ht ll then mk ll lk lv (mk lr k v r) else rotRL ll lk lv lr k v r
  | leaf, k, v, r => mk leaf k v r

/-- 左旋（右边高 2），和右旋对称 -/
def rotLR (l : T V) (k : Int) (v : V) : T V → Int → V → T V → T V
  | node rll rlk rlv rlr _ _, rk, rv, rr => mk (mk l k v rll) rlk rlv (mk rlr rk rv rr)
  | leaf, rk, rv, rr => mk l k v (mk leaf rk rv rr)

def rotL (l : T V) (k : Int) (v : V) : T V → T V
  | node rl rk rv rr _ _ =>
    if ht rl ≤ ht rr then mk (mk l k v rl) rk rv rr else rotLR l k v rl rk rv rr
  | leaf => mk l k v leaf

def bal (l : T V) (k : Int) (v : V) (r : T V) : T V :=
  if ht r + 1 < ht l then rotR l k v r
  else if ht l + 1 < ht r then rotL l k v r
  else mk l k v r

def ins (k : Int) (v : V) : T V → T V
  | leaf => node leaf k v leaf 1 1
  | node l a b r h s =>
    if k < a then bal (ins k v l) a b r
    else if a < k then bal l a b (ins k v r)
    else node l a v r h s

def get (x : Int) : T V → Option V
  | leaf => none
  | node l a b r _ _ => if x < a then get x l else if a < x then get x r else some b

/-- 取出 node l a b r 里最小的一项，返回它和剩下的树 -/
def sm : T V → Int → V → T V → Int × V × T V
  | leaf, a, b, r => (a, b, r)
  | node ll la lb lr _ _, a, b, r =>
    let p := sm ll la lb lr
    (p.1, p.2.1, bal p.2.2 a b r)

def del (k : Int) : T V → T V
  | leaf => leaf
  | node l a b r _ _ =>
    if k < a then bal (del k l) a b r
    else if a < k then bal l a b (del k r)
    else match r with
      | leaf => l
      | node rl ra rb rr _ _ =>
        let p := sm rl ra rb rr
        bal l p.1 p.2.1 p.2.2

/-- 中序第 i 项（用子树大小往下找） -/
def at? (i : Nat) : T V → Option (Int × V)
  | leaf => none
  | node l a b r _ _ =>
    if i < sz l then at? i l else if i = sz l then some (a, b) else at? (i - sz l - 1) r

def toList : T V → List (Int × V)
  | leaf => []
  | node l a b r _ _ => toList l ++ (a, b) :: toList r

/-! ## 列表上的规格 -/

def Srt (xs : List (Int × V)) : Prop := xs.Pairwise (fun p q => p.1 < q.1)

def insL (k : Int) (v : V) : List (Int × V) → List (Int × V)
  | [] => [(k, v)]
  | (a, b) :: r => if k < a then (k, v) :: (a, b) :: r else if a < k then (a, b) :: insL k v r else (k, v) :: r

def lookL (x : Int) : List (Int × V) → Option V
  | [] => none
  | (a, b) :: r => if a = x then some b else lookL x r

def delL (k : Int) : List (Int × V) → List (Int × V)
  | [] => []
  | (a, b) :: r => if a = k then delL k r else (a, b) :: delL k r

theorem lookL_insL (k x : Int) (v : V) : ∀ xs : List (Int × V),
    lookL x (insL k v xs) = if x = k then some v else lookL x xs
  | [] => by
    simp only [insL, lookL]
    repeat' split
    all_goals first | rfl | omega
  | (a, b) :: r => by
    have ih := lookL_insL k x v r
    simp only [insL]
    split
    · simp only [lookL]
      repeat' split
      all_goals first | rfl | omega
    · split
      · simp only [lookL]
        rw [ih]
        repeat' split
        all_goals first | rfl | omega
      · simp only [lookL]
        repeat' split
        all_goals first | rfl | omega

theorem lookL_delL (k x : Int) : ∀ xs : List (Int × V),
    lookL x (delL k xs) = if x = k then none else lookL x xs
  | [] => by
    simp only [delL, lookL]
    repeat' split
    all_goals first | rfl | omega
  | (a, b) :: r => by
    have ih := lookL_delL k x r
    simp only [delL]
    split
    · rw [ih]
      simp only [lookL]
      repeat' split
      all_goals first | rfl | omega
    · simp only [lookL]
      rw [ih]
      repeat' split
      all_goals first | rfl | omega

theorem mem_insL (k : Int) (v : V) : ∀ (xs : List (Int × V)) (p : Int × V), p ∈ insL k v xs → p = (k, v) ∨ p ∈ xs
  | [], p, h => by simp only [insL, List.mem_singleton] at h; exact Or.inl h
  | (a, b) :: r, p, h => by
    simp only [insL] at h
    split at h
    · rcases List.mem_cons.1 h with h | h
      · exact Or.inl h
      · exact Or.inr h
    · split at h
      · rcases List.mem_cons.1 h with h | h
        · exact Or.inr (by simp [h])
        · rcases mem_insL k v r p h with h | h
          · exact Or.inl h
          · exact Or.inr (List.mem_cons_of_mem _ h)
      · rcases List.mem_cons.1 h with h | h
        · exact Or.inl h
        · exact Or.inr (List.mem_cons_of_mem _ h)

theorem srt_insL (k : Int) (v : V) : ∀ xs : List (Int × V), Srt xs → Srt (insL k v xs)
  | [], _ => by unfold Srt; simp [insL]
  | (a, b) :: r, h => by
    unfold Srt at h ⊢
    have ⟨hr1, hr2⟩ := List.pairwise_cons.1 h
    simp only [insL]
    by_cases h1 : k < a
    · rw [ite_eq_left h1]
      refine List.pairwise_cons.2 ⟨?_, h⟩
      intro q hq
      rcases List.mem_cons.1 hq with hq | hq
      · subst hq; exact h1
      · have := hr1 q hq; simp only at this ⊢; omega
    · rw [ite_eq_right h1]
      by_cases h3 : a < k
      · rw [ite_eq_left h3]
        refine List.pairwise_cons.2 ⟨?_, srt_insL k v r hr2⟩
        intro q hq
        rcases mem_insL k v r q hq with hq | hq
        · subst hq; exact h3
        · exact hr1 q hq
      · rw [ite_eq_right h3]
        refine List.pairwise_cons.2 ⟨?_, hr2⟩
        intro q hq
        have := hr1 q hq; simp only at this ⊢; omega

theorem mem_delL (k : Int) : ∀ (xs : List (Int × V)) (p : Int × V), p ∈ delL k xs → p ∈ xs
  | [], _, h => h
  | (a, b) :: r, p, h => by
    simp only [delL] at h
    split at h
    · exact List.mem_cons_of_mem _ (mem_delL k r p h)
    · rcases List.mem_cons.1 h with h | h
      · simp [h]
      · exact List.mem_cons_of_mem _ (mem_delL k r p h)

theorem srt_delL (k : Int) : ∀ xs : List (Int × V), Srt xs → Srt (delL k xs)
  | [], _ => List.Pairwise.nil
  | (a, b) :: r, h => by
    unfold Srt at h ⊢
    have ⟨hr1, hr2⟩ := List.pairwise_cons.1 h
    simp only [delL]
    split
    · exact srt_delL k r hr2
    · exact List.pairwise_cons.2 ⟨fun p hp => hr1 p (mem_delL k r p hp), srt_delL k r hr2⟩

/-! ## 列表接在一起时的插入、删除、查找 -/

theorem insL_lt (k : Int) (v : V) (a : Int) (b : V) (R : List (Int × V)) (hk : k < a) :
    ∀ L : List (Int × V), insL k v (L ++ (a, b) :: R) = insL k v L ++ (a, b) :: R
  | [] => by simp only [List.nil_append, insL, hk, ↓reduceIte, List.cons_append]
  | (c, d) :: L => by
    have ih := insL_lt k v a b R hk L
    by_cases h1 : k < c
    · simp only [List.cons_append, insL, h1, ↓reduceIte]
    · by_cases h2 : c < k
      · simp only [List.cons_append, insL, h1, h2, ↓reduceIte, ih]
      · simp only [List.cons_append, insL, h1, h2, ↓reduceIte]

theorem insL_gt (k : Int) (v : V) (a : Int) (b : V) (R : List (Int × V)) (hak : a < k) :
    ∀ L : List (Int × V), (∀ p ∈ L, p.1 < k) → insL k v (L ++ (a, b) :: R) = L ++ (a, b) :: insL k v R
  | [], _ => by
    have h1 : ¬k < a := by omega
    simp only [List.nil_append, insL, h1, hak, ↓reduceIte]
  | (c, d) :: L, hL => by
    have hc : c < k := hL (c, d) (List.mem_cons_self ..)
    have h1 : ¬k < c := by omega
    have ih := insL_gt k v a b R hak L (fun p hp => hL p (List.mem_cons_of_mem _ hp))
    simp only [List.cons_append, insL, h1, hc, ↓reduceIte, ih]

theorem insL_eq (k : Int) (v b : V) (R : List (Int × V)) :
    ∀ L : List (Int × V), (∀ p ∈ L, p.1 < k) → insL k v (L ++ (k, b) :: R) = L ++ (k, v) :: R
  | [], _ => by
    have h1 : ¬k < k := by omega
    simp only [List.nil_append, insL, h1, ↓reduceIte]
  | (c, d) :: L, hL => by
    have hc : c < k := hL (c, d) (List.mem_cons_self ..)
    have h1 : ¬k < c := by omega
    have ih := insL_eq k v b R L (fun p hp => hL p (List.mem_cons_of_mem _ hp))
    simp only [List.cons_append, insL, h1, hc, ↓reduceIte, ih]

theorem delL_app (k : Int) : ∀ L R : List (Int × V), delL k (L ++ R) = delL k L ++ delL k R
  | [], _ => rfl
  | (c, d) :: L, R => by
    have ih := delL_app k L R
    by_cases h : c = k
    · simp only [List.cons_append, delL, h, ↓reduceIte, ih]
    · simp only [List.cons_append, delL, h, ↓reduceIte, ih]

theorem delL_id (k : Int) : ∀ L : List (Int × V), (∀ p ∈ L, p.1 ≠ k) → delL k L = L
  | [], _ => rfl
  | (c, d) :: L, hL => by
    have hc : ¬c = k := hL (c, d) (List.mem_cons_self ..)
    simp only [delL, hc, ↓reduceIte, delL_id k L (fun p hp => hL p (List.mem_cons_of_mem _ hp))]

theorem lookL_none (x : Int) : ∀ R : List (Int × V), (∀ p ∈ R, p.1 ≠ x) → lookL x R = none
  | [], _ => rfl
  | (c, d) :: R, h => by
    have hc : ¬c = x := h (c, d) (List.mem_cons_self ..)
    simp only [lookL, hc, ↓reduceIte, lookL_none x R (fun p hp => h p (List.mem_cons_of_mem _ hp))]

theorem lookL_app_l (x : Int) (R : List (Int × V)) (hR : ∀ p ∈ R, p.1 ≠ x) :
    ∀ L : List (Int × V), lookL x (L ++ R) = lookL x L
  | [] => lookL_none x R hR
  | (c, d) :: L => by
    by_cases hc : c = x
    · simp only [List.cons_append, lookL, hc, ↓reduceIte]
    · simp only [List.cons_append, lookL, hc, ↓reduceIte, lookL_app_l x R hR L]

theorem lookL_app_r (x : Int) (R : List (Int × V)) :
    ∀ L : List (Int × V), (∀ p ∈ L, p.1 ≠ x) → lookL x (L ++ R) = lookL x R
  | [], _ => rfl
  | (c, d) :: L, hL => by
    have hc : ¬c = x := hL (c, d) (List.mem_cons_self ..)
    simp only [List.cons_append, lookL, hc, ↓reduceIte,
      lookL_app_r x R L (fun p hp => hL p (List.mem_cons_of_mem _ hp))]

/-! ## 旋转不改变中序，insert / remove / get 落到列表上 -/

theorem toList_mk (l : T V) (k : Int) (v : V) (r : T V) : toList (mk l k v r) = toList l ++ (k, v) :: toList r := rfl

theorem toList_rotR (l : T V) (k : Int) (v : V) (r : T V) : toList (rotR l k v r) = toList l ++ (k, v) :: toList r := by
  cases l with
  | leaf => rfl
  | node ll lk lv lr h s =>
    simp only [rotR]
    split
    · simp [toList_mk, toList]
    · cases lr with
      | leaf => simp [rotRL, toList_mk, toList]
      | node lrl lrk lrv lrr _ _ => simp [rotRL, toList_mk, toList]

theorem toList_rotL (l : T V) (k : Int) (v : V) (r : T V) : toList (rotL l k v r) = toList l ++ (k, v) :: toList r := by
  cases r with
  | leaf => rfl
  | node rl rk rv rr h s =>
    simp only [rotL]
    split
    · simp [toList_mk, toList]
    · cases rl with
      | leaf => simp [rotLR, toList_mk, toList]
      | node rll rlk rlv rlr _ _ => simp [rotLR, toList_mk, toList]

theorem toList_bal (l : T V) (k : Int) (v : V) (r : T V) : toList (bal l k v r) = toList l ++ (k, v) :: toList r := by
  unfold bal
  split
  · exact toList_rotR ..
  · split
    · exact toList_rotL ..
    · rfl

theorem srt_node {l : T V} {a : Int} {b : V} {r : T V} (h : Srt (toList l ++ (a, b) :: toList r)) :
    Srt (toList l) ∧ Srt (toList r) ∧ (∀ p ∈ toList l, p.1 < a) ∧ (∀ p ∈ toList r, a < p.1) := by
  unfold Srt at *
  obtain ⟨h1, h2, h3⟩ := List.pairwise_append.1 h
  obtain ⟨h4, h5⟩ := List.pairwise_cons.1 h2
  exact ⟨h1, h5, fun p hp => h3 p hp (a, b) (List.mem_cons_self ..), h4⟩

/-- get 就是在中序列表里找 -/
theorem get_ok (x : Int) : ∀ t : T V, Srt (toList t) → get x t = lookL x (toList t)
  | leaf, _ => rfl
  | node l a b r h s, hs => by
    obtain ⟨h1, h2, h3, h4⟩ := srt_node (l := l) (a := a) (b := b) (r := r) hs
    simp only [get, toList]
    by_cases c1 : x < a
    · have hR : ∀ p ∈ (a, b) :: toList r, p.1 ≠ x := fun p hp => by
        rcases List.mem_cons.1 hp with hp | hp
        · rw [hp]; show a ≠ x; omega
        · have := h4 p hp; omega
      rw [ite_eq_left c1, get_ok x l h1, lookL_app_l x ((a, b) :: toList r) hR (toList l)]
    · have hL : ∀ p ∈ toList l, p.1 ≠ x := fun p hp => by have := h3 p hp; omega
      rw [ite_eq_right c1, lookL_app_r x ((a, b) :: toList r) (toList l) hL]
      simp only [lookL]
      by_cases c2 : a < x
      · rw [ite_eq_left c2, get_ok x r h2, ite_eq_right (by omega : ¬a = x)]
      · rw [ite_eq_right c2, ite_eq_left (by omega : a = x)]

/-- insert 之后的中序列表 = 在列表上 insL -/
theorem ins_toList (k : Int) (v : V) : ∀ t : T V, Srt (toList t) → toList (ins k v t) = insL k v (toList t)
  | leaf, _ => rfl
  | node l a b r h s, hs => by
    obtain ⟨h1, h2, h3, h4⟩ := srt_node (l := l) (a := a) (b := b) (r := r) hs
    simp only [ins, toList]
    by_cases c1 : k < a
    · rw [ite_eq_left c1, toList_bal, ins_toList k v l h1, insL_lt k v a b _ c1]
    · rw [ite_eq_right c1]
      by_cases c2 : a < k
      · rw [ite_eq_left c2, toList_bal, ins_toList k v r h2,
          insL_gt k v a b (toList r) c2 (toList l) (fun p hp => by have := h3 p hp; omega)]
      · rw [ite_eq_right c2]
        have e : k = a := by omega
        simp only [toList]
        rw [e, insL_eq a v b (toList r) (toList l) h3]

theorem sm_toList : ∀ (l : T V) (a : Int) (b : V) (r : T V),
    ((sm l a b r).1, (sm l a b r).2.1) :: toList (sm l a b r).2.2 = toList l ++ (a, b) :: toList r
  | leaf, _, _, _ => rfl
  | node ll la lb lr _ _, a, b, r => by
    have ih := sm_toList ll la lb lr
    simp only [sm, toList_bal, toList]
    rw [← List.cons_append, ih]

/-- remove 之后的中序列表 = 在列表上 delL -/
theorem del_toList (k : Int) : ∀ t : T V, Srt (toList t) → toList (del k t) = delL k (toList t)
  | leaf, _ => rfl
  | node l a b r h s, hs => by
    obtain ⟨h1, h2, h3, h4⟩ := srt_node (l := l) (a := a) (b := b) (r := r) hs
    have hA : k < a → ∀ p ∈ (a, b) :: toList r, p.1 ≠ k := fun c p hp => by
      rcases List.mem_cons.1 hp with hp | hp
      · rw [hp]; show a ≠ k; omega
      · have := h4 p hp; omega
    have hB : a ≤ k → ∀ p ∈ toList l, p.1 ≠ k := fun c p hp => by
      have := h3 p hp; omega
    simp only [del, toList]
    rw [delL_app]
    by_cases c1 : k < a
    · rw [ite_eq_left c1, toList_bal, del_toList k l h1, delL_id k ((a, b) :: toList r) (hA c1)]
    · rw [ite_eq_right c1]
      by_cases c2 : a < k
      · rw [ite_eq_left c2, toList_bal, del_toList k r h2, delL_id k (toList l) (hB (by omega))]
        simp only [delL]
        rw [ite_eq_right (by omega : ¬a = k)]
      · rw [ite_eq_right c2, delL_id k (toList l) (hB (by omega))]
        simp only [delL]
        rw [ite_eq_left (by omega : a = k), delL_id k (toList r) (fun p hp => by have := h4 p hp; omega)]
        cases r with
        | leaf => simp only [toList, List.append_nil]
        | node rl ra rb rr _ _ =>
          simp only [toList]
          rw [toList_bal, ← sm_toList rl ra rb rr]

/-! ## 平衡：AVL，存的高度和大小都对 -/

def avl : T V → Prop
  | leaf => True
  | node l _ _ r h s => avl l ∧ avl r ∧ ht l ≤ ht r + 1 ∧ ht r ≤ ht l + 1 ∧
      h = max (ht l) (ht r) + 1 ∧ s = sz l + sz r + 1

theorem avl_node {l r : T V} {k : Int} {v : V} {h s : Nat} :
    avl (node l k v r h s) ↔ avl l ∧ avl r ∧ ht l ≤ ht r + 1 ∧ ht r ≤ ht l + 1 ∧
      h = max (ht l) (ht r) + 1 ∧ s = sz l + sz r + 1 := Iff.rfl

theorem ht_mk (l : T V) (k : Int) (v : V) (r : T V) : ht (mk l k v r) = max (ht l) (ht r) + 1 := rfl

theorem avl_mk {l r : T V} {k : Int} {v : V} (hl : avl l) (hr : avl r) (h1 : ht l ≤ ht r + 1) (h2 : ht r ≤ ht l + 1) :
    avl (mk l k v r) := avl_node.2 ⟨hl, hr, h1, h2, rfl, rfl⟩

/-- 左边高 2 时右旋：结果是 AVL，高度是 ht l 或 ht l + 1 -/
theorem rotR_ok {l r : T V} {k : Int} {v : V} (hl : avl l) (hr : avl r) (he : ht l = ht r + 2) :
    avl (rotR l k v r) ∧ (ht (rotR l k v r) = ht l + 1 ∨ ht (rotR l k v r) = ht l) := by
  cases l with
  | leaf => exact absurd he (by show ¬(0 = ht r + 2); omega)
  | node ll lk lv lr h s =>
    obtain ⟨hll, hlr, b1, b2, hh, _⟩ := avl_node.1 hl
    have e1 : ht (node ll lk lv lr h s) = h := rfl
    simp only [rotR]
    split
    · refine ⟨avl_mk hll (avl_mk hlr hr ?_ ?_) ?_ ?_, ?_⟩ <;> (try simp only [ht_mk]) <;> omega
    · rename_i c
      cases lr with
      | leaf => exact absurd (Nat.zero_le _) c
      | node lrl lrk lrv lrr h' s' =>
        obtain ⟨h3, h4, b3, b4, hh', _⟩ := avl_node.1 hlr
        have e2 : ht (node lrl lrk lrv lrr h' s') = h' := rfl
        simp only [rotRL]
        refine ⟨avl_mk (avl_mk hll h3 ?_ ?_) (avl_mk h4 hr ?_ ?_) ?_ ?_, ?_⟩ <;> (try simp only [ht_mk]) <;> omega

/-- 右边高 2 时左旋 -/
theorem rotL_ok {l r : T V} {k : Int} {v : V} (hl : avl l) (hr : avl r) (he : ht r = ht l + 2) :
    avl (rotL l k v r) ∧ (ht (rotL l k v r) = ht r + 1 ∨ ht (rotL l k v r) = ht r) := by
  cases r with
  | leaf => exact absurd he (by show ¬(0 = ht l + 2); omega)
  | node rl rk rv rr h s =>
    obtain ⟨hrl, hrr, b1, b2, hh, _⟩ := avl_node.1 hr
    have e1 : ht (node rl rk rv rr h s) = h := rfl
    simp only [rotL]
    split
    · refine ⟨avl_mk (avl_mk hl hrl ?_ ?_) hrr ?_ ?_, ?_⟩ <;> (try simp only [ht_mk]) <;> omega
    · rename_i c
      cases rl with
      | leaf => exact absurd (Nat.zero_le _) c
      | node rll rlk rlv rlr h' s' =>
        obtain ⟨h3, h4, b3, b4, hh', _⟩ := avl_node.1 hrl
        have e2 : ht (node rll rlk rlv rlr h' s') = h' := rfl
        simp only [rotLR]
        refine ⟨avl_mk (avl_mk hl h3 ?_ ?_) (avl_mk h4 hrr ?_ ?_) ?_ ?_, ?_⟩ <;> (try simp only [ht_mk]) <;> omega

/-- bal：两边高度差不超过 2 时，结果是 AVL；高度等于直接接起来的高度，只有转过时可能矮 1 -/
theorem bal_ok {l r : T V} {k : Int} {v : V} (hl : avl l) (hr : avl r) (h1 : ht l ≤ ht r + 2) (h2 : ht r ≤ ht l + 2) :
    avl (bal l k v r) ∧ (ht (bal l k v r) = max (ht l) (ht r) + 1 ∨
      (ht (bal l k v r) + 1 = max (ht l) (ht r) + 1 ∧ (ht r + 1 < ht l ∨ ht l + 1 < ht r))) := by
  unfold bal
  split
  · rename_i c
    obtain ⟨a1, a2⟩ := rotR_ok (k := k) (v := v) hl hr (by omega)
    exact ⟨a1, by omega⟩
  · split
    · rename_i c c'
      obtain ⟨a1, a2⟩ := rotL_ok (k := k) (v := v) hl hr (by omega)
      exact ⟨a1, by omega⟩
    · rename_i c c'
      exact ⟨avl_mk hl hr (by omega) (by omega), Or.inl rfl⟩

/-- insert 之后还是 AVL，高度不变或加 1 -/
theorem ins_avl (k : Int) (v : V) : ∀ t : T V, avl t →
    avl (ins k v t) ∧ (ht (ins k v t) = ht t ∨ ht (ins k v t) = ht t + 1)
  | leaf, _ => ⟨avl_node.2 ⟨trivial, trivial, Nat.le_succ _, Nat.le_succ _, rfl, rfl⟩, Or.inr rfl⟩
  | node l a b r h s, hv => by
    obtain ⟨hl, hr, b1, b2, hh, hs⟩ := avl_node.1 hv
    have e : ht (node l a b r h s) = h := rfl
    simp only [ins]
    by_cases c1 : k < a
    · rw [ite_eq_left c1]
      obtain ⟨i1, i2⟩ := ins_avl k v l hl
      obtain ⟨a1, a2⟩ := bal_ok (k := a) (v := b) i1 hr (by omega) (by omega)
      exact ⟨a1, by omega⟩
    · rw [ite_eq_right c1]
      by_cases c2 : a < k
      · rw [ite_eq_left c2]
        obtain ⟨i1, i2⟩ := ins_avl k v r hr
        obtain ⟨a1, a2⟩ := bal_ok (k := a) (v := b) hl i1 (by omega) (by omega)
        exact ⟨a1, by omega⟩
      · rw [ite_eq_right c2]
        exact ⟨avl_node.2 ⟨hl, hr, b1, b2, hh, hs⟩, Or.inl rfl⟩

/-- 取出最小项之后还是 AVL，高度不变或减 1 -/
theorem sm_avl : ∀ (l : T V) (a : Int) (b : V) (r : T V) (h s : Nat), avl (node l a b r h s) →
    avl (sm l a b r).2.2 ∧ (ht (sm l a b r).2.2 = h ∨ ht (sm l a b r).2.2 + 1 = h)
  | leaf, a, b, r, h, s, hv => by
    obtain ⟨_, hr, b1, b2, hh, _⟩ := avl_node.1 hv
    have e : ht (leaf : T V) = 0 := rfl
    exact ⟨hr, by show ht r = h ∨ ht r + 1 = h; omega⟩
  | node ll la lb lr hl' sl, a, b, r, h, s, hv => by
    obtain ⟨hl, hr, b1, b2, hh, _⟩ := avl_node.1 hv
    have e : ht (node ll la lb lr hl' sl) = hl' := rfl
    obtain ⟨i1, i2⟩ := sm_avl ll la lb lr hl' sl hl
    simp only [sm]
    obtain ⟨a1, a2⟩ := bal_ok (k := a) (v := b) i1 hr (by omega) (by omega)
    exact ⟨a1, by omega⟩

/-- remove 之后还是 AVL，高度不变或减 1 -/
theorem del_avl (k : Int) : ∀ t : T V, avl t →
    avl (del k t) ∧ (ht (del k t) = ht t ∨ ht (del k t) + 1 = ht t)
  | leaf, _ => ⟨trivial, Or.inl rfl⟩
  | node l a b r h s, hv => by
    obtain ⟨hl, hr, b1, b2, hh, hs⟩ := avl_node.1 hv
    have e : ht (node l a b r h s) = h := rfl
    simp only [del]
    by_cases c1 : k < a
    · rw [ite_eq_left c1]
      obtain ⟨i1, i2⟩ := del_avl k l hl
      obtain ⟨a1, a2⟩ := bal_ok (k := a) (v := b) i1 hr (by omega) (by omega)
      exact ⟨a1, by omega⟩
    · rw [ite_eq_right c1]
      by_cases c2 : a < k
      · rw [ite_eq_left c2]
        obtain ⟨i1, i2⟩ := del_avl k r hr
        obtain ⟨a1, a2⟩ := bal_ok (k := a) (v := b) hl i1 (by omega) (by omega)
        exact ⟨a1, by omega⟩
      · rw [ite_eq_right c2]
        cases r with
        | leaf =>
          have e2 : ht (leaf : T V) = 0 := rfl
          simp only
          exact ⟨hl, by omega⟩
        | node rl ra rb rr hr' sr =>
          have e2 : ht (node rl ra rb rr hr' sr) = hr' := rfl
          obtain ⟨i1, i2⟩ := sm_avl rl ra rb rr hr' sr hr
          simp only
          obtain ⟨a1, a2⟩ := bal_ok (k := (sm rl ra rb rr).1) (v := (sm rl ra rb rr).2.1) hl i1 (by omega) (by omega)
          exact ⟨a1, by omega⟩

/-! ## 大小和按序号取 -/

theorem sz_ok : ∀ t : T V, avl t → sz t = (toList t).length
  | leaf, _ => rfl
  | node l a b r h s, hv => by
    obtain ⟨hl, hr, _, _, _, hs⟩ := avl_node.1 hv
    have e1 := sz_ok l hl
    have e2 := sz_ok r hr
    show s = (toList l ++ (a, b) :: toList r).length
    simp only [List.length_append, List.length_cons]
    omega

/-- at i 是中序列表的第 i 项 -/
theorem at_ok : ∀ (t : T V) (i : Nat), avl t → at? i t = (toList t)[i]?
  | leaf, i, _ => by simp [at?, toList]
  | node l a b r h s, i, hv => by
    obtain ⟨hl, hr, _, _, _, _⟩ := avl_node.1 hv
    have e1 := sz_ok l hl
    simp only [at?, toList]
    by_cases c1 : i < sz l
    · have h1 : i < (toList l).length := by omega
      rw [ite_eq_left c1, at_ok l i hl, List.getElem?_append_left h1]
    · have h1 : (toList l).length ≤ i := by omega
      rw [ite_eq_right c1, List.getElem?_append_right h1]
      by_cases c2 : i = sz l
      · have h2 : i - (toList l).length = 0 := by omega
        rw [ite_eq_left c2, h2, List.getElem?_cons_zero]
      · have h2 : i - (toList l).length = (i - sz l - 1) + 1 := by omega
        rw [ite_eq_right c2, h2, List.getElem?_cons_succ, at_ok r _ hr]

/-! ## 合起来 -/

/-- 不变式：AVL，中序按键严格递增 -/
def Inv (t : T V) : Prop := avl t ∧ Srt (toList t)

theorem empty_ok : Inv (leaf : T V) := ⟨trivial, List.Pairwise.nil⟩

/-- insert：不变式保持；中序列表是 insL；之后 get k 是 v，别的键不变 -/
theorem insert_ok (k : Int) (v : V) (t : T V) (hi : Inv t) :
    Inv (ins k v t) ∧ toList (ins k v t) = insL k v (toList t) ∧
    ∀ x, get x (ins k v t) = if x = k then some v else get x t := by
  have e := ins_toList k v t hi.2
  have s' : Srt (toList (ins k v t)) := by rw [e]; exact srt_insL k v _ hi.2
  refine ⟨⟨(ins_avl k v t hi.1).1, s'⟩, e, fun x => ?_⟩
  rw [get_ok x _ s', get_ok x t hi.2, e, lookL_insL]

/-- remove：不变式保持；中序列表是 delL；之后 get k 是 None，别的键不变 -/
theorem remove_ok (k : Int) (t : T V) (hi : Inv t) :
    Inv (del k t) ∧ toList (del k t) = delL k (toList t) ∧
    ∀ x, get x (del k t) = if x = k then none else get x t := by
  have e := del_toList k t hi.2
  have s' : Srt (toList (del k t)) := by rw [e]; exact srt_delL k _ hi.2
  refine ⟨⟨(del_avl k t hi.1).1, s'⟩, e, fun x => ?_⟩
  rw [get_ok x _ s', get_ok x t hi.2, e, lookL_delL]

end TreeMap
end Lark
