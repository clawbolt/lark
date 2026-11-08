/-
标准库的证明 · 哈希表（std/map.lark）

照着 std/map.lark 写一份。keys、vals 是列表（按插入顺序），slots 写成 S : Nat → Option Nat（空位 -1 是 none），
槽数 n。槽位的起点 hash(k) ^ seed 再打散，这里写成任意的函数 hf : K → Nat，下标先 % n
（槽数是 2 的幂，& (n - 1) 就是 % n：Nat.and_two_pow_sub_one_eq_mod）。map_slot 的循环写成带燃料的递归 probe。

不变式 WF：键两两不同；槽里存的下标都在 keys 里、两个槽不存同一个下标；每个键从它的起点往后探测，
到它所在的槽之前没有空位；占用的槽数等于键数，并且键数 < n（所以一定有空位，map_slot 会停）。

证明：有这个键时 map_slot 停在它所在的槽（`slot_present`）；没有时停在一个空槽，路上没有空位（`slot_absent`）。
-/
import Lark.Deque
import Lark.Heap

namespace Lark
namespace HMap

open Lark.Heap (sumR)
open Lark.Deque (mod_inj)

structure M (K V : Type) where
  keys : List K
  vals : List V
  S : Nat → Option Nat
  n : Nat

variable {K V : Type} [DecidableEq K] (hf : K → Nat)

/-- map_slot 的循环：空槽或者存着 k 的槽就停 -/
def probe (m : M K V) (k : K) : Nat → Nat → Nat
  | 0, i => i
  | f + 1, i =>
    match m.S i with
    | none => i
    | some j => if m.keys[j]? = some k then i else probe m k f ((i + 1) % m.n)

def slot (m : M K V) (k : K) : Nat := probe m k m.n (hf k % m.n)

def filled (S : Nat → Option Nat) (i : Nat) : Nat := if S i = none then 0 else 1

/-- 占用的槽数 -/
def cnt (S : Nat → Option Nat) (n : Nat) : Nat := sumR (filled S) n

structure WF (m : M K V) : Prop where
  npos : 0 < m.n
  len : m.keys.length = m.vals.length
  nodup : m.keys.Nodup
  lt : m.keys.length < m.n
  rng : ∀ i j, i < m.n → m.S i = some j → j < m.keys.length
  inj : ∀ i i' j, i < m.n → i' < m.n → m.S i = some j → m.S i' = some j → i = i'
  path : ∀ j (hj : j < m.keys.length), ∃ d, d < m.n ∧ m.S ((hf m.keys[j] + d) % m.n) = some j ∧
    ∀ t, t < d → m.S ((hf m.keys[j] + t) % m.n) ≠ none
  count : cnt m.S m.n = m.keys.length

/-! ## 下标和计数 -/

omit [DecidableEq K] in
theorem nd_inj : ∀ (l : List K), l.Nodup → ∀ i j (hi : i < l.length) (hj : j < l.length), l[i] = l[j] → i = j
  | [], _, _, _, hi, _, _ => absurd hi (by simp)
  | _ :: _, _, 0, 0, _, _, _ => rfl
  | x :: l, hnd, 0, j + 1, _, hj, e => by
    have hx := (List.nodup_cons.1 hnd).1
    simp only [List.getElem_cons_zero, List.getElem_cons_succ] at e
    exact absurd (e ▸ List.getElem_mem (by simp at hj; omega)) hx
  | x :: l, hnd, i + 1, 0, hi, _, e => by
    have hx := (List.nodup_cons.1 hnd).1
    simp only [List.getElem_cons_zero, List.getElem_cons_succ] at e
    exact absurd (e ▸ List.getElem_mem (by simp at hi; omega)) hx
  | _ :: l, hnd, i + 1, j + 1, hi, hj, e => by
    simp only [List.getElem_cons_succ] at e
    have := nd_inj l (List.nodup_cons.1 hnd).2 i j (by simp at hi; omega) (by simp at hj; omega) e
    omega

theorem nextpos (s t n : Nat) : ((s + t) % n + 1) % n = (s + (t + 1)) % n := by
  rw [Nat.mod_add_mod, Nat.add_assoc]

/-- 每个槽都能从任何起点走到：(s + t) % n 取遍 0..n -/
theorem off (s e n : Nat) (hn : 0 < n) (he : e < n) : ∃ t, t < n ∧ (s + t) % n = e := by
  refine ⟨(e + n - s % n) % n, Nat.mod_lt _ hn, ?_⟩
  have hr : s % n < n := Nat.mod_lt _ hn
  rw [Nat.add_mod_mod, ← Nat.mod_add_mod, show s % n + (e + n - s % n) = e + n by omega,
    Nat.add_mod_right, Nat.mod_eq_of_lt he]

/-- 占用的槽数比 n 少时有空槽 -/
theorem empty_of_cnt (S : Nat → Option Nat) : ∀ n, cnt S n < n → ∃ e, e < n ∧ S e = none
  | 0, h => absurd h (Nat.lt_irrefl 0)
  | n + 1, h => by
    have h' : sumR (filled S) n + filled S n < n + 1 := h
    by_cases hs : S n = none
    · exact ⟨n, by omega, hs⟩
    · have h1 : filled S n = 1 := by simp [filled, hs]
      obtain ⟨e, he, hse⟩ := empty_of_cnt S n (by unfold cnt; omega)
      exact ⟨e, by omega, hse⟩

/-! ## map_slot：有这个键时 -/

theorem probe_hit (m : M K V) (k : K) (s d j : Nat) (hSd : m.S ((s + d) % m.n) = some j)
    (hk : m.keys[j]? = some k) : ∀ f t, t ≤ d → d < t + f →
    (∀ t', t ≤ t' → t' < d → ∃ j', m.S ((s + t') % m.n) = some j' ∧ m.keys[j']? ≠ some k) →
    probe m k f ((s + t) % m.n) = (s + d) % m.n
  | 0, t, h1, h2, _ => absurd h2 (by omega)
  | f + 1, t, h1, h2, H => by
    by_cases htd : t = d
    · subst htd
      unfold probe
      simp only [hSd]
      rw [ite_eq_left hk]
    · obtain ⟨j', hj', hne⟩ := H t (Nat.le_refl _) (by omega)
      unfold probe
      simp only [hj']
      rw [ite_eq_right hne, nextpos]
      exact probe_hit m k s d j hSd hk f (t + 1) (by omega) (by omega)
        (fun t' h3 h4 => H t' (by omega) h4)

/-- 有这个键时，map_slot 停在它所在的槽 -/
theorem slot_present (m : M K V) (W : WF hf m) (j : Nat) (hj : j < m.keys.length) :
    m.S (slot hf m m.keys[j]) = some j := by
  obtain ⟨d, hd, hSd, hpath⟩ := W.path j hj
  have hk : m.keys[j]? = some m.keys[j] := List.getElem?_eq_getElem hj
  have hp := probe_hit m m.keys[j] (hf m.keys[j]) d j hSd hk m.n 0 (Nat.zero_le _) (by omega) (by
    intro t' _ ht'
    have hne := hpath t' ht'
    obtain ⟨j', hj'⟩ := Option.ne_none_iff_exists'.1 hne
    refine ⟨j', hj', fun e => ?_⟩
    have hj'l := W.rng _ j' (Nat.mod_lt _ W.npos) hj'
    rw [List.getElem?_eq_getElem hj'l, Option.some.injEq] at e
    have hjj := nd_inj m.keys W.nodup j' j hj'l hj e
    subst hjj
    have := W.inj _ _ j' (Nat.mod_lt _ W.npos) (Nat.mod_lt _ W.npos) hj' hSd
    have := mod_inj (by omega : t' < m.n) hd this
    omega)
  unfold slot
  rw [show hf m.keys[j] % m.n = (hf m.keys[j] + 0) % m.n by rw [Nat.add_zero], hp, hSd]

/-! ## map_slot：没有这个键时 -/

theorem probe_miss (m : M K V) (k : K) (hk : ∀ j : Nat, m.keys[j]? ≠ some k) (s : Nat) : ∀ f t,
    (∃ t', t ≤ t' ∧ t' < t + f ∧ m.S ((s + t') % m.n) = none) →
    ∃ u, t ≤ u ∧ probe m k f ((s + t) % m.n) = (s + u) % m.n ∧ m.S ((s + u) % m.n) = none ∧
      (∀ t'', t ≤ t'' → t'' < u → m.S ((s + t'') % m.n) ≠ none) ∧
      (∀ t', t ≤ t' → m.S ((s + t') % m.n) = none → u ≤ t')
  | 0, t, ⟨t', h1, h2, _⟩ => absurd h2 (by omega)
  | f + 1, t, ⟨t', h1, h2, h3⟩ => by
    cases hS : m.S ((s + t) % m.n) with
    | none =>
      refine ⟨t, Nat.le_refl _, ?_, hS, fun t'' a b => absurd b (by omega), fun _ a _ => a⟩
      unfold probe
      simp only [hS]
    | some j =>
      have ht' : t ≠ t' := by intro e; subst e; rw [hS] at h3; exact absurd h3 (by simp)
      obtain ⟨u, hu1, hu2, hu3, hu4, hu5⟩ := probe_miss m k hk s f (t + 1) ⟨t', by omega, by omega, h3⟩
      refine ⟨u, by omega, ?_, hu3, fun t'' a b => ?_, fun t2 a b => ?_⟩
      · unfold probe
        simp only [hS]
        rw [ite_eq_right (hk j), nextpos, hu2]
      · by_cases e : t'' = t
        · rw [e, hS]
          simp
        · exact hu4 t'' (by omega) b
      · by_cases e : t2 = t
        · rw [e, hS] at b
          exact absurd b (by simp)
        · exact hu5 t2 (by omega) b

/-- 没有这个键时，map_slot 停在一个空槽，从起点到它的路上都没有空位 -/
theorem slot_absent (m : M K V) (W : WF hf m) (k : K) (hk : k ∉ m.keys) :
    ∃ u, u < m.n ∧ slot hf m k = (hf k + u) % m.n ∧ m.S ((hf k + u) % m.n) = none ∧
      ∀ t, t < u → m.S ((hf k + t) % m.n) ≠ none := by
  have hk' : ∀ j : Nat, m.keys[j]? ≠ some k := fun j e => hk (List.mem_of_getElem? e)
  obtain ⟨e, he, hSe⟩ := empty_of_cnt m.S m.n (by rw [W.count]; exact W.lt)
  obtain ⟨te, hte, hpos⟩ := off (hf k) e m.n W.npos he
  obtain ⟨u, _, hu2, hu3, hu4, hu5⟩ :=
    probe_miss m k hk' (hf k) m.n 0 ⟨te, Nat.zero_le _, by omega, by rw [hpos]; exact hSe⟩
  have hu : u ≤ te := hu5 te (Nat.zero_le _) (by rw [hpos]; exact hSe)
  refine ⟨u, by omega, ?_, hu3, fun t ht => hu4 t (Nat.zero_le _) ht⟩
  unfold slot
  rw [show hf k % m.n = (hf k + 0) % m.n by rw [Nat.add_zero], hu2]

/-! ## 放进新键、改已有键的值 -/

/-- m.slots[p] = x -/
def put (S : Nat → Option Nat) (p x : Nat) : Nat → Option Nat := fun i => if i = p then some x else S i

/-- 没有这个键时：m.slots[i] = len(m.keys); m.keys.push(k); m.vals.push(v) -/
def insNew (m : M K V) (k : K) (v : V) (p : Nat) : M K V :=
  ⟨m.keys ++ [k], m.vals ++ [v], put m.S p m.keys.length, m.n⟩

/-- 有这个键时：m.vals[j] = v -/
def setVal (m : M K V) (j : Nat) (v : V) : M K V := ⟨m.keys, m.vals.set j v, m.S, m.n⟩

omit [DecidableEq K] in
theorem nodup_snoc : ∀ (l : List K) (x : K), l.Nodup → x ∉ l → (l ++ [x]).Nodup
  | [], x, _, _ => by simp
  | a :: l, x, h, hx => by
    obtain ⟨ha, hl⟩ := List.nodup_cons.1 h
    rw [List.cons_append, List.nodup_cons]
    refine ⟨fun hm => ?_, nodup_snoc l x hl (fun m => hx (List.mem_cons_of_mem _ m))⟩
    rcases List.mem_append.1 hm with h1 | h1
    · exact ha h1
    · have h2 : a = x := by simpa using h1
      rw [← h2] at hx
      exact hx (List.mem_cons_self ..)

omit [DecidableEq K] in
theorem getElem_snoc : ∀ (l : List K) (x : K), (l ++ [x])[l.length]'(by simp) = x
  | [], _ => rfl
  | a :: l, x => by
    show (a :: (l ++ [x]))[l.length + 1]'(by simp) = x
    exact getElem_snoc l x

omit [DecidableEq K] in
/-- 放进新键：(hf k + u) % n 是 slot_absent 给的空槽；放完以后键数还是 < n -/
theorem insNew_wf (m : M K V) (W : WF hf m) (k : K) (v : V) (hk : k ∉ m.keys) (u : Nat)
    (hp : m.S ((hf k + u) % m.n) = none) (hpath : ∀ t, t < u → m.S ((hf k + t) % m.n) ≠ none)
    (hu : u < m.n) (hlt : m.keys.length + 1 < m.n) : WF hf (insNew m k v ((hf k + u) % m.n)) := by
  have hpn : (hf k + u) % m.n < m.n := Nat.mod_lt _ W.npos
  -- 本来不空的槽不变
  have hS : ∀ i, m.S i ≠ none → put m.S ((hf k + u) % m.n) m.keys.length i = m.S i := by
    intro i hi
    have : i ≠ (hf k + u) % m.n := fun e => hi (e ▸ hp)
    simp [put, this]
  refine ⟨W.npos, ?_, nodup_snoc _ _ W.nodup hk, ?_, ?_, ?_, ?_, ?_⟩
  · show (m.keys ++ [k]).length = (m.vals ++ [v]).length
    simp [W.len]
  · show (m.keys ++ [k]).length < m.n
    simp only [List.length_append, List.length_singleton]
    exact hlt
  · intro i j hi h1
    show j < (m.keys ++ [k]).length
    simp only [List.length_append, List.length_singleton]
    simp only [insNew, put] at h1
    split at h1
    · simp at h1
      omega
    · have := W.rng i j hi h1
      omega
  · intro i i' j hi hi' h1 h2
    simp only [insNew, put] at h1 h2
    split at h1 <;> split at h2
    · omega
    · simp at h1
      have := W.rng i' j hi' h2
      omega
    · simp at h2
      have := W.rng i j hi h1
      omega
    · exact W.inj i i' j hi hi' h1 h2
  · intro j hj
    by_cases hjl : j < m.keys.length
    · have e : (m.keys ++ [k])[j] = m.keys[j] := List.getElem_append_left hjl
      obtain ⟨d, hd, hSd, hpa⟩ := W.path j hjl
      refine ⟨d, hd, ?_, fun t ht => ?_⟩
      · show put m.S ((hf k + u) % m.n) m.keys.length ((hf (m.keys ++ [k])[j] + d) % m.n) = some j
        rw [e, hS _ (by rw [hSd]; simp), hSd]
      · show put m.S ((hf k + u) % m.n) m.keys.length ((hf (m.keys ++ [k])[j] + t) % m.n) ≠ none
        rw [e, hS _ (hpa t ht)]
        exact hpa t ht
    · have hj2 : j < (m.keys ++ [k]).length := hj
      rw [List.length_append, List.length_singleton] at hj2
      have hjL : j = m.keys.length := by omega
      subst hjL
      have e : (m.keys ++ [k])[m.keys.length] = k := getElem_snoc m.keys k
      refine ⟨u, hu, ?_, fun t ht => ?_⟩
      · show put m.S ((hf k + u) % m.n) m.keys.length ((hf (m.keys ++ [k])[m.keys.length] + u) % m.n) =
          some m.keys.length
        rw [e]
        simp [put]
      · show put m.S ((hf k + u) % m.n) m.keys.length ((hf (m.keys ++ [k])[m.keys.length] + t) % m.n) ≠ none
        rw [e, hS _ (hpath t ht)]
        exact hpath t ht
  · show sumR (filled (put m.S ((hf k + u) % m.n) m.keys.length)) m.n = (m.keys ++ [k]).length
    have hsum := Lark.Heap.sum_pt (filled (put m.S ((hf k + u) % m.n) m.keys.length)) (filled m.S)
      ((hf k + u) % m.n) m.n hpn (fun i hi => by simp [filled, put, hi])
    have f1 : filled (put m.S ((hf k + u) % m.n) m.keys.length) ((hf k + u) % m.n) = 1 := by simp [filled, put]
    have f2 : filled m.S ((hf k + u) % m.n) = 0 := by simp [filled, hp]
    have hc : sumR (filled m.S) m.n = m.keys.length := W.count
    simp only [List.length_append, List.length_singleton]
    omega

omit [DecidableEq K] in
/-- 改已有键的值：槽和键都不变 -/
theorem setVal_wf (m : M K V) (W : WF hf m) (j : Nat) (v : V) : WF hf (setVal m j v) :=
  ⟨W.npos, by simp [setVal, W.len], W.nodup, W.lt, W.rng, W.inj, W.path, W.count⟩

/-! ## get：和键值对列表一样 -/

/-- get：map_slot 停在空槽是 None，否则是那个下标的值 -/
def get (m : M K V) (k : K) : Option V :=
  match m.S (slot hf m k) with
  | none => none
  | some j => m.vals[j]?

/-- 键值对列表里按键找 -/
def alook : List K → List V → K → Option V
  | k' :: ks, v :: vs, k => if k' = k then some v else alook ks vs k
  | _, _, _ => none

theorem alook_idx : ∀ (ks : List K) (vs : List V) (j : Nat) (hj : j < ks.length), ks.Nodup →
    ks.length = vs.length → alook ks vs ks[j] = vs[j]?
  | [], _, _, hj, _, _ => absurd hj (by simp)
  | _ :: _, [], _, _, _, hl => by simp at hl
  | k' :: ks, v :: vs, 0, _, _, _ => by simp [alook]
  | k' :: ks, v :: vs, j + 1, hj, hnd, hl => by
    have hj' : j < ks.length := by simp at hj; omega
    have hne : k' ≠ ks[j] := fun e => (List.nodup_cons.1 hnd).1 (e ▸ List.getElem_mem hj')
    simp only [List.getElem_cons_succ, List.getElem?_cons_succ]
    unfold alook
    rw [ite_eq_right hne]
    exact alook_idx ks vs j hj' (List.nodup_cons.1 hnd).2 (by simpa using hl)

theorem alook_none : ∀ (ks : List K) (vs : List V) (k : K), k ∉ ks → alook ks vs k = none
  | [], _, _, _ => by simp [alook]
  | _ :: _, [], _, _ => by simp [alook]
  | k' :: ks, _ :: vs, k, hk => by
    have hne : k' ≠ k := fun e => hk (e ▸ List.mem_cons_self ..)
    unfold alook
    rw [ite_eq_right hne]
    exact alook_none ks vs k (fun h => hk (List.mem_cons_of_mem _ h))

/-- get 和在键值对列表里按键找一样 -/
theorem get_ok (m : M K V) (W : WF hf m) (k : K) : get hf m k = alook m.keys m.vals k := by
  by_cases hk : k ∈ m.keys
  · obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.1 hk
    unfold get
    rw [slot_present hf m W j hj]
    exact (alook_idx m.keys m.vals j hj W.nodup W.len).symm
  · obtain ⟨u, _, hs, hn, _⟩ := slot_absent hf m W k hk
    unfold get
    rw [hs, hn, alook_none m.keys m.vals k hk]

/-! ## 重建槽位表（map_rehash） -/

/-- 槽里存的下标都 < L（对所有 i，不只是 i < n） -/
def Refs (S : Nat → Option Nat) (L : Nat) : Prop := ∀ i j, S i = some j → j < L

/-- 空表：n 个槽都是 -1 -/
def M0 (n : Nat) : M K V := ⟨[], [], fun _ => none, n⟩

theorem cnt_none : ∀ n, cnt (fun _ => none) n = 0
  | 0 => rfl
  | n + 1 => by
    have ih := cnt_none n
    unfold cnt at ih ⊢
    show sumR (filled fun _ => none) n + filled (fun _ => none) n = 0
    simp [filled, ih]

omit [DecidableEq K] in
theorem M0_wf (n : Nat) (hn : 0 < n) : WF hf (M0 n : M K V) :=
  ⟨hn, rfl, List.nodup_nil, hn, fun _ _ _ h => by simp [M0] at h, fun _ _ _ _ _ h => by simp [M0] at h,
    fun j hj => absurd hj (by simp [M0]), cnt_none n⟩

omit [DecidableEq K] in
theorem nd_mid : ∀ (l : List K) (x : K) (r : List K), (l ++ x :: r).Nodup → x ∉ l
  | [], _, _, _ => by simp
  | a :: l, x, r, h => by
    obtain ⟨ha, hl⟩ := List.nodup_cons.1 h
    intro hm
    rcases List.mem_cons.1 hm with rfl | hm
    · exact ha (List.mem_append_right _ (List.mem_cons_self ..))
    · exact nd_mid l x r hl hm

omit [DecidableEq K] in
theorem refs_put (m : M K V) (R : Refs m.S m.keys.length) (k : K) (v : V) (p : Nat) :
    Refs (insNew m k v p).S (insNew m k v p).keys.length := by
  intro i j h
  show j < (m.keys ++ [k]).length
  simp only [insNew, put] at h
  simp only [List.length_append, List.length_singleton]
  split at h
  · simp at h
    omega
  · have := R i j h
    omega

/-- 一个个放进去：每个键放进 map_slot 找到的空槽 -/
def build : List K → List V → M K V → M K V
  | k :: ks, v :: vs, m => build ks vs (insNew m k v (slot hf m k))
  | _, _, m => m

theorem build_wf : ∀ (ks : List K) (vs : List V) (m : M K V), WF hf m → Refs m.S m.keys.length →
    ks.length = vs.length → (m.keys ++ ks).Nodup → (m.keys ++ ks).length < m.n →
    WF hf (build hf ks vs m) ∧ (build hf ks vs m).keys = m.keys ++ ks ∧ (build hf ks vs m).vals = m.vals ++ vs ∧
      (build hf ks vs m).n = m.n ∧ Refs (build hf ks vs m).S (m.keys ++ ks).length
  | [], vs, m, W, R, hl, _, _ => by
    cases vs with
    | nil =>
      have hb : build hf [] [] m = m := by first | rfl | simp [build] | (unfold build; rfl)
      rw [hb]
      exact ⟨W, by simp, by simp, rfl, by simpa using R⟩
    | cons _ _ => simp at hl
  | _ :: _, [], _, _, _, hl, _, _ => by simp at hl
  | k :: ks, v :: vs, m, W, R, hl, hnd, hlt => by
    have hk : k ∉ m.keys := nd_mid _ _ _ hnd
    obtain ⟨u, hu, hs, hp, hpath⟩ := slot_absent hf m W k hk
    have hlt1 : m.keys.length + 1 < m.n := by simp at hlt; omega
    have W1 := insNew_wf hf m W k v hk u hp hpath hu hlt1
    rw [← hs] at W1
    have e1 : (insNew m k v (slot hf m k)).keys ++ ks = m.keys ++ k :: ks := by simp [insNew]
    obtain ⟨A, B, C, D, E⟩ := build_wf ks vs (insNew m k v (slot hf m k)) W1 (refs_put m R k v _)
      (by simpa using hl) (by rw [e1]; exact hnd) (by rw [e1]; exact hlt)
    refine ⟨A, B.trans e1, C.trans (by simp [insNew]), D, ?_⟩
    rw [← e1]
    exact E

/-- probe 只看槽里存的下标对应的键：两张表这些键一样时，探测结果一样 -/
theorem probe_congr {V1 V2 : Type} (m1 : M K V1) (m2 : M K V2) (k : K) (hS : m1.S = m2.S) (hn : m1.n = m2.n)
    (hk : ∀ i j, m1.S i = some j → m1.keys[j]? = m2.keys[j]?) : ∀ f i, probe m1 k f i = probe m2 k f i
  | 0, _ => rfl
  | f + 1, i => by
    unfold probe
    rw [← hS, ← hn]
    cases h : m1.S i with
    | none => rfl
    | some j =>
      dsimp only
      rw [hk i j h, probe_congr m1 m2 k hS hn hk f]

/-- map_rehash 的循环：slots[map_slot(m, keys[j])] = j。map_slot 用的是整个 keys，但槽里只有前 j 个的下标 -/
def rhL (keys : List K) (n : Nat) : List K → Nat → (Nat → Option Nat) → (Nat → Option Nat)
  | [], _, S => S
  | k :: ks, j, S => rhL keys n ks (j + 1) (put S (probe (⟨keys, [], S, n⟩ : M K Unit) k n (hf k % n)) j)

/-- Lark 的写法和一个个放进去一样 -/
theorem rh_eq (keys : List K) : ∀ (ks : List K) (vs : List V) (m : M K V), Refs m.S m.keys.length →
    keys = m.keys ++ ks → ks.length = vs.length →
    rhL hf keys m.n ks m.keys.length m.S = (build hf ks vs m).S
  | [], vs, m, _, _, hl => by
    cases vs with
    | nil => rfl
    | cons _ _ => simp at hl
  | _ :: _, [], _, _, _, hl => by simp at hl
  | k :: ks, v :: vs, m, R, hkeys, hl => by
    have hprobe : probe (⟨keys, [], m.S, m.n⟩ : M K Unit) k m.n (hf k % m.n) = slot hf m k :=
      probe_congr (⟨keys, [], m.S, m.n⟩ : M K Unit) m k rfl rfl (fun i j h => by
        show keys[j]? = m.keys[j]?
        rw [hkeys]
        exact List.getElem?_append_left (R i j h)) m.n _
    have hL : (insNew m k v (slot hf m k)).keys.length = m.keys.length + 1 := by simp [insNew]
    show rhL hf keys m.n ks (m.keys.length + 1) (put m.S (probe (⟨keys, [], m.S, m.n⟩ : M K Unit) k m.n
      (hf k % m.n)) m.keys.length) = (build hf ks vs (insNew m k v (slot hf m k))).S
    rw [hprobe, ← hL]
    exact rh_eq keys ks vs (insNew m k v (slot hf m k)) (refs_put m R k v _) (by rw [hkeys]; simp [insNew])
      (by simpa using hl)

/-- map_rehash(m, n)：按 keys 重新建槽位表 -/
def rehash (m : M K V) (n : Nat) : M K V := ⟨m.keys, m.vals, rhL hf m.keys n m.keys 0 (fun _ => none), n⟩

/-- 重建以后不变式成立（键两两不同、keys 和 vals 一样长、键数 < 新的槽数） -/
theorem rehash_wf (m : M K V) (hnd : m.keys.Nodup) (hl : m.keys.length = m.vals.length) (n : Nat)
    (hn : m.keys.length < n) : WF hf (rehash hf m n) := by
  have W0 := M0_wf (V := V) hf n (by omega)
  have R0 : Refs (M0 n : M K V).S (M0 n : M K V).keys.length := fun _ _ h => by simp [M0] at h
  obtain ⟨A, B, C, D, _⟩ := build_wf hf m.keys m.vals (M0 n) W0 R0 hl (by simpa [M0] using hnd)
    (by simpa [M0] using hn)
  have hS := rh_eq hf m.keys m.keys m.vals (M0 n) R0 (by simp [M0]) hl
  have e : rehash hf m n = ⟨(build hf m.keys m.vals (M0 n)).keys, (build hf m.keys m.vals (M0 n)).vals,
      (build hf m.keys m.vals (M0 n)).S, (build hf m.keys m.vals (M0 n)).n⟩ := by
    rw [B, C, D, ← hS]
    simp [rehash, M0]
  rw [e]
  exact A

/-! ## insert：和键值对列表一样 -/

/-- 末尾加一对（键原来没有时） -/
theorem alook_snoc (k : K) (v : V) (k' : K) : ∀ (ks : List K) (vs : List V), ks.length = vs.length → k ∉ ks →
    alook (ks ++ [k]) (vs ++ [v]) k' = if k' = k then some v else alook ks vs k'
  | [], [], _, _ => by
    by_cases h : k' = k
    · subst h
      simp [alook]
    · simp [alook, h, Ne.symm h]
  | [], _ :: _, hl, _ => by simp at hl
  | _ :: _, [], hl, _ => by simp at hl
  | a :: ks, b :: vs, hl, hk => by
    have ha : a ≠ k := fun e => hk (e ▸ List.mem_cons_self ..)
    have ih := alook_snoc k v k' ks vs (by simpa using hl) (fun h => hk (List.mem_cons_of_mem _ h))
    show (if a = k' then some b else alook (ks ++ [k]) (vs ++ [v]) k') =
      if k' = k then some v else (if a = k' then some b else alook ks vs k')
    rw [ih]
    by_cases h1 : k' = k
    · subst h1
      simp [ha]
    · by_cases h2 : a = k'
      · simp [h1, h2]
      · simp [h1, h2]

/-- 改第 j 个键的值 -/
theorem alook_set (v : V) (k' : K) : ∀ (ks : List K) (vs : List V) (j : Nat) (hj : j < ks.length), ks.Nodup →
    ks.length = vs.length → alook ks (vs.set j v) k' = if k' = ks[j] then some v else alook ks vs k'
  | [], _, _, hj, _, _ => absurd hj (by simp)
  | _ :: _, [], _, _, _, hl => by simp at hl
  | a :: ks, b :: vs, 0, _, _, _ => by
    show (if a = k' then some v else alook ks vs k') = if k' = a then some v else (if a = k' then some b else alook ks vs k')
    by_cases h : a = k'
    · subst h
      simp
    · simp [h, Ne.symm h]
  | a :: ks, b :: vs, j + 1, hj, hnd, hl => by
    have hj' : j < ks.length := by simp at hj; omega
    have hne : a ≠ ks[j] := fun e => (List.nodup_cons.1 hnd).1 (e ▸ List.getElem_mem hj')
    have ih := alook_set v k' ks vs j hj' (List.nodup_cons.1 hnd).2 (by simpa using hl)
    show (if a = k' then some b else alook ks (vs.set j v) k') =
      if k' = ks[j] then some v else (if a = k' then some b else alook ks vs k')
    rw [ih]
    by_cases h1 : a = k'
    · subst h1
      simp [hne]
    · simp [h1]

/-- insert 开头：(len(keys) + 1) * 2 > len(slots) 时翻倍并重建 -/
def grow (m : M K V) : M K V := if m.n < (m.keys.length + 1) * 2 then rehash hf m (m.n * 2) else m

/-- insert：有这个键时改值，没有时放进 map_slot 找到的空槽 -/
def insert (m : M K V) (k : K) (v : V) : M K V :=
  match (grow hf m).S (slot hf (grow hf m) k) with
  | some j => setVal (grow hf m) j v
  | none => insNew (grow hf m) k v (slot hf (grow hf m) k)

theorem grow_ok (m : M K V) (W : WF hf m) :
    WF hf (grow hf m) ∧ (grow hf m).keys = m.keys ∧ (grow hf m).vals = m.vals ∧
      (m.keys.length + 1) * 2 ≤ (grow hf m).n := by
  have hlt := W.lt
  unfold grow
  by_cases hc : m.n < (m.keys.length + 1) * 2
  · rw [ite_eq_left hc]
    exact ⟨rehash_wf hf m W.nodup W.len _ (by omega), rfl, rfl, by show _ ≤ m.n * 2; omega⟩
  · rw [ite_eq_right hc]
    exact ⟨W, rfl, rfl, by omega⟩

/-- insert 后：不变式成立，装填不超过一半；键的顺序是原来的（新键在最后）；按键找到的是新的值，别的键不变 -/
theorem insert_ok (m : M K V) (W : WF hf m) (k : K) (v : V) :
    WF hf (insert hf m k v) ∧ 2 * (insert hf m k v).keys.length ≤ (insert hf m k v).n ∧
    (insert hf m k v).keys = (if k ∈ m.keys then m.keys else m.keys ++ [k]) ∧
    ∀ k', alook (insert hf m k v).keys (insert hf m k v).vals k' = if k' = k then some v else alook m.keys m.vals k' := by
  obtain ⟨W1, hk1, hv1, hn1⟩ := grow_ok hf m W
  by_cases hk : k ∈ m.keys
  · have hkg : k ∈ (grow hf m).keys := by rw [hk1]; exact hk
    obtain ⟨j, hj, hjk⟩ := List.mem_iff_getElem.1 hkg
    have hs := slot_present hf (grow hf m) W1 j hj
    rw [hjk] at hs
    have e : insert hf m k v = setVal (grow hf m) j v := by
      unfold insert
      rw [hs]
    rw [e, ite_eq_left hk]
    refine ⟨setVal_wf hf _ W1 j v, ?_, ?_, fun k' => ?_⟩
    · show 2 * (grow hf m).keys.length ≤ (grow hf m).n
      rw [hk1]
      omega
    · exact hk1
    · show alook (grow hf m).keys ((grow hf m).vals.set j v) k' = _
      rw [alook_set v k' _ _ j hj W1.nodup W1.len, hjk, hk1, hv1]
  · have hkg : k ∉ (grow hf m).keys := by rw [hk1]; exact hk
    obtain ⟨u, hu, hs, hp, hpath⟩ := slot_absent hf (grow hf m) W1 k hkg
    have e : insert hf m k v = insNew (grow hf m) k v ((hf k + u) % (grow hf m).n) := by
      unfold insert
      rw [hs, hp]
    have hlt : (grow hf m).keys.length + 1 < (grow hf m).n := by rw [hk1]; omega
    rw [e, ite_eq_right hk]
    refine ⟨insNew_wf hf _ W1 k v hkg u hp hpath hu hlt, ?_, ?_, fun k' => ?_⟩
    · show 2 * ((grow hf m).keys ++ [k]).length ≤ (grow hf m).n
      rw [hk1]
      simp only [List.length_append, List.length_singleton]
      omega
    · show (grow hf m).keys ++ [k] = m.keys ++ [k]
      rw [hk1]
    · show alook ((grow hf m).keys ++ [k]) ((grow hf m).vals ++ [v]) k' = _
      rw [hk1, hv1, alook_snoc k v k' m.keys m.vals W.len hk]

/-! ## remove：去掉第 j 个，其余保持插入顺序，然后重建槽位表 -/

omit [DecidableEq K] in
theorem mem_erase : ∀ (l : List K) (j : Nat) (x : K), x ∈ l.eraseIdx j → x ∈ l
  | [], _, _, h => by simp at h
  | _ :: _, 0, _, h => List.mem_cons_of_mem _ h
  | a :: l, j + 1, x, h => by
    have h' : x ∈ a :: l.eraseIdx j := h
    rcases List.mem_cons.1 h' with rfl | h'
    · exact List.mem_cons_self ..
    · exact List.mem_cons_of_mem _ (mem_erase l j x h')

omit [DecidableEq K] in
theorem nd_erase : ∀ (l : List K) (j : Nat), l.Nodup → (l.eraseIdx j).Nodup
  | [], _, _ => List.nodup_nil
  | _ :: _, 0, h => (List.nodup_cons.1 h).2
  | a :: l, j + 1, h => by
    obtain ⟨ha, hl⟩ := List.nodup_cons.1 h
    show (a :: l.eraseIdx j).Nodup
    exact List.nodup_cons.2 ⟨fun hm => ha (mem_erase l j a hm), nd_erase l j hl⟩

theorem len_erase {α : Type} : ∀ (l : List α) (j : Nat), j < l.length → (l.eraseIdx j).length + 1 = l.length
  | [], _, h => absurd h (by simp)
  | _ :: l, 0, _ => by
    show l.length + 1 = _
    rfl
  | a :: l, j + 1, h => by
    have := len_erase l j (by simp at h; omega)
    show (a :: l.eraseIdx j).length + 1 = (a :: l).length
    simp only [List.length_cons]
    omega

theorem alook_erase (k' : K) : ∀ (ks : List K) (vs : List V) (j : Nat) (hj : j < ks.length), ks.Nodup →
    ks.length = vs.length → alook (ks.eraseIdx j) (vs.eraseIdx j) k' = if k' = ks[j] then none else alook ks vs k'
  | [], _, _, hj, _, _ => absurd hj (by simp)
  | _ :: _, [], _, _, _, hl => by simp at hl
  | a :: ks, b :: vs, 0, _, hnd, _ => by
    show alook ks vs k' = if k' = a then none else (if a = k' then some b else alook ks vs k')
    by_cases h : k' = a
    · subst h
      rw [alook_none ks vs k' (List.nodup_cons.1 hnd).1]
      simp
    · simp [h, Ne.symm h]
  | a :: ks, b :: vs, j + 1, hj, hnd, hl => by
    have hj' : j < ks.length := by simp at hj; omega
    have hne : a ≠ ks[j] := fun e => (List.nodup_cons.1 hnd).1 (e ▸ List.getElem_mem hj')
    have ih := alook_erase k' ks vs j hj' (List.nodup_cons.1 hnd).2 (by simpa using hl)
    show (if a = k' then some b else alook (ks.eraseIdx j) (vs.eraseIdx j) k') =
      if k' = ks[j] then none else (if a = k' then some b else alook ks vs k')
    rw [ih]
    by_cases h1 : a = k'
    · subst h1
      simp [hne]
    · simp [h1]

/-- remove：map_slot 停在空槽时是 None、不改；否则取出值，去掉第 j 个（Lark 里先把后面的挪开再放回），重建槽位表 -/
def remove (m : M K V) (k : K) : Option V × M K V :=
  match m.S (slot hf m k) with
  | none => (none, m)
  | some j => (m.vals[j]?, rehash hf ⟨m.keys.eraseIdx j, m.vals.eraseIdx j, m.S, m.n⟩ m.n)

/-- remove 后：没有这个键时不变；有时取出的是它的值，去掉的正好是它，别的键不变、顺序不变 -/
theorem remove_ok (m : M K V) (W : WF hf m) (k : K) :
    (k ∉ m.keys → remove hf m k = (none, m)) ∧
    (k ∈ m.keys → (remove hf m k).1 = alook m.keys m.vals k ∧ WF hf (remove hf m k).2 ∧
      (∃ j, ∃ hj : j < m.keys.length, m.keys[j] = k ∧ (remove hf m k).2.keys = m.keys.eraseIdx j) ∧
      ∀ k', alook (remove hf m k).2.keys (remove hf m k).2.vals k' = if k' = k then none else alook m.keys m.vals k') := by
  refine ⟨fun hk => ?_, fun hk => ?_⟩
  · obtain ⟨u, _, hs, hp, _⟩ := slot_absent hf m W k hk
    unfold remove
    rw [hs, hp]
  · obtain ⟨j, hj, hjk⟩ := List.mem_iff_getElem.1 hk
    have hs := slot_present hf m W j hj
    rw [hjk] at hs
    have e : remove hf m k = (m.vals[j]?, rehash hf ⟨m.keys.eraseIdx j, m.vals.eraseIdx j, m.S, m.n⟩ m.n) := by
      unfold remove
      rw [hs]
    rw [e]
    have hl1 := len_erase m.keys j hj
    have hl2 := len_erase m.vals j (by rw [← W.len]; exact hj)
    have hlen := W.len
    have hlt := W.lt
    refine ⟨?_, rehash_wf hf (⟨m.keys.eraseIdx j, m.vals.eraseIdx j, m.S, m.n⟩ : M K V) (nd_erase _ j W.nodup)
      (by show (m.keys.eraseIdx j).length = (m.vals.eraseIdx j).length; omega) _
      (by show (m.keys.eraseIdx j).length < m.n; omega), ⟨j, hj, hjk, rfl⟩, fun k' => ?_⟩
    · show m.vals[j]? = _
      rw [← hjk]
      exact (alook_idx m.keys m.vals j hj W.nodup W.len).symm
    · show alook (m.keys.eraseIdx j) (m.vals.eraseIdx j) k' = _
      rw [alook_erase k' m.keys m.vals j hj W.nodup W.len, hjk]

/-! ## retain：只留下 keep(键, 值) 为真的，然后重建槽位表 -/

/-- 按顺序留下 keep 为真的键值对 -/
def filt (keep : K → V → Bool) : List K → List V → List K × List V
  | k :: ks, v :: vs => if keep k v then (k :: (filt keep ks vs).1, v :: (filt keep ks vs).2) else filt keep ks vs
  | _, _ => ([], [])

omit [DecidableEq K] in
theorem filt_len (keep : K → V → Bool) : ∀ (ks : List K) (vs : List V), ks.length = vs.length →
    (filt keep ks vs).1.length = (filt keep ks vs).2.length ∧ (filt keep ks vs).1.length ≤ ks.length
  | [], [], _ => ⟨rfl, Nat.le_refl _⟩
  | [], _ :: _, hl => by simp at hl
  | _ :: _, [], hl => by simp at hl
  | k :: ks, v :: vs, hl => by
    have ih := filt_len keep ks vs (by simpa using hl)
    by_cases h : keep k v = true
    · simp only [filt, h, ↓reduceIte, List.length_cons]
      omega
    · simp only [filt, h, Bool.false_eq_true, ↓reduceIte, List.length_cons]
      omega

omit [DecidableEq K] in
theorem filt_mem (keep : K → V → Bool) : ∀ (ks : List K) (vs : List V) (x : K), x ∈ (filt keep ks vs).1 → x ∈ ks
  | [], _, _, h => by simp [filt] at h
  | _ :: _, [], _, h => by simp [filt] at h
  | k :: ks, v :: vs, x, h => by
    by_cases hk : keep k v = true
    · simp only [filt, hk, ↓reduceIte, List.mem_cons] at h
      rcases h with rfl | h
      · exact List.mem_cons_self ..
      · exact List.mem_cons_of_mem _ (filt_mem keep ks vs x h)
    · simp only [filt, hk, Bool.false_eq_true, ↓reduceIte] at h
      exact List.mem_cons_of_mem _ (filt_mem keep ks vs x h)

omit [DecidableEq K] in
theorem filt_nodup (keep : K → V → Bool) : ∀ (ks : List K) (vs : List V), ks.Nodup → (filt keep ks vs).1.Nodup
  | [], _, _ => by simp [filt]
  | _ :: _, [], _ => by simp [filt]
  | k :: ks, v :: vs, h => by
    obtain ⟨hk, hl⟩ := List.nodup_cons.1 h
    by_cases hkv : keep k v = true
    · simp only [filt, hkv, ↓reduceIte]
      exact List.nodup_cons.2 ⟨fun hm => hk (filt_mem keep ks vs k hm), filt_nodup keep ks vs hl⟩
    · simp only [filt, hkv, Bool.false_eq_true, ↓reduceIte]
      exact filt_nodup keep ks vs hl

/-- 留下的里面按键找：原来有、并且 keep 为真时才找得到 -/
theorem filt_alook (keep : K → V → Bool) (k' : K) : ∀ (ks : List K) (vs : List V), ks.Nodup →
    alook (filt keep ks vs).1 (filt keep ks vs).2 k' =
      (alook ks vs k').bind (fun v => if keep k' v then some v else none)
  | [], _, _ => by simp [filt, alook]
  | _ :: _, [], _ => by simp [filt, alook]
  | a :: ks, b :: vs, hnd => by
    have ha := (List.nodup_cons.1 hnd).1
    have ih := filt_alook keep k' ks vs (List.nodup_cons.1 hnd).2
    by_cases hkv : keep a b = true
    · simp only [filt, hkv, ↓reduceIte]
      show (if a = k' then some b else alook (filt keep ks vs).1 (filt keep ks vs).2 k') =
        (if a = k' then some b else alook ks vs k').bind _
      rw [ih]
      by_cases h1 : a = k'
      · subst h1
        simp [hkv]
      · simp [h1]
    · simp only [filt, hkv, Bool.false_eq_true, ↓reduceIte]
      show alook (filt keep ks vs).1 (filt keep ks vs).2 k' = (if a = k' then some b else alook ks vs k').bind _
      rw [ih]
      by_cases h1 : a = k'
      · subst h1
        rw [alook_none ks vs a ha]
        simp [hkv]
      · simp [h1]

omit [DecidableEq K] in
/-- 一个都没去掉时，留下的就是原来的 -/
theorem filt_same (keep : K → V → Bool) : ∀ (ks : List K) (vs : List V), ks.length = vs.length →
    (filt keep ks vs).1.length = ks.length → filt keep ks vs = (ks, vs)
  | [], [], _, _ => rfl
  | [], _ :: _, hl, _ => by simp at hl
  | _ :: _, [], hl, _ => by simp at hl
  | k :: ks, v :: vs, hl, h => by
    have hb := (filt_len keep ks vs (by simpa using hl)).2
    by_cases hkv : keep k v = true
    · simp only [filt, hkv, ↓reduceIte, List.length_cons] at h ⊢
      rw [filt_same keep ks vs (by simpa using hl) (by omega)]
    · simp only [filt, hkv, Bool.false_eq_true, ↓reduceIte, List.length_cons] at h
      omega

/-- retain：删掉了才重建（removed > 0） -/
def retain (m : M K V) (keep : K → V → Bool) : M K V :=
  if (filt keep m.keys m.vals).1.length = m.keys.length then m
  else rehash hf ⟨(filt keep m.keys m.vals).1, (filt keep m.keys m.vals).2, m.S, m.n⟩ m.n

/-- retain 后：不变式成立；按键找，原来有并且 keep 为真时还在，否则没有 -/
theorem retain_ok (m : M K V) (W : WF hf m) (keep : K → V → Bool) :
    WF hf (retain hf m keep) ∧ ∀ k', alook (retain hf m keep).keys (retain hf m keep).vals k' =
      (alook m.keys m.vals k').bind (fun v => if keep k' v then some v else none) := by
  have hfa := filt_alook keep
  obtain ⟨hl, hle⟩ := filt_len keep m.keys m.vals W.len
  have hlt := W.lt
  unfold retain
  by_cases hc : (filt keep m.keys m.vals).1.length = m.keys.length
  · rw [ite_eq_left hc]
    refine ⟨W, fun k' => ?_⟩
    have := hfa k' m.keys m.vals W.nodup
    rw [filt_same keep m.keys m.vals W.len hc] at this
    exact this
  · rw [ite_eq_right hc]
    exact ⟨rehash_wf hf (⟨(filt keep m.keys m.vals).1, (filt keep m.keys m.vals).2, m.S, m.n⟩ : M K V)
      (filt_nodup keep m.keys m.vals W.nodup) hl _ (by show (filt keep m.keys m.vals).1.length < m.n; omega),
      fun k' => hfa k' m.keys m.vals W.nodup⟩

end HMap
end Lark
