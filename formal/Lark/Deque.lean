/-
标准库的证明 · 双端队列（std/deque.lark）

照着 std/deque.lark 写一份。环形缓冲区 buf 写成 Nat → Option α（下标都先 % cap，读不到 cap 外面），
d.buf[i] = v 写成 upd。Lark 里 head、n 是 int，但从不为负，写成 Nat；push_front 的 (head - 1 + cap) % cap
在 cap > 0 时就是 (head + cap - 1) % cap。grow 用 replace 把旧元素一个个取出来，取的位置两两不同，
所以等于直接读旧的 buf。get 的 i < 0 直接是 None，这里只看 i ≥ 0。

抽象：view d 是从队头到队尾的元素，第 k 个是 buf[(head + k) % cap]。
不变式 WF：n ≤ cap，head < cap（cap = 0 时 head = 0），view 里都是 Some（iter_at 不会碰到空位）。
证明：new、push_back、push_front、pop_front、pop_back 在 view 上就是列表的对应操作，并且保持 WF；
get i 是 view 的第 i 个；of xs 的 view 是 xs。
-/

namespace Lark
namespace Deque

structure D (α : Type) where
  buf : Nat → Option α
  cap : Nat
  head : Nat
  n : Nat

variable {α : Type}

/-- d.buf[i] = v -/
def upd (f : Nat → Option α) (i : Nat) (v : Option α) : Nat → Option α := fun j => if j = i then v else f j

/-- 从队头到队尾 -/
def view (d : D α) : List (Option α) := (List.range d.n).map (fun k => d.buf ((d.head + k) % d.cap))

abbrev WF (d : D α) : Prop :=
  d.n ≤ d.cap ∧ (d.head < d.cap ∨ (d.cap = 0 ∧ d.head = 0)) ∧ ∀ o ∈ view d, o.isSome = true

/-! ## 写：deque.lark 的各个函数 -/

/-- new、clear -/
def empty : D α := ⟨fun _ => none, 0, 0, 0⟩

def gcap (c : Nat) : Nat := if c = 0 then 8 else c * 2

/-- grow：容量翻倍，元素按顺序搬到开头 -/
def grow (d : D α) : D α :=
  ⟨fun j => if j < d.n then d.buf ((d.head + j) % d.cap) else none, gcap d.cap, 0, d.n⟩

/-- push 开头的 if d.n == len(d.buf) { grow(&d) } -/
def prep (d : D α) : D α := if d.n = d.cap then grow d else d

def pb0 (d : D α) (x : α) : D α := ⟨upd d.buf ((d.head + d.n) % d.cap) (some x), d.cap, d.head, d.n + 1⟩
def pushBack (d : D α) (x : α) : D α := pb0 (prep d) x

def fh (d : D α) : Nat := (d.head + d.cap - 1) % d.cap
def pf0 (d : D α) (x : α) : D α := ⟨upd d.buf (fh d) (some x), d.cap, fh d, d.n + 1⟩
def pushFront (d : D α) (x : α) : D α := pf0 (prep d) x

def popF0 (d : D α) : D α := ⟨upd d.buf d.head none, d.cap, (d.head + 1) % d.cap, d.n - 1⟩
def popFront (d : D α) : Option α × D α := if d.n = 0 then (none, d) else (d.buf d.head, popF0 d)

def bi (d : D α) : Nat := (d.head + d.n - 1) % d.cap
def popB0 (d : D α) : D α := ⟨upd d.buf (bi d) none, d.cap, d.head, d.n - 1⟩
def popBack (d : D α) : Option α × D α := if d.n = 0 then (none, d) else (d.buf (bi d), popB0 d)

def get (d : D α) (i : Nat) : Option α := if i < d.n then d.buf ((d.head + i) % d.cap) else none

/-! ## 例子 -/

-- 先放 1 2，再从前面放 0，队头取出 0，队尾取出 2，剩下 1
#guard view (pushFront (pushBack (pushBack (empty : D Nat) 1) 2) 0) == [some 0, some 1, some 2]
#guard (popFront (pushFront (pushBack (pushBack (empty : D Nat) 1) 2) 0)).1 == some 0
#guard (popBack (pushFront (pushBack (pushBack (empty : D Nat) 1) 2) 0)).1 == some 2
-- 放 9 个，第 9 个时容量从 8 翻到 16
#guard view ((List.range 9).foldl pushBack (empty : D Nat)) == (List.range 9).map some
#guard ((List.range 9).foldl pushBack (empty : D Nat)).cap == 16

/-! ## 环上的下标 -/

/-- 在 cap 个位置里，(head + i) % cap 两两不同 -/
theorem mod_inj {h c i j : Nat} (hi : i < c) (hj : j < c) (e : (h + i) % c = (h + j) % c) : i = j := by
  rcases Nat.le_total i j with hij | hij
  · have h1 := Nat.sub_mod_eq_zero_of_mod_eq e.symm
    have h2 : h + j - (h + i) = j - i := by omega
    have h3 : j - i < c := by omega
    rw [h2, Nat.mod_eq_of_lt h3] at h1
    omega
  · have h1 := Nat.sub_mod_eq_zero_of_mod_eq e
    have h2 : h + i - (h + j) = i - j := by omega
    have h3 : i - j < c := by omega
    rw [h2, Nat.mod_eq_of_lt h3] at h1
    omega

theorem map_eq {β : Type} {f g : Nat → β} : ∀ l : List Nat, (∀ a ∈ l, f a = g a) → l.map f = l.map g
  | [], _ => rfl
  | a :: l, h => by
    simp only [List.map_cons]
    rw [h a (List.mem_cons_self ..), map_eq l (fun b hb => h b (List.mem_cons_of_mem _ hb))]

theorem view_ext (e d : D α) (hn : e.n = d.n)
    (h : ∀ k, k < d.n → e.buf ((e.head + k) % e.cap) = d.buf ((d.head + k) % d.cap)) : view e = view d := by
  unfold view
  rw [hn]
  exact map_eq _ (fun k hk => h k (List.mem_range.1 hk))

theorem view_snoc (e : D α) (m : Nat) (hm : e.n = m + 1) :
    view e = view { e with n := m } ++ [e.buf ((e.head + m) % e.cap)] := by
  unfold view
  (rw [hm, List.range_succ, List.map_append]) <;> rfl

theorem view_cons (e : D α) (m : Nat) (hm : e.n = m + 1) :
    view e = e.buf ((e.head + 0) % e.cap) :: (List.range m).map (fun k => e.buf ((e.head + (k + 1)) % e.cap)) := by
  unfold view
  (rw [hm, List.range_succ_eq_map, List.map_cons, List.map_map]) <;> rfl

theorem view_len (d : D α) : (view d).length = d.n := by simp [view]

/-! ## grow -/

theorem grow_view (d : D α) (hw : WF d) : view (grow d) = view d := by
  have hle := hw.1
  refine view_ext _ _ rfl ?_
  intro k hk
  have hl : k < gcap d.cap := by unfold gcap; split <;> omega
  have e : (0 + k) % gcap d.cap = k := by rw [Nat.zero_add]; exact Nat.mod_eq_of_lt hl
  show (if (0 + k) % gcap d.cap < d.n then d.buf ((d.head + (0 + k) % gcap d.cap) % d.cap) else none) = _
  rw [e, ite_eq_left hk]

/-- push 之前：有空位，view 不变 -/
theorem prep_ok (d : D α) (hw : WF d) : WF (prep d) ∧ (prep d).n < (prep d).cap ∧ view (prep d) = view d := by
  obtain ⟨h1, h2, h3⟩ := hw
  unfold prep
  by_cases hc : d.n = d.cap
  · rw [ite_eq_left hc]
    have hv := grow_view d ⟨h1, h2, h3⟩
    refine ⟨⟨?_, ?_, ?_⟩, ?_, hv⟩
    · show d.n ≤ gcap d.cap
      unfold gcap; split <;> omega
    · left
      show 0 < gcap d.cap
      unfold gcap; split <;> omega
    · rw [hv]; exact h3
    · show d.n < gcap d.cap
      unfold gcap; split <;> omega
  · rw [ite_eq_right hc]
    exact ⟨⟨h1, h2, h3⟩, by omega, rfl⟩

/-! ## push_back -/

theorem pb0_view (d : D α) (x : α) (hlt : d.n < d.cap) : view (pb0 d x) = view d ++ [some x] := by
  rw [view_snoc (pb0 d x) d.n rfl]
  congr 1
  · refine view_ext _ _ rfl ?_
    intro k hk
    have hk' : k < d.cap := by omega
    have hne : (d.head + k) % d.cap ≠ (d.head + d.n) % d.cap := fun e => absurd (mod_inj hk' hlt e) (by omega)
    show (if (d.head + k) % d.cap = (d.head + d.n) % d.cap then some x else d.buf ((d.head + k) % d.cap)) = _
    rw [ite_eq_right hne]
  · show [upd d.buf ((d.head + d.n) % d.cap) (some x) ((d.head + d.n) % d.cap)] = [some x]
    simp [upd]

theorem pb0_wf (d : D α) (x : α) (hw : WF d) (hlt : d.n < d.cap) : WF (pb0 d x) := by
  obtain ⟨_, h2, h3⟩ := hw
  refine ⟨?_, h2, ?_⟩
  · show d.n + 1 ≤ d.cap
    omega
  · rw [pb0_view d x hlt]
    intro o ho
    rcases List.mem_append.1 ho with ho | ho
    · exact h3 o ho
    · simp at ho
      subst ho
      rfl

/-- push_back：放到队尾 -/
theorem pushBack_ok (d : D α) (x : α) (hw : WF d) :
    view (pushBack d x) = view d ++ [some x] ∧ WF (pushBack d x) := by
  obtain ⟨hw', hlt, hv⟩ := prep_ok d hw
  refine ⟨?_, pb0_wf _ x hw' hlt⟩
  rw [pushBack, pb0_view _ x hlt, hv]

/-! ## push_front -/

theorem fh_lt (d : D α) (hc : 0 < d.cap) : fh d < d.cap := Nat.mod_lt _ hc

theorem fh_step (d : D α) (hc : 0 < d.cap) (k : Nat) : (fh d + (k + 1)) % d.cap = (d.head + k) % d.cap := by
  unfold fh
  rw [Nat.mod_add_mod]
  have e : d.head + d.cap - 1 + (k + 1) = d.head + k + d.cap := by omega
  rw [e, Nat.add_mod_right]

theorem fh_ne (d : D α) (hc : 0 < d.cap) (k : Nat) (hk : k + 1 < d.cap) : (d.head + k) % d.cap ≠ fh d := by
  intro e
  have e2 : fh d = (d.head + (d.cap - 1)) % d.cap := by
    unfold fh
    rw [show d.head + d.cap - 1 = d.head + (d.cap - 1) by omega]
  rw [e2] at e
  have hc1 : d.cap - 1 < d.cap := by omega
  have hk1 : k < d.cap := by omega
  have := mod_inj hk1 hc1 e
  omega

theorem pf0_view (d : D α) (x : α) (hlt : d.n < d.cap) : view (pf0 d x) = some x :: view d := by
  have hc : 0 < d.cap := by omega
  rw [view_cons (pf0 d x) d.n rfl]
  have h0 : (fh d + 0) % d.cap = fh d := by rw [Nat.add_zero]; exact Nat.mod_eq_of_lt (fh_lt d hc)
  congr 1
  · show (if (fh d + 0) % d.cap = fh d then some x else _) = some x
    rw [ite_eq_left h0]
  · unfold view
    apply map_eq
    intro k hk
    have hk' := List.mem_range.1 hk
    have hk1 : k + 1 < d.cap := by omega
    show (if (fh d + (k + 1)) % d.cap = fh d then some x else d.buf ((fh d + (k + 1)) % d.cap)) = _
    rw [fh_step d hc k, ite_eq_right (fh_ne d hc k hk1)]

theorem pf0_wf (d : D α) (x : α) (hw : WF d) (hlt : d.n < d.cap) : WF (pf0 d x) := by
  obtain ⟨_, _, h3⟩ := hw
  have hc : 0 < d.cap := by omega
  refine ⟨?_, Or.inl (fh_lt d hc), ?_⟩
  · show d.n + 1 ≤ d.cap
    omega
  · rw [pf0_view d x hlt]
    intro o ho
    rcases List.mem_cons.1 ho with rfl | ho
    · rfl
    · exact h3 o ho

/-- push_front：放到队头 -/
theorem pushFront_ok (d : D α) (x : α) (hw : WF d) :
    view (pushFront d x) = some x :: view d ∧ WF (pushFront d x) := by
  obtain ⟨hw', hlt, hv⟩ := prep_ok d hw
  refine ⟨?_, pf0_wf _ x hw' hlt⟩
  rw [pushFront, pf0_view _ x hlt, hv]

/-! ## pop_front -/

theorem popF0_view (d : D α) (hw : WF d) (hn : d.n ≠ 0) : view d = d.buf d.head :: view (popF0 d) := by
  obtain ⟨h1, h2, _⟩ := hw
  have hc : 0 < d.cap := by omega
  have hh : d.head < d.cap := by omega
  have h0 : (d.head + 0) % d.cap = d.head := by rw [Nat.add_zero]; exact Nat.mod_eq_of_lt hh
  rw [view_cons d (d.n - 1) (by omega), h0]
  congr 1
  unfold view
  show _ = List.map _ (List.range (d.n - 1))
  apply map_eq
  intro k hk
  have hk' := List.mem_range.1 hk
  have e1 : ((d.head + 1) % d.cap + k) % d.cap = (d.head + (k + 1)) % d.cap := by
    rw [Nat.mod_add_mod, show d.head + 1 + k = d.head + (k + 1) by omega]
  have hne : (d.head + (k + 1)) % d.cap ≠ d.head := by
    intro e
    have e' : (d.head + (k + 1)) % d.cap = (d.head + 0) % d.cap := by rw [e, h0]
    have := mod_inj (h := d.head) (by omega : k + 1 < d.cap) (by omega : 0 < d.cap) e'
    omega
  show _ = (if ((d.head + 1) % d.cap + k) % d.cap = d.head then none
    else d.buf (((d.head + 1) % d.cap + k) % d.cap))
  rw [e1, ite_eq_right hne]

/-- pop_front：取出队头。空的时候是 None，队列不变 -/
theorem popFront_ok (d : D α) (hw : WF d) :
    (d.n = 0 → popFront d = (none, d) ∧ view d = []) ∧
    (d.n ≠ 0 → view d = (popFront d).1 :: view (popFront d).2 ∧ WF (popFront d).2) := by
  refine ⟨fun hn => ⟨by unfold popFront; rw [ite_eq_left hn], by simp [view, hn]⟩, fun hn => ?_⟩
  have hp : popFront d = (d.buf d.head, popF0 d) := by unfold popFront; rw [ite_eq_right hn]
  rw [hp]
  have hv := popF0_view d hw hn
  obtain ⟨h1, _, h3⟩ := hw
  have hc : 0 < d.cap := by omega
  refine ⟨hv, ?_, Or.inl (Nat.mod_lt _ hc), ?_⟩
  · show d.n - 1 ≤ d.cap
    omega
  · intro o ho
    exact h3 o (by rw [hv]; exact List.mem_cons_of_mem _ ho)

/-! ## pop_back -/

theorem popB0_view (d : D α) (hw : WF d) (hn : d.n ≠ 0) : view d = view (popB0 d) ++ [d.buf (bi d)] := by
  have h1 := hw.1
  have hb : bi d = (d.head + (d.n - 1)) % d.cap := by
    unfold bi
    rw [show d.head + d.n - 1 = d.head + (d.n - 1) by omega]
  rw [view_snoc d (d.n - 1) (by omega), ← hb]
  congr 1
  refine (view_ext (popB0 d) { d with n := d.n - 1 } rfl ?_).symm
  intro k hk
  have hk' : k < d.n - 1 := hk
  have hne : (d.head + k) % d.cap ≠ bi d := by
    rw [hb]
    intro e
    have := mod_inj (by omega : k < d.cap) (by omega : d.n - 1 < d.cap) e
    omega
  show (if (d.head + k) % d.cap = bi d then none else d.buf ((d.head + k) % d.cap)) = d.buf ((d.head + k) % d.cap)
  rw [ite_eq_right hne]

/-- pop_back：取出队尾。空的时候是 None，队列不变 -/
theorem popBack_ok (d : D α) (hw : WF d) :
    (d.n = 0 → popBack d = (none, d) ∧ view d = []) ∧
    (d.n ≠ 0 → view d = view (popBack d).2 ++ [(popBack d).1] ∧ WF (popBack d).2) := by
  refine ⟨fun hn => ⟨by unfold popBack; rw [ite_eq_left hn], by simp [view, hn]⟩, fun hn => ?_⟩
  have hp : popBack d = (d.buf (bi d), popB0 d) := by unfold popBack; rw [ite_eq_right hn]
  rw [hp]
  have hv := popB0_view d hw hn
  obtain ⟨h1, h2, h3⟩ := hw
  refine ⟨hv, ?_, h2, ?_⟩
  · show d.n - 1 ≤ d.cap
    omega
  · intro o ho
    exact h3 o (by rw [hv]; exact List.mem_append_left _ ho)

/-- 不空时取出来的是 Some（view 里没有空位） -/
theorem pop_some (d : D α) (hw : WF d) (hn : d.n ≠ 0) :
    (popFront d).1.isSome = true ∧ (popBack d).1.isSome = true := by
  have h3 := hw.2.2
  refine ⟨h3 _ ?_, h3 _ ?_⟩
  · rw [(popFront_ok d hw).2 hn |>.1]
    exact List.mem_cons_self ..
  · rw [(popBack_ok d hw).2 hn |>.1]
    exact List.mem_append_right _ (List.mem_cons_self ..)

/-! ## get、new、of -/

/-- get i：view 的第 i 个；越界是 None -/
theorem get_ok (d : D α) (i : Nat) : (i < d.n → (view d)[i]? = some (get d i)) ∧ (d.n ≤ i → get d i = none) := by
  refine ⟨fun hi => ?_, fun hi => ?_⟩
  · unfold view get
    first
      | (rw [List.getElem?_map, List.getElem?_range hi, ite_eq_left hi]) <;> rfl
      | simp [hi]
  · have hi' : ¬i < d.n := by omega
    unfold get
    rw [ite_eq_right hi']

theorem empty_ok : WF (empty : D α) ∧ view (empty : D α) = [] := by
  refine ⟨⟨Nat.le_refl _, Or.inr ⟨rfl, rfl⟩, ?_⟩, ?_⟩ <;> simp [view, empty]

/-- of(xs)：一个个 push_back -/
theorem of_ok : ∀ (xs : List α) (d : D α), WF d →
    view (xs.foldl pushBack d) = view d ++ xs.map some ∧ WF (xs.foldl pushBack d)
  | [], _, hw => ⟨by simp, hw⟩
  | x :: xs, d, hw => by
    obtain ⟨hv, hw'⟩ := pushBack_ok d x hw
    obtain ⟨hv2, hw2⟩ := of_ok xs (pushBack d x) hw'
    simp only [List.foldl_cons, List.map_cons]
    rw [hv2, hv]
    exact ⟨by simp, hw2⟩

end Deque
end Lark
