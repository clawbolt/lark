/-
标准库的证明 · 格式化（std/fmt.lark）

照着 std/fmt.lark 写 radix、thousands 和 fixed(int, digits)。数字写成每一位的值（0..base-1），
radix 里 slice(digits, d, d + 1) 就是第 d 个字符，这里直接记 d。

- radix：Lark 的 % 和 / 是向 0 截断的（C 的语义，Lean 里是 Int.tmod / Int.tdiv）。为了最小的 int 不溢出，
  循环里用负数 k 累计，d = -(k % base)。证明这个循环和对 |n| 用 Nat 的 % / 一样（`loop_nat`），
  所以写出来的每一位都 < base，第一位不是 0，按 base 读回去正好是 |n|（`radix_ok`）。
- thousands：去掉逗号就是原来的数字（`thou_strip`）。
- fixed(n, digits)：前面补 0 直到比 digits 长，再在倒数第 digits 位前插小数点；小数点后面正好 digits 位，
  前面至少一位，补的 0 不改变值（`fixed_ok`）。
-/

namespace Lark
namespace Fmt

/-! ## radix -/

/-- radix 的循环：k ≤ 0，d = -(k % base)，k = k / base，d 放到最前面 -/
def loop (b : Nat) : Nat → Int → List Nat → List Nat
  | 0, _, acc => acc
  | f + 1, k, acc => if k = 0 then acc else loop b f (k.tdiv b) ((-(k.tmod b)).toNat :: acc)

/-- 同一个循环，对 |n| 用 Nat -/
def nl (b : Nat) : Nat → Nat → List Nat → List Nat
  | 0, _, acc => acc
  | f + 1, m, acc => if m = 0 then acc else nl b f (m / b) ((m % b) :: acc)

/-- 从左往右按 base 读 -/
def val (b : Nat) (a : Nat) (ds : List Nat) : Nat := ds.foldl (fun x d => x * b + d) a

/-- radix(n, base) 的各位（不含负号）和是否有负号；燃料给 |n| + 1 -/
def radix (b : Nat) (n : Int) : List Nat × Bool :=
  if n = 0 then ([0], false)
  else (loop b (n.natAbs + 1) (if n < 0 then n else -n) [], decide (n < 0))

-- fmt.hex(255) = "ff"、fmt.bin(5) = "101"、fmt.radix(-35, 36) = "-z"
#guard radix 16 255 == ([15, 15], false)
#guard radix 2 5 == ([1, 0, 1], false)
#guard radix 36 (-35) == ([35], true)
#guard radix 10 (-9223372036854775808) == ([9, 2, 2, 3, 3, 7, 2, 0, 3, 6, 8, 5, 4, 7, 7, 5, 8, 0, 8], true)

theorem loop_nat (b : Nat) : ∀ (f m : Nat) (acc : List Nat), loop b f (-(m : Int)) acc = nl b f m acc
  | 0, _, _ => rfl
  | f + 1, 0, acc => by simp [loop, nl]
  | f + 1, m + 1, acc => by
    have h0 : (-((m + 1 : Nat) : Int)) ≠ 0 := by omega
    have hd : (-((m + 1 : Nat) : Int)).tdiv (b : Int) = -(((m + 1) / b : Nat) : Int) := rfl
    have hm : (-(-((m + 1 : Nat) : Int)).tmod (b : Int)).toNat = (m + 1) % b := by
      show (-(-(((m + 1) % b : Nat) : Int))).toNat = _
      exact congrArg Int.toNat (Int.neg_neg _)
    unfold loop nl
    rw [ite_eq_right h0, ite_eq_right (by omega : ¬m + 1 = 0), hd, hm, loop_nat b f]

theorem nl_zero (b : Nat) : ∀ (f : Nat) (acc : List Nat), nl b f 0 acc = acc
  | 0, _ => rfl
  | _ + 1, _ => by simp [nl]

/-- 读回去：nl 每一步把 m 换成 m / b、把 m % b 放到前面，按 base 读不变 -/
theorem nl_val (b : Nat) (hb : 1 < b) : ∀ (f m : Nat) (acc : List Nat), m < f → val b 0 (nl b f m acc) = val b m acc
  | 0, _, _, h => absurd h (Nat.not_lt_zero _)
  | f + 1, m, acc, h => by
    unfold nl
    by_cases hm : m = 0
    · rw [ite_eq_left hm, hm]
    · rw [ite_eq_right hm]
      have hlt : m / b < m := Nat.div_lt_self (by omega) hb
      rw [nl_val b hb f (m / b) _ (by omega)]
      show val b (m / b * b + m % b) acc = val b m acc
      rw [Nat.mul_comm, Nat.div_add_mod]

theorem nl_lt (b : Nat) (hb : 1 < b) : ∀ (f m : Nat) (acc : List Nat), (∀ d ∈ acc, d < b) → ∀ d ∈ nl b f m acc, d < b
  | 0, _, _, h => h
  | f + 1, m, acc, h => by
    unfold nl
    split
    · exact h
    · refine nl_lt b hb f (m / b) _ ?_
      intro d hd
      rcases List.mem_cons.1 hd with rfl | hd
      · exact Nat.mod_lt _ (by omega)
      · exact h d hd

/-- 第一位不是 0 -/
theorem nl_head (b : Nat) (hb : 1 < b) : ∀ (f m : Nat) (acc : List Nat), m < f → 0 < m →
    ∃ d ds, nl b f m acc = d :: ds ∧ d ≠ 0
  | 0, _, _, h, _ => absurd h (Nat.not_lt_zero _)
  | f + 1, m, acc, h, hm => by
    unfold nl
    rw [ite_eq_right (by omega : ¬m = 0)]
    have hlt : m / b < m := Nat.div_lt_self hm hb
    by_cases h0 : m / b = 0
    · rw [h0, nl_zero]
      have hmb : m < b := by
        rcases Nat.lt_or_ge m b with h1 | h1
        · exact h1
        · have := Nat.div_pos h1 (by omega : 0 < b)
          omega
      exact ⟨m % b, acc, rfl, by rw [Nat.mod_eq_of_lt hmb]; omega⟩
    · exact nl_head b hb f (m / b) _ (by omega) (Nat.pos_of_ne_zero h0)

/-- radix 写出来的：每一位 < base，第一位不是 0（n = 0 时是 "0"），按 base 读回去是 |n|，负号正好在 n < 0 时有 -/
theorem radix_ok (b : Nat) (hb : 1 < b) (n : Int) :
    (radix b n).2 = decide (n < 0) ∧ (∀ d ∈ (radix b n).1, d < b) ∧ val b 0 (radix b n).1 = n.natAbs ∧
    (n ≠ 0 → ∃ d ds, (radix b n).1 = d :: ds ∧ d ≠ 0) := by
  unfold radix
  by_cases hn : n = 0
  · subst hn
    refine ⟨rfl, ?_, by simp [val], fun h => absurd rfl h⟩
    intro d hd
    simp at hd
    omega
  · rw [ite_eq_right hn]
    have hk : (if n < 0 then n else -n) = -((n.natAbs : Nat) : Int) := by
      by_cases h : n < 0
      · rw [ite_eq_left h]
        have e := Int.natAbs_of_nonneg (by omega : (0 : Int) ≤ -n)
        rw [Int.natAbs_neg] at e
        omega
      · rw [ite_eq_right h]
        have e := Int.natAbs_of_nonneg (by omega : (0 : Int) ≤ n)
        omega
    rw [hk, loop_nat]
    have hm : n.natAbs < n.natAbs + 1 := by omega
    exact ⟨rfl, nl_lt b hb _ _ [] (by simp), nl_val b hb _ _ [] hm,
      fun _ => nl_head b hb _ _ [] hm (Int.natAbs_pos.2 hn)⟩

/-! ## thousands -/

/-- thousands 的循环：第 i 位前面，i > 0 且后面还剩 3 的倍数位时加一个逗号（44） -/
def thouL (L : Nat) : Nat → List Nat → List Nat
  | _, [] => []
  | i, c :: r => (if 0 < i ∧ (L - i) % 3 = 0 then [44] else []) ++ c :: thouL L (i + 1) r

def thou (body : List Nat) : List Nat := thouL body.length 0 body

-- "1234567" 写成 "1,234,567"
#guard thou [49, 50, 51, 52, 53, 54, 55] == [49, 44, 50, 51, 52, 44, 53, 54, 55]
#guard thou [49, 50, 51] == [49, 50, 51]

theorem thouL_strip (L : Nat) : ∀ (i : Nat) (body : List Nat), (∀ c ∈ body, c ≠ 44) →
    (thouL L i body).filter (fun c => c != 44) = body
  | _, [], _ => rfl
  | i, c :: r, h => by
    have hc := h c (List.mem_cons_self ..)
    have ih := thouL_strip L (i + 1) r (fun x hx => h x (List.mem_cons_of_mem _ hx))
    unfold thouL
    split <;> simp [hc, ih]

/-- thousands 去掉逗号就是原来的数字 -/
theorem thou_strip (body : List Nat) (h : ∀ c ∈ body, c ≠ 44) : (thou body).filter (fun c => c != 44) = body :=
  thouL_strip body.length 0 body h

/-! ## fixed(n, digits) -/

/-- for len(body) <= digits { body = "0" + body }（数字记成每一位的值，"0" 是 0） -/
def padL (d : Nat) : Nat → List Nat → List Nat
  | 0, body => body
  | f + 1, body => if body.length ≤ d then padL d f (0 :: body) else body

/-- 小数点前、后两部分 -/
def fixedP (d : Nat) (body : List Nat) : List Nat × List Nat :=
  let p := padL d (d + 1) body
  (p.take (p.length - d), p.drop (p.length - d))

-- fixed(31416, 4) = "3.1416"、fixed(5, 2) = "0.05"
#guard fixedP 4 [3, 1, 4, 1, 6] == ([3], [1, 4, 1, 6])
#guard fixedP 2 [5] == ([0], [0, 5])

theorem val_zero (b : Nat) (ds : List Nat) : val b 0 (0 :: ds) = val b 0 ds := by
  show val b (0 * b + 0) ds = val b 0 ds
  rw [Nat.zero_mul]

theorem padL_ok (d : Nat) : ∀ (f : Nat) (body : List Nat), d + 1 ≤ f + body.length →
    d < (padL d f body).length ∧ val 10 0 (padL d f body) = val 10 0 body
  | 0, body, h => ⟨by simp [padL]; omega, rfl⟩
  | f + 1, body, h => by
    unfold padL
    by_cases hb : body.length ≤ d
    · rw [ite_eq_left hb]
      obtain ⟨h1, h2⟩ := padL_ok d f (0 :: body) (by simp; omega)
      exact ⟨h1, by rw [h2, val_zero]⟩
    · rw [ite_eq_right hb]
      exact ⟨by omega, rfl⟩

/-- fixed：小数点后正好 digits 位，前面至少一位；两部分接起来按十进制读，还是原来的数 -/
theorem fixed_ok (d : Nat) (body : List Nat) :
    (fixedP d body).2.length = d ∧ 0 < (fixedP d body).1.length ∧
    val 10 0 ((fixedP d body).1 ++ (fixedP d body).2) = val 10 0 body := by
  obtain ⟨h1, h2⟩ := padL_ok d (d + 1) body (by omega)
  unfold fixedP
  simp only
  refine ⟨?_, ?_, ?_⟩
  · simp only [List.length_drop]
    omega
  · simp only [List.length_take]
    omega
  · rw [List.take_append_drop, h2]

end Fmt
end Lark
