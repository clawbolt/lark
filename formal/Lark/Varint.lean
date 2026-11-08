/-
标准库的证明 · varint（先证明，再照着写 std/bytes.lark 的 push_uvarint / uvarint）

无符号 LEB128（protobuf、wasm、Go 的 encoding/binary.Uvarint 都用它）：每个字节放 7 位，低位在前，
最高位是 1 表示后面还有。int 是 64 位，按位看成 0..2^64 的 Nat（负数就是高位是 1，和 u64_be 一样）。

写（照着它写 Lark）：
    x = v
    for x >>> 7 != 0 { out.push(((x & 0x7F) | 0x80).wrap_u8()); x = x >>> 7 }
    out.push(x.wrap_u8())
读（从 d[at] 起，最多 10 个字节）：
    第 i 个字节 b < 0x80 时结束：i == 9 且 b > 1 是溢出（None），否则结果是 x | (b << 7i)，读了 i + 1 个；
    b >= 0x80 时 x = x | ((b & 0x7F) << 7i)，接着读；没字节了或者 10 个都 >= 0x80 是 None。
    和 Go 一样，不是最短的写法（比如 0x80 0x00）也接受。

证明：
- `enc_ok`：写出来的每个字节 < 256，最多 10 个；
- `uvarint_enc`：任何 64 位的值写出来再读回去不变，后面跟着什么都不影响，读的字节数正好是写的长度；
- `uvarint_safe`：对任意输入，读成功时结果 < 2^64（不会超出 int），读了 1..10 个字节。
-/

namespace Lark
namespace Varint

def encF : Nat → Nat → List Nat
  | 0, x => [x]
  | f + 1, x => if x >>> 7 = 0 then [x] else ((x &&& 127) ||| 128) :: encF f (x >>> 7)

/-- push_uvarint 追加的字节（x 是 int 的 64 位） -/
def enc (x : Nat) : List Nat := encF 10 x

/-- uvarint 的循环：i 是第几个字节，x 是已经拼好的低位 -/
def dec : List Nat → Nat → Nat → Option (Nat × Nat)
  | [], _, _ => none
  | b :: r, i, x =>
    if b < 128 then (if i = 9 ∧ 1 < b then none else some (x ||| (b <<< (7 * i)), i + 1))
    else if i = 9 then none else dec r (i + 1) (x ||| ((b &&& 127) <<< (7 * i)))

/-- uvarint(d, at)：(值, 读了几个字节)，写成 d.drop at 上的 dec -/
def uvarint (d : List Nat) : Option (Nat × Nat) := dec d 0 0

/-! ## 例子 -/

#guard enc 300 == [172, 2]
#guard uvarint [172, 2, 99] == some (300, 2)
#guard enc 0 == [0]
#guard (enc (2 ^ 64 - 1)).length == 10
#guard uvarint (enc (2 ^ 64 - 1)) == some (2 ^ 64 - 1, 10)
-- 截断、第 10 个字节 > 1（超出 64 位）、10 个都 >= 0x80
#guard uvarint [128] == none
#guard uvarint [255, 255, 255, 255, 255, 255, 255, 255, 255, 2] == none
#guard uvarint [128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 0] == none
-- 不是最短的写法也接受（和 Go 一样）
#guard uvarint [128, 0] == some (0, 2)

/-! ## 位运算换成算术 -/

theorem shr7 (y : Nat) : y >>> 7 = y / 128 := by
  (rw [Nat.shiftRight_eq_div_pow]) <;> rfl

theorem and127 (y : Nat) : y &&& 127 = y % 128 := Nat.and_two_pow_sub_one_eq_mod y 7

theorem or128 (a : Nat) (h : a < 128) : a ||| 128 = a + 128 := Nat.or_two_pow_eq_add_of_lt (n := 7) h

/-- 低位 acc < 2^s 时，| 就是 + -/
theorem or_add (acc c s : Nat) (h : acc < 2 ^ s) : acc ||| (c <<< s) = acc + c * 2 ^ s := by
  rw [Nat.shiftLeft_eq, Nat.or_comm, Nat.mul_comm, ← Nat.two_pow_add_eq_or_of_lt h, Nat.add_comm]

theorem pow7 (i : Nat) : (2 : Nat) ^ (7 * (i + 1)) = 2 ^ (7 * i) * 128 := by
  rw [show 7 * (i + 1) = 7 * i + 7 by omega, Nat.pow_add, show (2 : Nat) ^ 7 = 128 from rfl]

/-- 读第 9 个字节（最后一个）时，剩下的值只能是 0 或 1 -/
theorem lt2 (y i : Nat) (h : y * 2 ^ (7 * i) < 2 ^ 64) (hi : i = 9) : y < 2 := by
  subst hi
  have e1 : (2 : Nat) ^ (7 * 9) = 9223372036854775808 := rfl
  have e2 : (2 : Nat) ^ 64 = 18446744073709551616 := rfl
  rw [e1, e2] at h
  omega

/-! ## 写 -/

theorem encF_small (f y : Nat) (h : y < 128) : encF f y = [y] := by
  cases f with
  | zero => rfl
  | succ f =>
    have h0 : y >>> 7 = 0 := by rw [shr7]; omega
    simp only [encF]
    rw [ite_eq_left h0]

theorem encF_big (f y : Nat) (h : 128 ≤ y) : encF (f + 1) y = (y % 128 + 128) :: encF f (y / 128) := by
  have h0 : ¬(y >>> 7 = 0) := by rw [shr7]; omega
  simp only [encF]
  rw [ite_eq_right h0, and127, or128 _ (Nat.mod_lt _ (by decide)), shr7]

theorem enc_bytes : ∀ (f y : Nat), 1 ≤ f → y < 2 ^ (7 * f - 6) →
    (∀ b ∈ encF f y, b < 256) ∧ (encF f y).length ≤ f
  | 0, _, h, _ => absurd h (by decide)
  | f + 1, y, _, hy => by
    by_cases h128 : y < 128
    · rw [encF_small (f + 1) y h128]
      refine ⟨fun b hb => ?_, by simp⟩
      simp at hb
      omega
    · have hf : 1 ≤ f := by
        cases f with
        | zero => simp at hy; omega
        | succ f => omega
      have e : 7 * (f + 1) - 6 = (7 * f - 6) + 7 := by omega
      rw [e, Nat.pow_add, show (2 : Nat) ^ 7 = 128 from rfl] at hy
      have hy' : y / 128 < 2 ^ (7 * f - 6) := by omega
      obtain ⟨h1, h2⟩ := enc_bytes f (y / 128) hf hy'
      rw [encF_big f y (by omega)]
      refine ⟨fun b hb => ?_, by simp; omega⟩
      rcases List.mem_cons.1 hb with rfl | hb
      · omega
      · exact h1 b hb

/-- push_uvarint 写出来的：每个字节 < 256，最多 10 个 -/
theorem enc_ok (x : Nat) (hx : x < 2 ^ 64) : (∀ b ∈ enc x, b < 256) ∧ (enc x).length ≤ 10 :=
  enc_bytes 10 x (by omega) (by simpa using hx)

/-! ## 写出来再读回去 -/

/-- 最后一个字节（< 0x80） -/
theorem dec_last (rest : List Nat) (y i acc : Nat) (h : y < 128) (hacc : acc < 2 ^ (7 * i))
    (hy : y * 2 ^ (7 * i) < 2 ^ 64) : dec (y :: rest) i acc = some (acc + y * 2 ^ (7 * i), i + 1) := by
  have hchk : ¬(i = 9 ∧ 1 < y) := by
    intro ⟨h9, h1⟩
    have := lt2 y i hy h9
    omega
  simp only [dec]
  rw [ite_eq_left h, ite_eq_right hchk, or_add acc y (7 * i) hacc]

theorem dec_enc (rest : List Nat) : ∀ (f y i acc : Nat), acc < 2 ^ (7 * i) → y * 2 ^ (7 * i) < 2 ^ 64 →
    i ≤ 9 → 9 ≤ i + f → dec (encF f y ++ rest) i acc = some (acc + y * 2 ^ (7 * i), i + (encF f y).length)
  | 0, y, i, acc, hacc, hy, _, hf => by
    have hy2 := lt2 y i hy (by omega)
    rw [encF_small 0 y (by omega)]
    exact dec_last rest y i acc (by omega) hacc hy
  | f + 1, y, i, acc, hacc, hy, hi, hf => by
    by_cases h128 : y < 128
    · rw [encF_small (f + 1) y h128]
      exact dec_last rest y i acc h128 hacc hy
    · have hi9 : i ≠ 9 := fun e => by have := lt2 y i hy e; omega
      have hb : ¬(y % 128 + 128 < 128) := by omega
      have hm : (y % 128 + 128) % 128 = y % 128 := by omega
      -- 下一步的低位和剩下的值
      have hP := pow7 i
      have hbP : y % 128 * 2 ^ (7 * i) ≤ 127 * 2 ^ (7 * i) := Nat.mul_le_mul_right _ (by omega)
      have hacc' : acc + y % 128 * 2 ^ (7 * i) < 2 ^ (7 * (i + 1)) := by rw [hP]; omega
      have e3 : y / 128 * (2 ^ (7 * i) * 128) = y / 128 * 128 * 2 ^ (7 * i) := by
        rw [Nat.mul_comm (2 ^ (7 * i)) 128, ← Nat.mul_assoc]
      have e4 : y / 128 * 128 * 2 ^ (7 * i) + y % 128 * 2 ^ (7 * i) = y * 2 ^ (7 * i) := by
        rw [← Nat.add_mul, show y / 128 * 128 + y % 128 = y by omega]
      have hle : y / 128 * 128 * 2 ^ (7 * i) ≤ y * 2 ^ (7 * i) := by omega
      have hy' : y / 128 * 2 ^ (7 * (i + 1)) < 2 ^ 64 := by rw [hP, e3]; omega
      rw [encF_big f y (by omega)]
      show dec ((y % 128 + 128) :: (encF f (y / 128) ++ rest)) i acc =
        some (acc + y * 2 ^ (7 * i), i + ((y % 128 + 128) :: encF f (y / 128)).length)
      simp only [dec]
      rw [ite_eq_right hb, ite_eq_right hi9, and127, hm, or_add acc (y % 128) (7 * i) hacc,
        dec_enc rest f (y / 128) (i + 1) _ hacc' hy' (by omega) (by omega), hP, e3]
      have e5 : acc + y % 128 * 2 ^ (7 * i) + y / 128 * 128 * 2 ^ (7 * i) = acc + y * 2 ^ (7 * i) := by omega
      rw [e5, List.length_cons, Nat.add_assoc, Nat.add_comm 1]

/-- 任何 64 位的值写出来再读回去不变，后面跟着什么都不影响 -/
theorem uvarint_enc (x : Nat) (rest : List Nat) (hx : x < 2 ^ 64) :
    uvarint (enc x ++ rest) = some (x, (enc x).length) := by
  have := dec_enc rest 10 x 0 0 (by simp) (by simpa using hx) (by omega) (by omega)
  simpa [uvarint, enc] using this

/-! ## 读任意输入都不会超出 64 位 -/

theorem dec_safe : ∀ (r : List Nat) (i acc v n : Nat), dec r i acc = some (v, n) → acc < 2 ^ (7 * i) →
    i ≤ 9 → v < 2 ^ 64 ∧ i < n ∧ n ≤ 10
  | [], _, _, _, _, h, _, _ => by simp [dec] at h
  | b :: r, i, acc, v, n, h, hacc, hi => by
    simp only [dec] at h
    have e63 : (2 : Nat) ^ 63 = 9223372036854775808 := rfl
    have e64 : (2 : Nat) ^ 64 = 18446744073709551616 := rfl
    by_cases hb : b < 128
    · rw [ite_eq_left hb] at h
      by_cases hc : i = 9 ∧ 1 < b
      · rw [ite_eq_left hc] at h
        simp at h
      · rw [ite_eq_right hc] at h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        rw [or_add acc b (7 * i) hacc]
        refine ⟨?_, by omega, by omega⟩
        by_cases h9 : i = 9
        · subst h9
          have e : (2 : Nat) ^ (7 * 9) = 9223372036854775808 := rfl
          rw [e] at hacc ⊢
          rw [e64]
          omega
        · have hbP : b * 2 ^ (7 * i) ≤ 127 * 2 ^ (7 * i) := Nat.mul_le_mul_right _ (by omega)
          have hP : 2 ^ (7 * i) * 128 ≤ 2 ^ 63 := by
            rw [← pow7]
            exact Nat.pow_le_pow_right (by decide) (by omega)
          rw [e63] at hP
          rw [e64]
          omega
    · rw [ite_eq_right hb] at h
      by_cases h9 : i = 9
      · rw [ite_eq_left h9] at h
        simp at h
      · rw [ite_eq_right h9, and127, or_add acc (b % 128) (7 * i) hacc] at h
        have hbP : b % 128 * 2 ^ (7 * i) ≤ 127 * 2 ^ (7 * i) := Nat.mul_le_mul_right _ (by omega)
        have hacc' : acc + b % 128 * 2 ^ (7 * i) < 2 ^ (7 * (i + 1)) := by rw [pow7]; omega
        have := dec_safe r (i + 1) _ v n h hacc' (by omega)
        omega

/-- 对任意输入：读成功时结果 < 2^64，读了 1..10 个字节 -/
theorem uvarint_safe (d : List Nat) (v n : Nat) (h : uvarint d = some (v, n)) : v < 2 ^ 64 ∧ 0 < n ∧ n ≤ 10 := by
  have := dec_safe d 0 0 v n h (by simp) (by omega)
  omega

end Varint
end Lark
