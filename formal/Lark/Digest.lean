/-
标准库的证明 · 摘要和校验和（std/digest.lark）

照着 std/digest.lark 写其中三样，字节串写成 List Nat（每个 < 256）：

- crc32：短的（< 512 字节）逐位算，长的查表算。查表的一步是 t[(c ^ b) & 0xFF] ^ (c >>> 8)，
  t[n] 是 n 逐位算 8 次。证明两种算法对任何输入结果都一样（`crc32_ok`）：逐位算的一步对 ^ 是线性的
  （`st_lin`），c ^ b 拆成低 8 位和 (c >>> 8) << 8 两半，高的那一半走 8 步正好变成 c >>> 8（`lin`）。
  另外 (c ^ b) & 0xFF < 256，查表不会越界。
- to_hex / from_hex：from_hex(to_hex(d)) = d；from_hex 大小写都认。
- equal：两个字节串相同时才是 true（`equal_ok`）。

SHA-1 / SHA-256 / SHA-512 和 HMAC 就是照着标准一步步写的，没有另外的规格可比，靠 tests/unit/digest.lark
里的标准测试向量（FIPS 180、RFC 4231）。
-/

namespace Lark
namespace Digest

/-! ## crc32 -/

def P : Nat := 0xEDB88320
def M : Nat := 0xFFFFFFFF

/-- 逐位算的一步：c = if (c & 1) != 0 { (c >>> 1) ^ 0xEDB8_8320 } else { c >>> 1 } -/
def st (c : Nat) : Nat := if c &&& 1 ≠ 0 then (c >>> 1) ^^^ P else c >>> 1

def steps : Nat → Nat → Nat
  | 0, c => c
  | k + 1, c => steps k (st c)

/-- 短的：一个字节逐位算 8 次 -/
def fbit (c b : Nat) : Nat := steps 8 (c ^^^ b)
/-- 长的：查表，t[n] 是 crc_table 里的第 n 项 = steps 8 n -/
def ftab (c b : Nat) : Nat := steps 8 ((c ^^^ b) &&& 255) ^^^ (c >>> 8)

def crc32 (d : List Nat) : Nat := if d.length < 512 then d.foldl fbit M ^^^ M else d.foldl ftab M ^^^ M

-- tests/unit/digest.lark 里的两个；再加一个 600 字节的，两种算法一样
#guard crc32 [49, 50, 51, 52, 53, 54, 55, 56, 57] == 0xCBF43926
#guard crc32 [] == 0
#guard ((List.range 600).map (· % 256)).foldl ftab M == ((List.range 600).map (· % 256)).foldl fbit M

theorem and1 (c : Nat) : (c &&& 1 ≠ 0) ↔ c.testBit 0 = true := by
  rw [Nat.and_one_is_mod, Nat.testBit_zero, decide_eq_true_eq]
  constructor <;> intro h <;> omega

theorem shl_shr (h k : Nat) : (h <<< (k + 1)) >>> 1 = h <<< k := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_shiftRight, Nat.testBit_shiftLeft, Nat.testBit_shiftLeft]
  have e : 1 + i - (k + 1) = i - k := by omega
  rw [e]
  by_cases hik : k ≤ i
  · have h1 : k + 1 ≤ 1 + i := by omega
    simp [h1, hik]
  · have h1 : ¬(k + 1 ≤ 1 + i) := by omega
    simp [h1, hik]

/-- 一步对 ^ 线性：低 k + 1 位是 0 的那一半，走一步就是右移一位 -/
theorem st_lin (x h k : Nat) : st (x ^^^ (h <<< (k + 1))) = st x ^^^ (h <<< k) := by
  have hb : (x ^^^ (h <<< (k + 1))).testBit 0 = x.testBit 0 := by
    rw [Nat.testBit_xor, Nat.testBit_shiftLeft]
    simp
  have hs : (x ^^^ (h <<< (k + 1))) >>> 1 = (x >>> 1) ^^^ (h <<< k) := by
    rw [Nat.shiftRight_xor_distrib, shl_shr]
  have hc : ((x ^^^ (h <<< (k + 1))) &&& 1 ≠ 0) ↔ (x &&& 1 ≠ 0) := by rw [and1, and1, hb]
  unfold st
  by_cases hx : x &&& 1 ≠ 0
  · rw [ite_eq_left (hc.2 hx), ite_eq_left hx, hs]
    ac_rfl
  · rw [ite_eq_right (fun e => hx (hc.1 e)), ite_eq_right hx, hs]

/-- 走 k 步：高的那一半 h << k 变成 h -/
theorem lin : ∀ (k x h : Nat), steps k (x ^^^ (h <<< k)) = steps k x ^^^ h
  | 0, x, h => by simp [steps]
  | k + 1, x, h => by
    show steps k (st (x ^^^ (h <<< (k + 1)))) = steps k (st x) ^^^ h
    rw [st_lin, lin k]

/-- 拆成低 8 位和高的部分 -/
theorem split8 (y : Nat) : y = (y &&& 255) ^^^ ((y >>> 8) <<< 8) := by
  rw [show (255 : Nat) = 2 ^ 8 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_xor, Nat.testBit_mod_two_pow, Nat.testBit_shiftLeft, Nat.testBit_shiftRight]
  by_cases hi : i < 8
  · have h1 : ¬(i ≥ 8) := by omega
    simp [hi, h1]
  · have h1 : i ≥ 8 := by omega
    have e : 8 + (i - 8) = i := by omega
    simp [hi, h1, e]

theorem hi8 (c b : Nat) (hb : b < 256) : (c ^^^ b) >>> 8 = c >>> 8 := by
  have h0 : b >>> 8 = 0 := by
    rw [Nat.shiftRight_eq_div_pow]
    exact Nat.div_eq_of_lt hb
  rw [Nat.shiftRight_xor_distrib, h0, Nat.xor_zero]

/-- 查表的一步和逐位算 8 次一样 -/
theorem tab_ok (c b : Nat) (hb : b < 256) : fbit c b = ftab c b := by
  unfold fbit ftab
  have d := split8 (c ^^^ b)
  rw [hi8 c b hb] at d
  have := lin 8 ((c ^^^ b) &&& 255) (c >>> 8)
  rw [← d] at this
  exact this

/-- 查表的下标在 0..256 里 -/
theorem tab_idx (x : Nat) : x &&& 255 < 256 := Nat.and_lt_two_pow x (n := 8) (by decide)

theorem fold_eq : ∀ (d : List Nat) (c : Nat), (∀ b ∈ d, b < 256) → d.foldl fbit c = d.foldl ftab c
  | [], _, _ => rfl
  | b :: d, c, h => by
    simp only [List.foldl_cons]
    rw [tab_ok c b (h b (List.mem_cons_self ..))]
    exact fold_eq d _ (fun x hx => h x (List.mem_cons_of_mem _ hx))

/-- crc32 长短两条路结果一样：都是逐位算的 CRC-32 -/
theorem crc32_ok (d : List Nat) (h : ∀ b ∈ d, b < 256) : crc32 d = d.foldl fbit M ^^^ M := by
  unfold crc32
  split
  · rfl
  · rw [fold_eq d M h]

/-! ## to_hex / from_hex -/

/-- HEX = "0123456789abcdef" 的第 n 个 -/
def hexOf (n : Nat) : Nat := if n < 10 then 48 + n else 87 + n

def toHex : List Nat → List Nat
  | [] => []
  | b :: d => hexOf (b / 16) :: hexOf (b % 16) :: toHex d

/-- hex_val：不是十六进制数字时是 none（Lark 里是 -1） -/
def hexVal (c : Nat) : Option Nat :=
  if 48 ≤ c ∧ c ≤ 57 then some (c - 48)
  else if 97 ≤ c ∧ c ≤ 102 then some (c - 87)
  else if 65 ≤ c ∧ c ≤ 70 then some (c - 55)
  else none

/-- from_hex：长度是奇数、有不是十六进制的字符时是 none（Lark 里是 Err） -/
def fromHex : List Nat → Option (List Nat)
  | [] => some []
  | [_] => none
  | h :: l :: r =>
    match hexVal h, hexVal l, fromHex r with
    | some hi, some lo, some rest => some ((hi * 16 + lo) :: rest)
    | _, _, _ => none

#guard toHex [0x0a, 0xff] == [48, 97, 102, 102]
#guard fromHex [65, 98] == some [0xab]
#guard fromHex [48] == none
#guard fromHex [48, 103] == none

theorem hex_val_of : ∀ n, n < 16 → hexVal (hexOf n) = some n := by decide

/-- from_hex(to_hex(d)) = d -/
theorem fromHex_toHex : ∀ d : List Nat, (∀ b ∈ d, b < 256) → fromHex (toHex d) = some d
  | [], _ => rfl
  | b :: d, h => by
    have hb := h b (List.mem_cons_self ..)
    simp only [toHex, fromHex, hex_val_of (b / 16) (by omega), hex_val_of (b % 16) (by omega),
      fromHex_toHex d (fun x hx => h x (List.mem_cons_of_mem _ hx))]
    have e : b / 16 * 16 + b % 16 = b := by omega
    rw [e]

/-! ## equal -/

/-- equal：长度不同是 false；否则所有 a[i] ^ b[i] 或起来是 0 -/
def equal (a b : List Nat) : Bool :=
  if a.length ≠ b.length then false else (List.zipWith (· ^^^ ·) a b).foldl (· ||| ·) 0 == 0

#guard equal [1, 2, 3] [1, 2, 3]
#guard !equal [1, 2, 3] [1, 2, 4]
#guard !equal [1, 2] [1, 2, 3]

theorem xor_eq_zero {x y : Nat} : x ^^^ y = 0 ↔ x = y := by
  constructor
  · intro h
    apply Nat.eq_of_testBit_eq
    intro i
    have h1 : (x.testBit i ^^ y.testBit i) = false := by rw [← Nat.testBit_xor, h, Nat.zero_testBit]
    revert h1
    cases x.testBit i <;> cases y.testBit i <;> decide
  · intro h
    rw [h, Nat.xor_self]

theorem fold_or : ∀ (l : List Nat) (acc : Nat), l.foldl (· ||| ·) acc = 0 ↔ acc = 0 ∧ ∀ x ∈ l, x = 0
  | [], acc => by simp
  | x :: l, acc => by simp [fold_or l, Nat.or_eq_zero_iff, and_assoc]

theorem zip_zero : ∀ (a b : List Nat), a.length = b.length →
    ((∀ x ∈ List.zipWith (· ^^^ ·) a b, x = 0) ↔ a = b)
  | [], [], _ => by simp
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | x :: a, y :: b, h => by simp [xor_eq_zero, zip_zero a b (by simpa using h)]

/-- equal 是 true 正好当两个字节串相同 -/
theorem equal_ok (a b : List Nat) : equal a b = true ↔ a = b := by
  unfold equal
  by_cases hl : a.length ≠ b.length
  · rw [ite_eq_left hl]
    constructor
    · intro h
      exact absurd h (by decide)
    · intro h
      exact absurd (by rw [h]) hl
  · rw [ite_eq_right hl, beq_iff_eq, fold_or, zip_zero a b (by omega)]
    simp

end Digest
end Lark
