/-
标准库的证明 · 字节里的整数（std/bytes.lark）

照着 std/bytes.lark 写一份。int 是有符号的 64 位：写成它在内存里的 64 位 bits v = v mod 2^64（Nat），
读 u64 时再按有符号解回来（toInt64）。字节串写成 List Nat。

- 写：((v >>> s) & 0xFF).wrap_u8() 是 bits v / 2^s % 256。s 最大是 56，所以 >>> 是逻辑右移还是算术右移都一样。
- 读：几个字节各自移到不重叠的位置再 |，等于加起来（每个字节 < 256）；u64_be 里 (hi << 32) 在 64 位里回绕，写成 % 2^64。
- d[at] 越界时 panic：读写成 Option，越界是 none；从 at 开始读写成先 drop at。

证明：写进去再从同一个位置读出来，u16、u32 得到低 16 / 32 位，u64_be 得到原来的 int（负数也一样）；
反过来，任意几个字节读成整数再写回去，还是这几个字节。
-/

namespace Lark
namespace Bytes

/-- int 在内存里的 64 位 -/
def bits (v : Int) : Nat := (v % 18446744073709551616).toNat

/-- 64 位按有符号解回 int -/
def toInt64 (u : Nat) : Int := if u < 9223372036854775808 then (u : Int) else (u : Int) - 18446744073709551616

/-! ## 写：push_* 追加的字节（u 是 bits v） -/

def be16 (u : Nat) : List Nat := [u / 256 % 256, u % 256]
def le16 (u : Nat) : List Nat := [u % 256, u / 256 % 256]
def be32 (u : Nat) : List Nat := [u / 16777216 % 256, u / 65536 % 256, u / 256 % 256, u % 256]
def le32 (u : Nat) : List Nat := [u % 256, u / 256 % 256, u / 65536 % 256, u / 16777216 % 256]
def be64 (u : Nat) : List Nat :=
  [u / 72057594037927936 % 256, u / 281474976710656 % 256, u / 1099511627776 % 256, u / 4294967296 % 256,
   u / 16777216 % 256, u / 65536 % 256, u / 256 % 256, u % 256]

/-! ## 读：u*_be(d, at) 是 rd* (d.drop at) -/

def rd16be : List Nat → Option Nat
  | a :: b :: _ => some (a * 256 + b)
  | _ => none

def rd16le : List Nat → Option Nat
  | a :: b :: _ => some (a + b * 256)
  | _ => none

def rd32be : List Nat → Option Nat
  | a :: b :: c :: d :: _ => some (a * 16777216 + b * 65536 + c * 256 + d)
  | _ => none

def rd32le : List Nat → Option Nat
  | a :: b :: c :: d :: _ => some (a + b * 256 + c * 65536 + d * 16777216)
  | _ => none

/-- u64_be：(u32_be(d, at) << 32) | u32_be(d, at + 4)，结果按有符号解 -/
def rd64be (l : List Nat) : Option Int :=
  match rd32be l, rd32be (l.drop 4) with
  | some h, some lo => some (toInt64 (h * 4294967296 % 18446744073709551616 + lo))
  | _, _ => none

/-! ## 例子 -/

example : be32 0x01020304 = [1, 2, 3, 4] := by decide
example : le32 0x01020304 = [4, 3, 2, 1] := by decide
example : rd32be [1, 2, 3, 4, 9] = some 0x01020304 := by decide
example : rd16le [0x34, 0x12] = some 0x1234 := by decide
-- -1 在内存里是 64 个 1，写成 8 个 0xFF，读回来还是 -1
example : be64 (bits (-1)) = [255, 255, 255, 255, 255, 255, 255, 255] := by decide
example : rd64be (be64 (bits (-1))) = some (-1) := by decide
-- 读越界
example : rd32be [1, 2, 3] = none := by decide

/-! ## 写进去再读出来 -/

theorem drop_app : ∀ (out l : List Nat), (out ++ l).drop out.length = l
  | [], _ => rfl
  | _ :: out, l => drop_app out l

theorem rt16be (out rest : List Nat) (u : Nat) :
    rd16be ((out ++ (be16 u ++ rest)).drop out.length) = some (u % 65536) := by
  rw [drop_app]
  simp only [be16, rd16be, List.cons_append, List.nil_append, Option.some.injEq]
  omega

theorem rt16le (out rest : List Nat) (u : Nat) :
    rd16le ((out ++ (le16 u ++ rest)).drop out.length) = some (u % 65536) := by
  rw [drop_app]
  simp only [le16, rd16le, List.cons_append, List.nil_append, Option.some.injEq]
  omega

theorem rt32be (out rest : List Nat) (u : Nat) :
    rd32be ((out ++ (be32 u ++ rest)).drop out.length) = some (u % 4294967296) := by
  rw [drop_app]
  simp only [be32, rd32be, List.cons_append, List.nil_append, Option.some.injEq]
  omega

theorem rt32le (out rest : List Nat) (u : Nat) :
    rd32le ((out ++ (le32 u ++ rest)).drop out.length) = some (u % 4294967296) := by
  rw [drop_app]
  simp only [le32, rd32le, List.cons_append, List.nil_append, Option.some.injEq]
  omega

theorem bits_lt (v : Int) : bits v < 18446744073709551616 := by
  have h0 := Int.emod_nonneg v (by decide : (18446744073709551616 : Int) ≠ 0)
  have h1 := Int.emod_lt_of_pos v (by decide : (0 : Int) < 18446744073709551616)
  have e := Int.toNat_of_nonneg h0
  unfold bits
  omega

theorem toInt_bits (v : Int) (h1 : -9223372036854775808 ≤ v) (h2 : v < 9223372036854775808) :
    toInt64 (bits v) = v := by
  have h0 := Int.emod_nonneg v (by decide : (18446744073709551616 : Int) ≠ 0)
  have e := Int.toNat_of_nonneg h0
  unfold toInt64 bits
  split <;> omega

/-- 4 个字节拼回去是低 32 位 -/
theorem join32 (x : Nat) :
    x / 16777216 % 256 * 16777216 + x / 65536 % 256 * 65536 + x / 256 % 256 * 256 + x % 256 = x % 4294967296 := by
  omega

theorem rd64_be64 (rest : List Nat) (u : Nat) (hu : u < 18446744073709551616) :
    rd64be (be64 u ++ rest) = some (toInt64 u) := by
  -- 高 4 个字节是 u / 2^32 的 4 个字节
  have hh1 : u / 72057594037927936 = u / 4294967296 / 16777216 := by rw [Nat.div_div_eq_div_mul]
  have hh2 : u / 281474976710656 = u / 4294967296 / 65536 := by rw [Nat.div_div_eq_div_mul]
  have hh3 : u / 1099511627776 = u / 4294967296 / 256 := by rw [Nat.div_div_eq_div_mul]
  simp only [be64, rd64be, rd32be, List.cons_append, List.drop]
  rw [hh1, hh2, hh3, join32, join32]
  have hlt : u / 4294967296 < 4294967296 := by omega
  rw [Nat.mod_eq_of_lt hlt, Nat.mod_eq_of_lt (by omega : u / 4294967296 * 4294967296 < 18446744073709551616)]
  have e : u / 4294967296 * 4294967296 + u % 4294967296 = u := by omega
  rw [e]

/-- push_u64_be 再 u64_be：得到原来的 int，负数也一样 -/
theorem rt64be (out rest : List Nat) (v : Int) (h1 : -9223372036854775808 ≤ v) (h2 : v < 9223372036854775808) :
    rd64be ((out ++ (be64 (bits v) ++ rest)).drop out.length) = some v := by
  rw [drop_app, rd64_be64 rest (bits v) (bits_lt v), toInt_bits v h1 h2]

/-! ## 反过来：几个字节读成整数再写回去，还是这几个字节 -/

theorem be16_rd {a b : Nat} (ha : a < 256) (hb : b < 256) : be16 (a * 256 + b) = [a, b] := by
  have e1 : (a * 256 + b) / 256 % 256 = a := by omega
  have e2 : (a * 256 + b) % 256 = b := by omega
  unfold be16
  rw [e1, e2]

theorem le16_rd {a b : Nat} (ha : a < 256) (hb : b < 256) : le16 (a + b * 256) = [a, b] := by
  have e1 : (a + b * 256) % 256 = a := by omega
  have e2 : (a + b * 256) / 256 % 256 = b := by omega
  unfold le16
  rw [e1, e2]

theorem be32_rd {a b c d : Nat} (ha : a < 256) (hb : b < 256) (hc : c < 256) (hd : d < 256) :
    be32 (a * 16777216 + b * 65536 + c * 256 + d) = [a, b, c, d] := by
  have e1 : (a * 16777216 + b * 65536 + c * 256 + d) / 16777216 % 256 = a := by omega
  have e2 : (a * 16777216 + b * 65536 + c * 256 + d) / 65536 % 256 = b := by omega
  have e3 : (a * 16777216 + b * 65536 + c * 256 + d) / 256 % 256 = c := by omega
  have e4 : (a * 16777216 + b * 65536 + c * 256 + d) % 256 = d := by omega
  unfold be32
  rw [e1, e2, e3, e4]

theorem le32_rd {a b c d : Nat} (ha : a < 256) (hb : b < 256) (hc : c < 256) (hd : d < 256) :
    le32 (a + b * 256 + c * 65536 + d * 16777216) = [a, b, c, d] := by
  have e1 : (a + b * 256 + c * 65536 + d * 16777216) % 256 = a := by omega
  have e2 : (a + b * 256 + c * 65536 + d * 16777216) / 256 % 256 = b := by omega
  have e3 : (a + b * 256 + c * 65536 + d * 16777216) / 65536 % 256 = c := by omega
  have e4 : (a + b * 256 + c * 65536 + d * 16777216) / 16777216 % 256 = d := by omega
  unfold le32
  rw [e1, e2, e3, e4]

end Bytes
end Lark
