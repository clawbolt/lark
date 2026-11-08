/-
apps/ltls 的证明 · 阶段 4a：Ed25519 签名（RFC 8032 第 5.1 节）和 TLS 1.3 的 CertificateVerify（RFC 8446 第 4.4.3 节）
先证明，再写 apps/ltls/tls/ed25519.lark，换掉 Session.lean 里 HMAC 的占位。

规格照着 RFC 8032 第 5.1 节和第 6 节的 Python 写，模 p = 2^255 - 19 直接用 Nat 算，点用扩展坐标 (X, Y, Z, T)：
`padd`（第 5.1.4 节的加法公式）、`pmul`（从低位起的加倍-相加）、`recoverX` / `decodePt` / `encodePt`（第 5.1.2、5.1.3 节）、
`clampE`（第 5.1.5 节的截位）、`sign` / `verify`（第 5.1.6、5.1.7 节）。SHA-512 也写成规格（FIPS 180-4）。
用 #guard 对了：SHA-512 的两个向量；RFC 8032 第 7.1 节的 TEST 1、2、3、SHA(abc)（公钥、签名逐字节一样，验证通过，
改了消息或签名验证不过）；基点的编码。

证明了：
- `verify_len`：签名不是 64 字节时验证不过；
- `verify_big_s`：S ≥ L 时验证不过（第 5.1.7 节，防止同一个签名有多种写法，见第 8.4 节）；
- `decode_big_y`：y ≥ p（不是唯一的写法）时解码失败；
- `clamp_ok`：截位以后的标量是 8 的倍数，在 [2^254, 2^255) 里；
- `cv_inj`：TLS 1.3 CertificateVerify 签的内容能唯一拆回消息摘要（64 个空格 + 上下文 + 0 + 摘要）。
没有证明：签了再验一定通过（要椭圆曲线的群律，没有 Mathlib 证不动，只靠测试向量）；点的运算不按秘密分支（常数时间）。
-/
import Lark.Tls13

namespace Lark
namespace Ed25519
open Lark.Tls Lark.Tls13

/-! ## SHA-512（FIPS 180-4） -/

def rotr64 (x n : Nat) : Nat := ((x >>> n) ||| (x <<< (64 - n))) % 2 ^ 64
def ch64 (e f g : Nat) : Nat := (e &&& f) ^^^ ((e ^^^ (2 ^ 64 - 1)) &&& g)
def maj64 (a b c : Nat) : Nat := (a &&& b) ^^^ (a &&& c) ^^^ (b &&& c)
def S0 (a : Nat) : Nat := rotr64 a 28 ^^^ rotr64 a 34 ^^^ rotr64 a 39
def S1 (e : Nat) : Nat := rotr64 e 14 ^^^ rotr64 e 18 ^^^ rotr64 e 41
def s0 (x : Nat) : Nat := rotr64 x 1 ^^^ rotr64 x 8 ^^^ (x >>> 7)
def s1 (x : Nat) : Nat := rotr64 x 19 ^^^ rotr64 x 61 ^^^ (x >>> 6)

def K512 : List Nat :=
  [0x428a2f98d728ae22, 0x7137449123ef65cd, 0xb5c0fbcfec4d3b2f, 0xe9b5dba58189dbbc,
   0x3956c25bf348b538, 0x59f111f1b605d019, 0x923f82a4af194f9b, 0xab1c5ed5da6d8118,
   0xd807aa98a3030242, 0x12835b0145706fbe, 0x243185be4ee4b28c, 0x550c7dc3d5ffb4e2,
   0x72be5d74f27b896f, 0x80deb1fe3b1696b1, 0x9bdc06a725c71235, 0xc19bf174cf692694,
   0xe49b69c19ef14ad2, 0xefbe4786384f25e3, 0x0fc19dc68b8cd5b5, 0x240ca1cc77ac9c65,
   0x2de92c6f592b0275, 0x4a7484aa6ea6e483, 0x5cb0a9dcbd41fbd4, 0x76f988da831153b5,
   0x983e5152ee66dfab, 0xa831c66d2db43210, 0xb00327c898fb213f, 0xbf597fc7beef0ee4,
   0xc6e00bf33da88fc2, 0xd5a79147930aa725, 0x06ca6351e003826f, 0x142929670a0e6e70,
   0x27b70a8546d22ffc, 0x2e1b21385c26c926, 0x4d2c6dfc5ac42aed, 0x53380d139d95b3df,
   0x650a73548baf63de, 0x766a0abb3c77b2a8, 0x81c2c92e47edaee6, 0x92722c851482353b,
   0xa2bfe8a14cf10364, 0xa81a664bbc423001, 0xc24b8b70d0f89791, 0xc76c51a30654be30,
   0xd192e819d6ef5218, 0xd69906245565a910, 0xf40e35855771202a, 0x106aa07032bbd1b8,
   0x19a4c116b8d2d0c8, 0x1e376c085141ab53, 0x2748774cdf8eeb99, 0x34b0bcb5e19b48a8,
   0x391c0cb3c5c95a63, 0x4ed8aa4ae3418acb, 0x5b9cca4f7763e373, 0x682e6ff3d6b2b8a3,
   0x748f82ee5defb2fc, 0x78a5636f43172f60, 0x84c87814a1f0ab72, 0x8cc702081a6439ec,
   0x90befffa23631e28, 0xa4506cebde82bde9, 0xbef9a3f7b2c67915, 0xc67178f2e372532b,
   0xca273eceea26619c, 0xd186b8c721c0c207, 0xeada7dd6cde0eb1e, 0xf57d4f7fee6ed178,
   0x06f067aa72176fba, 0x0a637dc5a2c898a6, 0x113f9804bef90dae, 0x1b710b35131c471b,
   0x28db77f523047d84, 0x32caab7b40c72493, 0x3c9ebe0a15c9bebc, 0x431d67c49c100d4c,
   0x4cc5d4becb3e42b6, 0x597f299cfc657e2a, 0x5fcb6fab3ad6faec, 0x6c44198c4a475817]

def H512 : List Nat :=
  [0x6a09e667f3bcc908, 0xbb67ae8584caa73b, 0x3c6ef372fe94f82b, 0xa54ff53a5f1d36f1,
   0x510e527fade682d1, 0x9b05688c2b3e6c1f, 0x1f83d9abfb41bd6b, 0x5be0cd19137e2179]

def words64 : Nat → List Nat → List Nat
  | 0, _ => []
  | k + 1, d => unbe (d.take 8) :: words64 k (d.drop 8)

def sched64 : Nat → Array Nat → Array Nat
  | 0, w => w
  | k + 1, w =>
    let j := w.size
    sched64 k (w.push ((s1 w[j - 2]! + w[j - 7]! + s0 w[j - 15]! + w[j - 16]!) % 2 ^ 64))

def rnd64 (w : Array Nat) (s : List Nat) (i : Nat) : List Nat :=
  match s with
  | [a, b, c, d, e, f, g, h] =>
    let t1 := (h + S1 e + ch64 e f g + K512.getD i 0 + w[i]!) % 2 ^ 64
    let t2 := (S0 a + maj64 a b c) % 2 ^ 64
    [(t1 + t2) % 2 ^ 64, a, b, c, (d + t1) % 2 ^ 64, e, f, g]
  | _ => s

def comp64 (h blk : List Nat) : List Nat :=
  let w := sched64 64 (words64 16 blk).toArray
  List.zipWith (fun x y => (x + y) % 2 ^ 64) h ((List.range 80).foldl (rnd64 w) h)

def chunk128 : Nat → List Nat → List (List Nat)
  | 0, _ => []
  | _ + 1, [] => []
  | k + 1, d => d.take 128 :: chunk128 k (d.drop 128)

def pad512 (m : List Nat) : List Nat :=
  m ++ [0x80] ++ List.replicate ((239 - m.length % 128) % 128) 0 ++ be 16 (8 * m.length)

def ser64 : List Nat → List Nat
  | [] => []
  | w :: r => be 8 w ++ ser64 r

def sha512 (m : List Nat) : List Nat :=
  ser64 ((chunk128 (pad512 m).length (pad512 m)).foldl comp64 H512)

#guard sha512 [] == hx "cf83e1357eefb8bdf1542850d66d8007d620e4050b5715dc83f4a921d36ce9ce47d0d13c5d85f2b0ff8318d2877eec2f63b931bd47417a81a538327af927da3e"
#guard sha512 (ascii "abc") == hx "ddaf35a193617abacc417349ae20413112e6fa4e89a97ea20a9eeee64b55d39a2192992a274fc1a836ba3c23a3feebbd454d4423643ce80e2a9ac94fa54ca49f"

/-! ## 模 p 的运算和点（第 5.1.1 到 5.1.4 节） -/

def finv (a : Nat) : Nat := powMod a 256 (P25 - 2)
/-- d = -121665 / 121666 -/
def dC : Nat := fmul (P25 - 121665) (finv 121666)
/-- -1 的平方根 -/
def sqrtM1 : Nat := powMod 2 256 ((P25 - 1) / 4)

/-- 由 y 和 x 的最低位求 x（第 5.1.3 节）。y ≥ p、没有平方根、x = 0 但最低位要 1，都失败 -/
def recoverX (y sign : Nat) : Option Nat :=
  if P25 ≤ y then none
  else
    let x2 := fmul (fsub (fmul y y) 1) (finv (fadd (fmul dC (fmul y y)) 1))
    if x2 = 0 then (if sign = 1 then none else some 0)
    else
      let x0 := powMod x2 256 ((P25 + 3) / 8)
      let x1 := if fmul x0 x0 = x2 then x0 else fmul x0 sqrtM1
      if fmul x1 x1 = x2 then some (if x1 % 2 = sign then x1 else P25 - x1) else none

structure Pt where
  x : Nat
  y : Nat
  z : Nat
  t : Nat

def zeroPt : Pt := ⟨0, 1, 1, 0⟩

/-- 第 5.1.4 节的加法公式（对所有点都成立，加倍也用它） -/
def padd (P Q : Pt) : Pt :=
  let a := fmul (fsub P.y P.x) (fsub Q.y Q.x)
  let b := fmul (fadd P.y P.x) (fadd Q.y Q.x)
  let c := fmul (fmul (fmul P.t 2) dC) Q.t
  let dd := fmul (fmul P.z 2) Q.z
  let e := fsub b a
  let f := fsub dd c
  let g := fadd dd c
  let h := fadd b a
  ⟨fmul e f, fmul g h, fmul f g, fmul e h⟩

/-- [s]P：从低位起，这一位是 1 就加上，P 每次加倍（256 位） -/
def pmulF : Nat → Nat → Pt → Pt → Pt
  | 0, _, _, q => q
  | k + 1, s, p, q => pmulF k (s / 2) (padd p p) (if s % 2 = 1 then padd q p else q)

def pmul (s : Nat) (p : Pt) : Pt := pmulF 256 s p zeroPt

/-- 射影坐标下相等：x1 / z1 = x2 / z2 且 y1 / z1 = y2 / z2 -/
def peq (P Q : Pt) : Bool := fmul P.x Q.z == fmul Q.x P.z && fmul P.y Q.z == fmul Q.y P.z

def baseY : Nat := fmul 4 (finv 5)
def Bpt : Pt :=
  match recoverX baseY 0 with
  | some x => ⟨x, baseY, 1, fmul x baseY⟩
  | none => zeroPt

/-- 第 5.1.2 节：y 的 255 位，最高位放 x 的最低位 -/
def encodePt (P : Pt) : List Nat :=
  let zi := finv P.z
  enc 32 (fmul P.y zi + fmul P.x zi % 2 * 2 ^ 255)

def decodePt (s : List Nat) : Option Pt :=
  if s.length ≠ 32 then none
  else
    match recoverX (dec s % 2 ^ 255) (dec s / 2 ^ 255) with
    | some x => some ⟨x, dec s % 2 ^ 255, 1, fmul x (dec s % 2 ^ 255)⟩
    | none => none

/-! ## 签名和验证（第 5.1.5 到 5.1.7 节） -/

def Lq : Nat := 2 ^ 252 + 27742317777372353535851937790883648493

/-- 第 5.1.5 节：低 3 位清 0，第 255 位清 0，第 254 位置 1 -/
def clampE (x : Nat) : Nat := 2 ^ 254 + x % 2 ^ 254 / 8 * 8

def sha512q (m : List Nat) : Nat := dec (sha512 m) % Lq

def pubOf (sk : List Nat) : List Nat := encodePt (pmul (clampE (dec ((sha512 sk).take 32))) Bpt)

def sign (sk msg : List Nat) : List Nat :=
  let h := sha512 sk
  let a := clampE (dec (h.take 32))
  let A := encodePt (pmul a Bpt)
  let r := sha512q (h.drop 32 ++ msg)
  let R := encodePt (pmul r Bpt)
  let k := sha512q (R ++ A ++ msg)
  R ++ enc 32 ((r + k * a) % Lq)

theorem encodePt_len (P : Pt) : (encodePt P).length = 32 := enc_len 32 _

/-- 签名总是 64 字节（R 32 字节 + S 32 字节） -/
theorem sign_len (sk msg : List Nat) : (sign sk msg).length = 64 := by
  simp only [sign, List.length_append, encodePt_len, enc_len]

/-- 先查长度和 S < L，再解码 A、R，最后看 [S]B = R + [k]A -/
def verify (pk msg sig : List Nat) : Bool :=
  if sig.length ≠ 64 then false
  else if Lq ≤ dec (sig.drop 32) then false
  else
    match decodePt pk, decodePt (sig.take 32) with
    | some A, some R => peq (pmul (dec (sig.drop 32)) Bpt) (padd R (pmul (sha512q (sig.take 32 ++ pk ++ msg)) A))
    | _, _ => false

theorem verify_len (pk msg sig : List Nat) (h : sig.length ≠ 64) : verify pk msg sig = false := by
  unfold verify
  simp [h]

theorem verify_big_s (pk msg sig : List Nat) (h : Lq ≤ dec (sig.drop 32)) : verify pk msg sig = false := by
  unfold verify
  by_cases h1 : sig.length = 64
  · simp [h1, h]
  · simp [h1]

theorem recoverX_big (y sign : Nat) (h : P25 ≤ y) : recoverX y sign = none := by
  unfold recoverX
  simp [h]

theorem decode_big_y (s : List Nat) (h : P25 ≤ dec s % 2 ^ 255) : decodePt s = none := by
  unfold decodePt
  by_cases hl : s.length = 32
  · simp [hl, recoverX_big (dec s % 2 ^ 255) (dec s / 2 ^ 255) h]
  · simp [hl]

theorem clamp_ok (x : Nat) : clampE x % 8 = 0 ∧ 2 ^ 254 ≤ clampE x ∧ clampE x < 2 ^ 255 := by
  have h8 : 2 ^ 254 % 8 = 0 := by decide
  have h2 : (2 : Nat) ^ 255 = 2 * 2 ^ 254 := by decide
  have hp : 0 < (2 : Nat) ^ 254 := by decide
  unfold clampE
  rw [h2]
  have hm := Nat.mod_lt x hp
  generalize x % 2 ^ 254 = m at hm ⊢
  generalize (2 : Nat) ^ 254 = K at h8 hm ⊢
  refine ⟨by omega, by omega, by omega⟩

/-! ## TLS 1.3 的 CertificateVerify（RFC 8446 第 4.4.3 节）：签的是 64 个空格 + 上下文 + 0 + 消息摘要 -/

def cvContext : List Nat := List.replicate 64 32 ++ ascii "TLS 1.3, server CertificateVerify" ++ [0]
def cvContent (th : List Nat) : List Nat := cvContext ++ th

theorem cv_inj (a b : List Nat) (h : cvContent a = cvContent b) : a = b := by
  have e := congrArg (List.drop cvContext.length) h
  unfold cvContent at e
  rw [drop_app, drop_app] at e
  exact e

/-! ## 测试向量（RFC 8032 第 7.1 节） -/

-- 基点的编码是 58 66 66 …
#guard encodePt Bpt == hx "5866666666666666666666666666666666666666666666666666666666666666"

def sk1 : List Nat := hx "9d61b19deffd5a60ba844af492ec2cc44449c5697b326919703bac031cae7f60"
def pk1 : List Nat := hx "d75a980182b10ab7d54bfed3c964073a0ee172f3daa62325af021a68f707511a"
def sig1 : List Nat := hx "e5564300c360ac729086e2cc806e828a84877f1eb8e5d974d873e065224901555fb8821590a33bacc61e39701cf9b46bd25bf5f0595bbe24655141438e7a100b"
#guard pubOf sk1 == pk1
#guard sign sk1 [] == sig1
#guard verify pk1 [] sig1
#guard !verify pk1 [0] sig1
-- 同一个签名把 S 加上 L：数学上一样，但 S ≥ L，验证不过（verify_big_s）
#guard !verify pk1 [] (sig1.take 32 ++ enc 32 (dec (sig1.drop 32) + Lq))

def sk2 : List Nat := hx "4ccd089b28ff96da9db6c346ec114e0f5b8a319f35aba624da8cf6ed4fb8a6fb"
def pk2 : List Nat := hx "3d4017c3e843895a92b70aa74d1b7ebc9c982ccf2ec4968cc0cd55f12af4660c"
def sig2 : List Nat := hx "92a009a9f0d4cab8720e820b5f642540a2b27b5416503f8fb3762223ebdb69da085ac1e43e15996e458f3613d0f11d8c387b2eaeb4302aeeb00d291612bb0c00"
#guard pubOf sk2 == pk2
#guard sign sk2 [0x72] == sig2
#guard verify pk2 [0x72] sig2
#guard !verify pk1 [0x72] sig2

def sk3 : List Nat := hx "c5aa8df43f9f837bedb7442f31dcb7b166d38535076f094b85ce3a2e0b4458f7"
def pk3 : List Nat := hx "fc51cd8e6218a1a38da47ed00230f0580816ed13ba3303ac5deb911548908025"
def sig3 : List Nat := hx "6291d657deec24024827e69c3abe01a30ce548a284743a445e3680d7db5ac3ac18ff9b538d16f290ae67f760984dc6594a7c15e9716ed28dc027beceea1ec40a"
#guard pubOf sk3 == pk3
#guard sign sk3 [0xaf, 0x82] == sig3
#guard verify pk3 [0xaf, 0x82] sig3
#guard !verify pk3 [0xaf, 0x82] (sig3.set 5 ((sig3.getD 5 0 + 1) % 256))

def skA : List Nat := hx "833fe62409237b9d62ec77587520911e9a759cec1d19755b7da901b96dca3d42"
def pkA : List Nat := hx "ec172b93ad5e563bf4932c70e1245034c35467ef2efd4d64ebf819683467e2bf"
def sigA : List Nat := hx "dc2a4459e7369633a52b1bf277839a00201009a3efbf3ecb69bea2186c26b58909351fc9ac90b3ecfdfbc7c66431e0303dca179c138ac17ad9bef1177331a704"
#guard pubOf skA == pkA
#guard sign skA (sha512 (ascii "abc")) == sigA
#guard verify pkA (sha512 (ascii "abc")) sigA

-- 客户端和服务器的上下文不一样（服务器的签名不能拿去冒充客户端的）
#guard cvContext != List.replicate 64 32 ++ ascii "TLS 1.3, client CertificateVerify" ++ [0]
#guard cvContext.length == 98

end Ed25519
end Lark
