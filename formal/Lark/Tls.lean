/-
apps/ltls 的证明 · 阶段 1：加密原语（先证明，再照着改 apps/ltls/tls/*.lark）

字节串写成 List Nat（每个 < 256），32 / 64 位的字写成 Nat，模 2^32 或看成 64 位的位模式。

规格（照着 RFC 写，用 #guard 对 RFC 里的测试向量；和 apps/ltls/tests.lark 是同一批向量）：
- ChaCha20（RFC 8439 第 2.3、2.4 节）：`block`、`xorC`；
- Poly1305（第 2.5 节）：直接用模 2^130 - 5 的 Nat 算，`poly`；
- ChaCha20-Poly1305（第 2.8 节）：`sealA`、`openA`、`macData`；
- X25519（RFC 7748 第 5 节）：直接用模 2^255 - 19 的 Nat 算，`x25519`。

证明了：
- `dec_enc`：小端写成 n 字节再读回来不变（le32、le64、Poly1305 的 16 字节）；
- `xorC_xorC`：同一个密钥流异或两次回到原样，长度不变（加密和解密是同一个操作）；
- `open_seal`：任何密钥、nonce、明文、aad，seal 出来的再 open 回到明文；
- `open_some`：open 成功时，输入正好是 seal(明文) 的结果（接受的只有 seal 能算出来的东西）；
- `macData_inj`：(aad, 密文) 不同，交给 Poly1305 的数据就不同（补 0 加两个长度，能唯一拆回去）；
- `label_inj`：HKDF-Expand-Label 的 info 能唯一拆回 (长度, label, context)，不同用途的密钥 info 不会撞上；
- `expand_len`：HKDF-Expand 输出正好 n 字节（HMAC 输出 32 字节时）；n ≤ 8160 时块计数 ≤ 255，放得进 1 个字节；
- `sel_keep` / `sel_swap`：Poly1305 最后“减不减 p”的掩码选择，`cswap_zero` / `cswap_one`：X25519 的掩码交换；
- `ladder_swap`：X25519 代码里“每步前后都按这一位交换”（TweetNaCl 的写法）和 RFC 7748 里
  “按相邻两位的异或交换、最后再换一次”结果一样（对任何一步的运算都成立）；
- `inv_ok`：代码里求逆的平方-乘序列（k = 253..0，k 是 2 和 4 时只平方）算的正好是 a^(p-2) mod p；
- `clamp_ok`：私钥按第 5 节截掉一些位以后，标量是 8 的倍数，并且在 [2^254, 2^255) 里。

没有证明的（只靠测试向量）：Poly1305 的 26 位分段乘法和进位、X25519 的 16 段乘法和进位与 Nat 规格一致；
a^(p-2) 是逆（要 p 是素数，没有 Mathlib 证不动）；HMAC-SHA256 本身（见 Digest.lean）；常数时间。
-/

namespace Lark
namespace Tls

/-! ## 小端编码 -/

/-- x 的低 n 字节，小端 -/
def enc : Nat → Nat → List Nat
  | 0, _ => []
  | n + 1, x => x % 256 :: enc n (x / 256)

/-- 小端读回来 -/
def dec : List Nat → Nat
  | [] => 0
  | b :: r => b + 256 * dec r

theorem enc_len : ∀ (n x : Nat), (enc n x).length = n
  | 0, _ => rfl
  | n + 1, x => by simp only [enc, List.length_cons, enc_len n (x / 256)]

theorem dec_enc : ∀ (n x : Nat), x < 256 ^ n → dec (enc n x) = x
  | 0, x, h => by simp at h; subst h; rfl
  | n + 1, x, h => by
    have h' : x / 256 < 256 ^ n := by
      rw [Nat.pow_succ] at h
      exact Nat.div_lt_of_lt_mul (by rwa [Nat.mul_comm] at h)
    show x % 256 + 256 * dec (enc n (x / 256)) = x
    rw [dec_enc n (x / 256) h']
    omega

theorem dec_lt : ∀ l : List Nat, (∀ b ∈ l, b < 256) → dec l < 256 ^ l.length
  | [], _ => by simp [dec]
  | b :: l, h => by
    have h1 : b < 256 := h b (by simp)
    have h2 := dec_lt l (fun x hx => h x (by simp [hx]))
    show b + 256 * dec l < 256 ^ (l.length + 1)
    rw [Nat.pow_succ]
    omega

theorem dec_append : ∀ (l : List Nat) (t : Nat), dec (l ++ [t]) = dec l + t * 256 ^ l.length
  | [], t => by simp [dec]
  | b :: l, t => by
    show b + 256 * dec (l ++ [t]) = b + 256 * dec l + t * 256 ^ (l.length + 1)
    rw [dec_append l t, Nat.pow_succ, Nat.mul_add]
    have e : 256 * (t * 256 ^ l.length) = t * (256 ^ l.length * 256) := by
      rw [Nat.mul_comm (256 ^ l.length) 256, Nat.mul_left_comm]
    rw [e, Nat.add_assoc]

/-! ## 列表拼接以后取前面、去掉前面 -/

theorem take_app {α : Type} : ∀ (l₁ l₂ : List α), (l₁ ++ l₂).take l₁.length = l₁
  | [], _ => by simp
  | a :: l₁, l₂ => congrArg (a :: ·) (take_app l₁ l₂)

theorem drop_app {α : Type} : ∀ (l₁ l₂ : List α), (l₁ ++ l₂).drop l₁.length = l₂
  | [], _ => rfl
  | _ :: l₁, l₂ => drop_app l₁ l₂

/-! ## ChaCha20（第 2.3、2.4 节） -/

def add32 (a b : Nat) : Nat := (a + b) % 2 ^ 32
def rotl (x n : Nat) : Nat := ((x <<< n) ||| (x >>> (32 - n))) % 2 ^ 32

/-- 第 2.1 节的四分之一轮，和 chacha20.lark 的 qr 一行对一行 -/
def qr (s : List Nat) (a b c d : Nat) : List Nat :=
  let s := s.set a (add32 (s.getD a 0) (s.getD b 0))
  let s := s.set d (rotl (s.getD d 0 ^^^ s.getD a 0) 16)
  let s := s.set c (add32 (s.getD c 0) (s.getD d 0))
  let s := s.set b (rotl (s.getD b 0 ^^^ s.getD c 0) 12)
  let s := s.set a (add32 (s.getD a 0) (s.getD b 0))
  let s := s.set d (rotl (s.getD d 0 ^^^ s.getD a 0) 8)
  let s := s.set c (add32 (s.getD c 0) (s.getD d 0))
  s.set b (rotl (s.getD b 0 ^^^ s.getD c 0) 7)

def dround (s : List Nat) : List Nat :=
  qr (qr (qr (qr (qr (qr (qr (qr s 0 4 8 12) 1 5 9 13) 2 6 10 14) 3 7 11 15) 0 5 10 15) 1 6 11 12) 2 7 8 13) 3 4 9 14

def rounds : Nat → List Nat → List Nat
  | 0, s => s
  | k + 1, s => rounds k (dround s)

/-- 每 4 字节小端读成一个字 -/
def wordsOf : Nat → List Nat → List Nat
  | 0, _ => []
  | k + 1, d => dec (d.take 4) :: wordsOf k (d.drop 4)

def ser : List Nat → List Nat
  | [] => []
  | w :: r => enc 4 w ++ ser r

def init (key : List Nat) (ctr : Nat) (nonce : List Nat) : List Nat :=
  [0x61707865, 0x3320646e, 0x79622d32, 0x6b206574] ++ wordsOf 8 key ++ [ctr % 2 ^ 32] ++ wordsOf 3 nonce

/-- 第 ctr 块的 64 字节密钥流 -/
def block (key : List Nat) (ctr : Nat) (nonce : List Nat) : List Nat :=
  ser (List.zipWith add32 (rounds 10 (init key ctr nonce)) (init key ctr nonce))

/-- 从第 c 块起的 k 块密钥流 -/
def blocks (key nonce : List Nat) : Nat → Nat → List Nat
  | 0, _ => []
  | k + 1, c => block key c nonce ++ blocks key nonce k (c + 1)

/-- 逐字节异或；密钥流不够长时剩下的不变（实际上总是够长：m.length / 64 + 1 块） -/
def xorP : List Nat → List Nat → List Nat
  | [], _ => []
  | b :: m, [] => b :: xorP m []
  | b :: m, k :: ks => (b ^^^ k) :: xorP m ks

/-- chacha20.xor(key, c, nonce, m) -/
def xorC (key : List Nat) (c : Nat) (nonce m : List Nat) : List Nat :=
  xorP m (blocks key nonce (m.length / 64 + 1) c)

theorem xorP_length : ∀ (m ks : List Nat), (xorP m ks).length = m.length
  | [], _ => rfl
  | _ :: m, [] => by simp only [xorP, List.length_cons, xorP_length m []]
  | _ :: m, _ :: ks => by simp only [xorP, List.length_cons, xorP_length m ks]

theorem xorP_xorP : ∀ (m ks : List Nat), xorP (xorP m ks) ks = m
  | [], _ => rfl
  | _ :: m, [] => by simp only [xorP, xorP_xorP m []]
  | _ :: m, _ :: ks => by simp only [xorP, Nat.xor_assoc, Nat.xor_self, Nat.xor_zero, xorP_xorP m ks]

/-- 加密和解密是同一个操作；长度不变 -/
theorem xorC_xorC (key : List Nat) (c : Nat) (nonce m : List Nat) : xorC key c nonce (xorC key c nonce m) = m := by
  unfold xorC
  rw [xorP_length]
  exact xorP_xorP _ _

theorem xorC_length (key : List Nat) (c : Nat) (nonce m : List Nat) : (xorC key c nonce m).length = m.length :=
  xorP_length _ _

/-! ## Poly1305（第 2.5 节） -/

def P1305 : Nat := 2 ^ 130 - 5
def clampR : Nat := 0x0ffffffc0ffffffc0ffffffc0fffffff

/-- 每 16 字节一块，最后一块可以不满 -/
def chunks : Nat → List Nat → List (List Nat)
  | _, [] => []
  | 0, _ => []
  | k + 1, d => d.take 16 :: chunks k (d.drop 16)

/-- 一块：加上 块的值 + 2^(8 × 块长)（就是在块后面补一个 1），再乘 r，模 p -/
def polyAcc (r acc : Nat) (c : List Nat) : Nat := (acc + dec c + 2 ^ (8 * c.length)) * r % P1305

def poly (key msg : List Nat) : List Nat :=
  enc 16 (((chunks msg.length msg).foldl (polyAcc (dec (key.take 16) &&& clampR)) 0 + dec (key.drop 16)) % 2 ^ 128)

theorem poly_len (key msg : List Nat) : (poly key msg).length = 16 := enc_len 16 _

/-! ## ChaCha20-Poly1305（第 2.8 节） -/

def pad (m : Nat) : List Nat := List.replicate ((16 - m % 16) % 16) 0

/-- aad、补 0、密文、补 0、两个长度（各 8 字节小端） -/
def macData (a c : List Nat) : List Nat :=
  a ++ pad a.length ++ c ++ pad c.length ++ (enc 8 a.length ++ enc 8 c.length)

/-- 一次性的 Poly1305 密钥：第 0 块的前 32 字节 -/
def otk (key nonce : List Nat) : List Nat := (block key 0 nonce).take 32

def sealA (key nonce p a : List Nat) : List Nat :=
  xorC key 1 nonce p ++ poly (otk key nonce) (macData a (xorC key 1 nonce p))

def ctOf (d : List Nat) : List Nat := d.take (d.length - 16)
def tagOf (d : List Nat) : List Nat := d.drop (d.length - 16)

def openA (key nonce d a : List Nat) : Option (List Nat) :=
  if d.length < 16 then none
  else if poly (otk key nonce) (macData a (ctOf d)) = tagOf d then some (xorC key 1 nonce (ctOf d))
  else none

theorem open_app (key nonce c t a : List Nat) (ht : t.length = 16) :
    openA key nonce (c ++ t) a =
      if poly (otk key nonce) (macData a c) = t then some (xorC key 1 nonce c) else none := by
  have h1 : ¬(c ++ t).length < 16 := by simp only [List.length_append, ht]; omega
  have h2 : (c ++ t).length - 16 = c.length := by simp only [List.length_append, ht]; omega
  have hc : ctOf (c ++ t) = c := by unfold ctOf; rw [h2]; exact take_app c t
  have hg : tagOf (c ++ t) = t := by unfold tagOf; rw [h2]; exact drop_app c t
  unfold openA
  rw [ite_eq_right h1, hc, hg]

/-- seal 出来的再 open 回到明文 -/
theorem open_seal (key nonce p a : List Nat) : openA key nonce (sealA key nonce p a) a = some p := by
  unfold sealA
  rw [open_app _ _ _ _ _ (poly_len _ _), ite_eq_left rfl, xorC_xorC]

/-- open 成功时，输入正好是 seal(明文) -/
theorem open_some (key nonce d a p : List Nat) (h : openA key nonce d a = some p) : d = sealA key nonce p a := by
  unfold openA at h
  split at h
  · cases h
  · split at h
    · rename_i ht
      cases h
      unfold sealA
      rw [xorC_xorC, ht]
      simp only [ctOf, tagOf, List.take_append_drop]
    · cases h

/-! ### 交给 Poly1305 的数据能唯一拆回 (aad, 密文) -/

def tl16 (d : List Nat) : List Nat := d.drop (d.length - 16)
def lenA (d : List Nat) : Nat := dec ((tl16 d).take 8)
def lenC (d : List Nat) : Nat := dec ((tl16 d).drop 8)

def parseMac (d : List Nat) : List Nat × List Nat :=
  (d.take (lenA d), (d.drop (lenA d + (16 - lenA d % 16) % 16)).take (lenC d))

theorem parse_mac (a c : List Nat) (ha : a.length < 2 ^ 64) (hc : c.length < 2 ^ 64) :
    parseMac (macData a c) = (a, c) := by
  have e64 : (256 : Nat) ^ 8 = 2 ^ 64 := by decide
  have e1 : (macData a c).length - 16 = (a ++ pad a.length ++ c ++ pad c.length).length := by
    simp only [macData, List.length_append, enc_len]
    omega
  have e2 : tl16 (macData a c) = enc 8 a.length ++ enc 8 c.length := by
    unfold tl16
    rw [e1]
    exact drop_app (a ++ pad a.length ++ c ++ pad c.length) _
  have t1 : (enc 8 a.length ++ enc 8 c.length).take 8 = enc 8 a.length := by
    have := take_app (enc 8 a.length) (enc 8 c.length)
    rwa [enc_len] at this
  have t2 : (enc 8 a.length ++ enc 8 c.length).drop 8 = enc 8 c.length := by
    have := drop_app (enc 8 a.length) (enc 8 c.length)
    rwa [enc_len] at this
  have hA : lenA (macData a c) = a.length := by
    unfold lenA
    rw [e2, t1]
    exact dec_enc 8 _ (by rw [e64]; exact ha)
  have hC : lenC (macData a c) = c.length := by
    unfold lenC
    rw [e2, t2]
    exact dec_enc 8 _ (by rw [e64]; exact hc)
  have f1 : (macData a c).take a.length = a := by
    show (a ++ pad a.length ++ c ++ pad c.length ++ (enc 8 a.length ++ enc 8 c.length)).take a.length = a
    simp only [List.append_assoc]
    exact take_app _ _
  have f2 : ((macData a c).drop (a.length + (16 - a.length % 16) % 16)).take c.length = c := by
    have hp : a.length + (16 - a.length % 16) % 16 = (a ++ pad a.length).length := by
      simp [pad]
    have hre : macData a c = (a ++ pad a.length) ++ (c ++ (pad c.length ++ (enc 8 a.length ++ enc 8 c.length))) := by
      simp only [macData, List.append_assoc]
    rw [hp, hre, drop_app]
    exact take_app _ _
  unfold parseMac
  rw [hA, hC, f1, f2]

/-- (aad, 密文) 不同，交给 Poly1305 的数据就不同 -/
theorem macData_inj (a c a' c' : List Nat) (ha : a.length < 2 ^ 64) (hc : c.length < 2 ^ 64)
    (ha' : a'.length < 2 ^ 64) (hc' : c'.length < 2 ^ 64) (h : macData a c = macData a' c') : a = a' ∧ c = c' := by
  have := congrArg parseMac h
  rw [parse_mac a c ha hc, parse_mac a' c' ha' hc'] at this
  simp only [Prod.mk.injEq] at this
  exact this

/-! ## HKDF（RFC 5869）和 HKDF-Expand-Label（RFC 8446 第 7.1 节） -/

/-- T(i) = HMAC(prk, T(i-1) ++ info ++ [i])，k 块拼起来；H 是 HMAC-SHA256 -/
def expT (H : List Nat → List Nat → List Nat) (prk info : List Nat) : Nat → List Nat → Nat → List Nat
  | 0, _, _ => []
  | k + 1, t, i => H prk (t ++ info ++ [i]) ++ expT H prk info k (H prk (t ++ info ++ [i])) (i + 1)

/-- hkdf.expand：计数 1..(n + 31) / 32，取前 n 字节 -/
def expand (H : List Nat → List Nat → List Nat) (prk info : List Nat) (n : Nat) : List Nat :=
  (expT H prk info ((n + 31) / 32) [] 1).take n

theorem expT_len (H : List Nat → List Nat → List Nat) (hH : ∀ k m, (H k m).length = 32) (prk info : List Nat) :
    ∀ (k : Nat) (t : List Nat) (i : Nat), (expT H prk info k t i).length = 32 * k
  | 0, _, _ => rfl
  | k + 1, t, i => by
    simp only [expT, List.length_append, hH, expT_len H hH prk info k]
    omega

theorem expand_len (H : List Nat → List Nat → List Nat) (hH : ∀ k m, (H k m).length = 32) (prk info : List Nat)
    (n : Nat) : (expand H prk info n).length = n := by
  simp only [expand, List.length_take, expT_len H hH]
  omega

/-- n ≤ 8160 时块计数（1..(n + 31) / 32）放得进 1 个字节 -/
theorem expand_ctr (n : Nat) (h : n ≤ 255 * 32) : (n + 31) / 32 ≤ 255 := by omega

def tls13 : List Nat := [116, 108, 115, 49, 51, 32]   -- "tls13 "

/-- HkdfLabel：长度（2 字节大端）、"tls13 " + label（前面 1 字节长度）、context（前面 1 字节长度） -/
def labelInfo (n : Nat) (l c : List Nat) : List Nat :=
  [n / 256, n % 256, l.length + 6] ++ (tls13 ++ l) ++ ([c.length] ++ c)

def parseLabel : List Nat → Nat × List Nat × List Nat
  | h :: lo :: k :: r => (h * 256 + lo, (r.take k).drop 6, (r.drop k).drop 1)
  | _ => (0, [], [])

theorem parse_label (n : Nat) (l c : List Nat) : parseLabel (labelInfo n l c) = (n, l, c) := by
  show parseLabel ((n / 256) :: (n % 256) :: (l.length + 6) :: ((tls13 ++ l) ++ ([c.length] ++ c))) = (n, l, c)
  have hl : (tls13 ++ l).length = l.length + 6 := by
    simp only [List.length_append, tls13, List.length_cons, List.length_nil]
    omega
  have h6 : (tls13 ++ l).drop 6 = l := drop_app tls13 l
  have h1 : ([c.length] ++ c).drop 1 = c := rfl
  simp only [parseLabel]
  rw [← hl, take_app, drop_app, h6, h1, show n / 256 * 256 + n % 256 = n by omega]

/-- 长度、label、context 有一个不同，info 就不同。代码里每个长度占 1 个字节，所以要
    n < 65536、label 不超过 249 字节、context 不超过 255 字节（hkdf.expand_label 检查了，超了 panic） -/
theorem label_inj (n n' : Nat) (l c l' c' : List Nat) (h : labelInfo n l c = labelInfo n' l' c') :
    n = n' ∧ l = l' ∧ c = c' := by
  have := congrArg parseLabel h
  rw [parse_label, parse_label] at this
  simp only [Prod.mk.injEq] at this
  exact this

/-! ## 掩码选择和交换（不按秘密数据分支） -/

def M64 : Nat := 2 ^ 64 - 1

/-- poly1305.lark：h = (h & keep) | (g & !keep)，keep 是全 1 或全 0（!keep 在 64 位里是 keep ^ M64） -/
def sel (keep a b : Nat) : Nat := (a &&& keep) ||| (b &&& (keep ^^^ M64))

theorem sel_keep (a b : Nat) (ha : a < 2 ^ 64) : sel M64 a b = a := by
  unfold sel
  rw [Nat.xor_self, Nat.and_zero, Nat.or_zero]
  unfold M64
  rw [Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt ha]

theorem sel_swap (a b : Nat) (hb : b < 2 ^ 64) : sel 0 a b = b := by
  unfold sel
  rw [Nat.and_zero, Nat.zero_xor, Nat.zero_or]
  unfold M64
  rw [Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt hb]

/-- x25519.lark 的 cswap：m = -b（b 是 1 时全 1，是 0 时全 0），t = m & (p ^ q)，p ^= t，q ^= t -/
def cswapM (m a b : Nat) : Nat × Nat := (a ^^^ (m &&& (a ^^^ b)), b ^^^ (m &&& (a ^^^ b)))

theorem cswap_zero (a b : Nat) : cswapM 0 a b = (a, b) := by
  simp only [cswapM, Nat.zero_and, Nat.xor_zero]

theorem cswap_one (a b : Nat) (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) : cswapM M64 a b = (b, a) := by
  have hx : M64 &&& (a ^^^ b) = a ^^^ b := by
    rw [Nat.and_comm]
    unfold M64
    rw [Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt (Nat.xor_lt_two_pow ha hb)]
  simp only [cswapM, hx]
  rw [← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor, Nat.xor_comm a b, ← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor]

/-! ## X25519 的蒙哥马利阶梯：两种交换的写法一样 -/

/-- b 是 true 时交换一对 -/
def cs {α : Type} (b : Bool) (s : α × α) : α × α := if b then (s.2, s.1) else s

theorem cs_cs {α : Type} (b : Bool) (s : α × α) : cs b (cs b s) = s := by
  cases b <;> rfl

theorem cs_xor {α : Type} (a b : Bool) (s : α × α) : cs (a != b) (cs a s) = cs b s := by
  cases a <;> cases b <;> rfl

/-- RFC 7748：swap ^= k_t；按 swap 交换；swap = k_t；走一步。全部走完再按 swap 交换一次 -/
def rfcLoop {α : Type} (step : α × α → α × α) : List Bool → Bool → α × α → α × α
  | [], sw, s => cs sw s
  | k :: ks, sw, s => rfcLoop step ks k (step (cs (sw != k) s))

/-- x25519.lark（TweetNaCl）：每一步前后都按这一位交换 -/
def tnLoop {α : Type} (step : α × α → α × α) : List Bool → α × α → α × α
  | [], s => s
  | k :: ks, s => tnLoop step ks (cs k (step (cs k s)))

theorem rfc_tn {α : Type} (step : α × α → α × α) :
    ∀ (ks : List Bool) (sw : Bool) (s : α × α), rfcLoop step ks sw (cs sw s) = tnLoop step ks s
  | [], sw, s => cs_cs sw s
  | k :: ks, sw, s => by
    have ih := rfc_tn step ks k (cs k (step (cs k s)))
    rw [cs_cs] at ih
    show rfcLoop step ks k (step (cs (sw != k) (cs sw s))) = tnLoop step ks (cs k (step (cs k s)))
    rw [cs_xor]
    exact ih

/-- 对任何一步的运算，两种写法结果一样 -/
theorem ladder_swap {α : Type} (step : α × α → α × α) (ks : List Bool) (s : α × α) :
    rfcLoop step ks false s = tnLoop step ks s :=
  rfc_tn step ks false s

/-! ## X25519 的求逆：平方-乘的序列 -/

def P25 : Nat := 2 ^ 255 - 19

/-- x25519.lark 的 inv：c 从 a 开始，k = 253..0 每次平方，k 不是 2、4 时再乘 a -/
def invF : List Nat → Nat → Nat → Nat
  | [], _, c => c
  | k :: ks, a, c => invF ks a (if k = 2 ∨ k = 4 then c * c % P25 else c * c * a % P25)

/-- 同一个序列对应的指数 -/
def invE : List Nat → Nat → Nat
  | [], e => e
  | k :: ks, e => invE ks (if k = 2 ∨ k = 4 then 2 * e else 2 * e + 1)

theorem sq_mod (x : Nat) : x % P25 * (x % P25) % P25 = x * x % P25 := (Nat.mul_mod x x P25).symm

theorem sqm_mod (x a : Nat) : x % P25 * (x % P25) * a % P25 = x * x * a % P25 := by
  rw [Nat.mul_mod (x % P25 * (x % P25)) a P25, ← Nat.mul_mod x x P25, ← Nat.mul_mod (x * x) a P25]

theorem invF_pow : ∀ (ks : List Nat) (a e : Nat), invF ks a (a ^ e % P25) = a ^ invE ks e % P25
  | [], _, _ => rfl
  | k :: ks, a, e => by
    simp only [invF, invE]
    by_cases h : k = 2 ∨ k = 4
    · simp only [h, ↓reduceIte]
      rw [← invF_pow ks a (2 * e), sq_mod, Nat.two_mul, Nat.pow_add]
    · simp only [h, ↓reduceIte]
      rw [← invF_pow ks a (2 * e + 1), sqm_mod, Nat.pow_succ, Nat.two_mul, Nat.pow_add]

def invKs : List Nat := (List.range 254).reverse   -- 253, 252, …, 0

set_option maxRecDepth 100000 in
theorem invE_ok : invE invKs 1 = P25 - 2 := by decide

/-- 代码里的求逆算的是 a^(p-2) mod p -/
theorem inv_ok (a : Nat) : invF invKs a (a % P25) = a ^ (P25 - 2) % P25 := by
  have := invF_pow invKs a 1
  rw [Nat.pow_one, invE_ok] at this
  exact this

/-! ## X25519 的私钥截位（第 5 节） -/

/-- k[0] &= 248；k[31] = (k[31] & 127) | 64 -/
def clamp : List Nat → List Nat
  | x :: r => (x &&& 248) :: (r.take 30 ++ [r.getD 30 0 &&& 127 ||| 64])
  | [] => []

set_option maxRecDepth 100000 in
theorem low3 : ∀ b, b < 256 → (b &&& 248) % 8 = 0 := by decide

set_option maxRecDepth 100000 in
theorem top : ∀ y, y < 128 → 64 ≤ (y ||| 64) ∧ (y ||| 64) < 128 := by decide

/-- 标量是 8 的倍数（消掉小阶的部分），最高的一位是第 254 位 -/
theorem clamp_ok (k : List Nat) (hk : k.length = 32) (hb : ∀ b ∈ k, b < 256) :
    dec (clamp k) % 8 = 0 ∧ 2 ^ 254 ≤ dec (clamp k) ∧ dec (clamp k) < 2 ^ 255 := by
  cases k with
  | nil => simp at hk
  | cons x r =>
    have hr : r.length = 31 := by simp only [List.length_cons] at hk; omega
    have hx : x &&& 248 < 256 := Nat.and_lt_two_pow _ (n := 8) (by decide)
    have h0 := low3 x (hb x (by simp))
    have hmid : (r.take 30).length = 30 := by simp [hr]
    have hd := dec_lt (r.take 30) (fun b h => hb b (List.mem_cons_of_mem _ (List.mem_of_mem_take h)))
    rw [hmid] at hd
    have hy : r.getD 30 0 &&& 127 < 128 := Nat.and_lt_two_pow _ (n := 7) (by decide)
    have ht := top _ hy
    have e : dec (clamp (x :: r)) =
        (x &&& 248) + 256 * (dec (r.take 30) + (r.getD 30 0 &&& 127 ||| 64) * 256 ^ 30) := by
      show (x &&& 248) + 256 * dec (r.take 30 ++ [r.getD 30 0 &&& 127 ||| 64]) = _
      rw [dec_append, hmid]
    have e254 : (2 : Nat) ^ 254 = 16384 * 256 ^ 30 := by decide
    have e255 : (2 : Nat) ^ 255 = 32768 * 256 ^ 30 := by decide
    rw [e, e254, e255]
    generalize dec (r.take 30) = D at hd ⊢
    generalize (r.getD 30 0 &&& 127 ||| 64) = t at ht ⊢
    generalize x &&& 248 = x' at hx h0 ⊢
    generalize (256 : Nat) ^ 30 = X at hd ⊢
    have h1 : 64 * X ≤ t * X := Nat.mul_le_mul_right _ ht.1
    have h2 : (t + 1) * X ≤ 128 * X := Nat.mul_le_mul_right _ ht.2
    rw [Nat.add_mul, Nat.one_mul] at h2
    generalize t * X = tX at h1 h2 ⊢
    refine ⟨by omega, by omega, by omega⟩

/-! ## X25519 的规格（第 5 节），模 p 直接算 -/

def fadd (a b : Nat) : Nat := (a + b) % P25
def fsub (a b : Nat) : Nat := (a + P25 - b) % P25
def fmul (a b : Nat) : Nat := a * b % P25

/-- 第 5 节阶梯里的一步：((x_2, z_2), (x_3, z_3)) → 新的两对 -/
def ladStep (x1 : Nat) : (Nat × Nat) × (Nat × Nat) → (Nat × Nat) × (Nat × Nat)
  | ((x2, z2), (x3, z3)) =>
    let A := fadd x2 z2
    let AA := fmul A A
    let B := fsub x2 z2
    let BB := fmul B B
    let E := fsub AA BB
    let C := fadd x3 z3
    let D := fsub x3 z3
    let DA := fmul D A
    let CB := fmul C B
    ((fmul AA BB, fmul E (fadd AA (fmul 121665 E))),
     (fmul (fadd DA CB) (fadd DA CB), fmul x1 (fmul (fsub DA CB) (fsub DA CB))))

def powMod (b : Nat) : Nat → Nat → Nat
  | 0, _ => 1
  | f + 1, e =>
    if e = 0 then 1
    else
      let h := powMod b f (e / 2)
      if e % 2 = 1 then h * h % P25 * b % P25 else h * h % P25

/-- 标量的第 254 位到第 0 位 -/
def kbits (k : Nat) : List Bool := (List.range 255).reverse.map (fun i => k.testBit i)

def x25519 (kb ub : List Nat) : List Nat :=
  let u := dec ub % 2 ^ 255 % P25
  match rfcLoop (ladStep u) (kbits (dec (clamp kb))) false ((1, 0), (u, 1)) with
  | ((x2, z2), _) => enc 32 (fmul x2 (powMod z2 256 (P25 - 2)))

/-! ## 测试向量（和 apps/ltls/tests.lark 一样） -/

def hv (c : Char) : Nat := if c.isDigit then c.toNat - 48 else c.toNat - 87

def hxL : List Char → List Nat
  | a :: b :: r => (hv a * 16 + hv b) :: hxL r
  | _ => []

def hx (s : String) : List Nat := hxL s.toList
def ascii (s : String) : List Nat := s.toList.map Char.toNat
def seqB (a n : Nat) : List Nat := (List.range n).map (· + a)

def sunscreen : List Nat :=
  ascii "Ladies and Gentlemen of the class of '99: If I could offer you only one tip for the future, sunscreen would be it."

-- RFC 8439 第 2.3.2 节
#guard block (seqB 0 32) 1 (hx "000000090000004a00000000") ==
  hx "10f1e7e4d13b5915500fdd1fa32071c4c7d1f4c733c068030422aa9ac3d46c4ed2826446079faa0914c2d705d98b02a2b5129cd1de164eb9cbd083e8a2503c4e"
-- 第 2.4.2 节
#guard xorC (seqB 0 32) 1 (hx "000000000000004a00000000") sunscreen ==
  hx "6e2e359a2568f98041ba0728dd0d6981e97e7aec1d4360c20a27afccfd9fae0bf91b65c5524733ab8f593dabcd62b3571639d624e65152ab8f530c359f0861d807ca0dbf500d6a6156a38e088a22b65e52bc514d16ccf806818ce91ab77937365af90bbf74a35be6b40b8eedf2785e42874d"
-- 第 2.5.2 节
#guard poly (hx "85d6be7857556d337f4452fe42d506a80103808afb0db2fd4abff6af4149f51b") (ascii "Cryptographic Forum Research Group") ==
  hx "a8061dc1305136c6c22b8baf0c0127a9"
-- 第 2.8.2 节
#guard sealA (seqB 0x80 32) (hx "070000004041424344454647") sunscreen (hx "50515253c0c1c2c3c4c5c6c7") ==
  hx ("d31a8d34648e60db7b86afbc53ef7ec2a4aded51296e08fea9e2b5a736ee62d63dbea45e8ca9671282fafb69da92728b1a71de0a9e060b2905d6a5b67ecd3b3692ddbd7f2d778b8c9803aee328091b58fab324e4fad675945585808b4831d7bc3ff4def08e4b7a9de576d26586cec64b6116" ++
      "1ae10b594f09e26a7e902ecbd0600691")
#guard openA (seqB 0x80 32) (hx "070000004041424344454647")
  (sealA (seqB 0x80 32) (hx "070000004041424344454647") sunscreen (hx "50515253c0c1c2c3c4c5c6c7")) [] == none

-- RFC 7748 第 5.2 节（第二个的 u 最高位是 1）
#guard x25519 (hx "a546e36bf0527c9d3b16154b82465edd62144c0ac1fc5a18506a2244ba449ac4")
  (hx "e6db6867583030db3594c1a424b15f7c726624ec26b3353b10a903a6d0ab1c4c") ==
  hx "c3da55379de9c6908e94ea4df28d084f32eccf03491c71f754b4075577a28552"
#guard x25519 (hx "4b66e9d4d1b4673c5ad22691957d6af5c11b6421e0ea01d42ca4169e7918ba0d")
  (hx "e5210f12786811d3f4b7959d0538ae2c31dbe7106fc03c3efc4cd549c715a493") ==
  hx "95cbde9476e8907d7aade45cb4b873f88b595a68799fa152e6f8f7647aac7957"
-- 第 6.1 节：Alice 的公钥、Bob 的公钥、共享的密钥
#guard x25519 (hx "77076d0a7318a57d3c16c17251b26645df4c2f87ebc0992ab177fba51db92c2a") (9 :: List.replicate 31 0) ==
  hx "8520f0098930a754748b7ddcb43ef75a0dbf3a0d26381af4eba4a98eaa9b4e6a"
#guard x25519 (hx "5dab087e624a8a4b79e17f8b83800ee66f3bb1292618b6fd1c2f8b27ff88e0eb")
  (hx "8520f0098930a754748b7ddcb43ef75a0dbf3a0d26381af4eba4a98eaa9b4e6a") ==
  hx "4a5d9d5ba4ce2de1728e3bf480350f25e07e21c947d19e3376f09b3c1e161742"
-- 代码里的求逆和 a^(p-2) 一样（inv_ok 证明了，这里再算一个）
#guard invF invKs 12345 12345 == powMod 12345 256 (P25 - 2)

end Tls
end Lark
