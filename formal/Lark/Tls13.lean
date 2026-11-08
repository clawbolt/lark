/-
apps/ltls 的证明 · 阶段 2：记录层、握手消息的格式、密钥计算、客户端的握手状态机（先证明，再写 apps/ltls/tls/*.lark）

字节串还是 List Nat（每个 < 256）。加密原语用阶段 1 的规格（Tls.lean）。

规格：
- 带长度前缀的格式（`frame k`：k 字节大端长度 + 内容）：记录（RFC 8446 第 5.1 节）、握手消息（第 4 节）、扩展里的各种向量都是它；
- 记录（`recWrite` / `recParse`）、内层明文（`inner` / `unpad`，第 5.2、5.4 节）、每条记录的 nonce（`nonce`，第 5.3 节）、
  加密的记录（`protect` / `unprotect`，用 ChaCha20-Poly1305，即 TLS_CHACHA20_POLY1305_SHA256）；
- SHA-256 和 HMAC-SHA256（`sha256` / `hmac`，只用来对 RFC 8448 的值；std/digest 的实现见 tests/unit/digest）；
- 密钥计算（第 7.1 节）：`extract`、`expandLabel`、`deriveH`、`finishedMac`，用 `#guard` 逐个对 RFC 8448 第 3 节的值；
- 客户端的状态机（附录 A.1，只有 1-RTT、不支持 HelloRetryRequest / PSK / 客户端证书）：`St`、`Ev`、`step`、`run`。

证明了：
- `unframe_frame`：写出来再读回来不变，后面跟着的数据原样留下；`unframe_some`：读成功时，输入正好是 写出来的 ++ 剩下的
  （读到的长度和内容是唯一的，不会多读也不会少读）；
- `rec_parse_write` / `rec_parse_some`：记录也一样（另外长度超过 2^14 + 256 时拒绝）；`hs_parse` / `hs_parse_some`：握手消息也一样；
- `unpad_inner`：内层明文（内容 + 类型 + 若干个 0）能拆回 (内容, 类型)；`unpad_zeros`：全是 0 的拒绝；
- `nonce_inj`：序号小于 2^64 时，不同的序号给出不同的 nonce（同一个密钥下 nonce 不会重复）；
- `unprotect_protect`：加密的记录解得开、回到内层明文；`protect_rec`：加密的记录就是类型 23、版本 0x0303 的普通记录；
- `handshake_order`：客户端走到 connected，收到的事件一定以
  发出 ClientHello、ServerHello、EncryptedExtensions、Certificate、CertificateVerify（签名对上）、Finished（MAC 对上）开头，
  后面只有握手以后的消息（应用数据、NewSessionTicket、KeyUpdate）。所以 Finished 没核对就不会发、收应用数据，
  也不能跳过 Certificate / CertificateVerify。

没有证明 / 没有覆盖的：
- RFC 8448 用的是 TLS_AES_128_GCM_SHA256，我们还没有 AES-GCM，所以加密以后的记录没法逐字节对（密钥、IV、各个秘密值、
  Finished 和记录头都对上了）；
- 证书链和签名的验证（`cert` / `cv` 事件只是“验证通过了”的抽象）；ServerHello 里各个字段的检查。
-/
import Lark.Tls

namespace Lark
namespace Tls13
open Lark.Tls

/-! ## 大端编码 -/

def be (n x : Nat) : List Nat := (enc n x).reverse
def unbe (l : List Nat) : Nat := dec l.reverse

theorem be_len (n x : Nat) : (be n x).length = n := by
  simp only [be, List.length_reverse, enc_len]

theorem unbe_be (n x : Nat) (h : x < 256 ^ n) : unbe (be n x) = x := by
  simp only [unbe, be, List.reverse_reverse]
  exact dec_enc n x h

theorem enc_dec : ∀ l : List Nat, (∀ b ∈ l, b < 256) → enc l.length (dec l) = l
  | [], _ => rfl
  | b :: l, h => by
    have hb : b < 256 := h b (by simp)
    have ih := enc_dec l (fun x hx => h x (by simp [hx]))
    show (b + 256 * dec l) % 256 :: enc l.length ((b + 256 * dec l) / 256) = b :: l
    have e1 : (b + 256 * dec l) % 256 = b := by omega
    have e2 : (b + 256 * dec l) / 256 = dec l := by omega
    rw [e1, e2, ih]

theorem be_unbe (l : List Nat) (h : ∀ b ∈ l, b < 256) : be l.length (unbe l) = l := by
  have h' : ∀ b ∈ l.reverse, b < 256 := fun b hb => h b (List.mem_reverse.mp hb)
  have e := enc_dec l.reverse h'
  rw [List.length_reverse] at e
  unfold be unbe
  rw [e, List.reverse_reverse]

theorem take_app' {α : Type} (l₁ l₂ : List α) (n : Nat) (h : l₁.length = n) : (l₁ ++ l₂).take n = l₁ := by
  subst h
  exact take_app l₁ l₂

theorem drop_app' {α : Type} (l₁ l₂ : List α) (n : Nat) (h : l₁.length = n) : (l₁ ++ l₂).drop n = l₂ := by
  subst h
  exact drop_app l₁ l₂

/-! ## 带长度前缀的格式 -/

/-- k 字节大端长度 + 内容 -/
def frame (k : Nat) (b : List Nat) : List Nat := be k b.length ++ b

/-- 读一段：不够 k 字节、或者说的长度比剩下的多，就是 none；否则 (内容, 剩下的) -/
def unframe (k : Nat) (d : List Nat) : Option (List Nat × List Nat) :=
  if d.length < k then none
  else if d.length - k < unbe (d.take k) then none
  else some ((d.drop k).take (unbe (d.take k)), (d.drop k).drop (unbe (d.take k)))

theorem unframe_frame (k : Nat) (b r : List Nat) (h : b.length < 256 ^ k) :
    unframe k (frame k b ++ r) = some (b, r) := by
  have hl : (be k b.length).length = k := be_len k b.length
  have ht : (frame k b ++ r).take k = be k b.length := by
    unfold frame
    rw [List.append_assoc]
    exact take_app' _ _ _ hl
  have hd : (frame k b ++ r).drop k = b ++ r := by
    unfold frame
    rw [List.append_assoc]
    exact drop_app' _ _ _ hl
  have hlen : (frame k b ++ r).length = k + b.length + r.length := by
    simp only [frame, List.length_append, hl]
  have h1 : ¬(frame k b ++ r).length < k := by rw [hlen]; omega
  have h2 : ¬(frame k b ++ r).length - k < b.length := by rw [hlen]; omega
  unfold unframe
  rw [ht, hd, unbe_be k b.length h]
  simp only [h1, h2, ↓reduceIte, take_app, drop_app]

/-- 读成功时，输入正好是 写出来的 ++ 剩下的 -/
theorem unframe_some (k : Nat) (d b r : List Nat) (hd : ∀ x ∈ d, x < 256) (h : unframe k d = some (b, r)) :
    d = frame k b ++ r := by
  unfold unframe at h
  split at h
  · cases h
  · split at h
    · cases h
    · rename_i h1 h2
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨hb, hr⟩ := h
      have hbl : b.length = unbe (d.take k) := by
        rw [← hb, List.length_take, List.length_drop]
        omega
      have hk : (d.take k).length = k := by
        rw [List.length_take]
        omega
      have e := be_unbe (d.take k) (fun x hx => hd x (List.mem_of_mem_take hx))
      rw [hk] at e
      unfold frame
      rw [hbl, e, ← hb, ← hr, List.append_assoc, List.take_append_drop, List.take_append_drop]

/-! ## 记录（第 5.1 节） -/

/-- 加密的记录最长 2^14 + 256 字节 -/
def maxFrag : Nat := 16640

/-- 类型、两个字节的版本（写的时候是 3 3，第一个 ClientHello 是 3 1）、2 字节长度、内容 -/
def recWrite (t a v : Nat) (f : List Nat) : List Nat := t :: a :: v :: frame 2 f

/-- 版本不看（第 5.1 节：MUST be ignored）；长度超过 maxFrag 时拒绝 -/
def recParse : List Nat → Option (Nat × List Nat × List Nat)
  | t :: _ :: _ :: r =>
    match unframe 2 r with
    | some (f, rest) => if f.length ≤ maxFrag then some (t, f, rest) else none
    | none => none
  | _ => none

theorem rec_parse_write (t a v : Nat) (f r : List Nat) (h : f.length ≤ maxFrag) :
    recParse (recWrite t a v f ++ r) = some (t, f, r) := by
  have hf : f.length < 256 ^ 2 := by
    have e : (256 : Nat) ^ 2 = 65536 := by decide
    rw [e]
    unfold maxFrag at h
    omega
  have hu := unframe_frame 2 f r hf
  show recParse (t :: a :: v :: (frame 2 f ++ r)) = _
  simp [recParse, hu, h]

theorem rec_parse_some (d : List Nat) (t : Nat) (f rest : List Nat) (hd : ∀ x ∈ d, x < 256)
    (h : recParse d = some (t, f, rest)) : ∃ a v, d = recWrite t a v f ++ rest ∧ f.length ≤ maxFrag := by
  match d, hd, h with
  | [], _, h => simp [recParse] at h
  | [_], _, h => simp [recParse] at h
  | [_, _], _, h => simp [recParse] at h
  | t' :: a :: v :: r, hd, h =>
    cases hu : unframe 2 r with
    | none => simp [recParse, hu] at h
    | some p =>
      obtain ⟨f', rest'⟩ := p
      by_cases hl : f'.length ≤ maxFrag
      · simp [recParse, hu, hl] at h
        obtain ⟨h1, h2, h3⟩ := h
        subst h1 h2 h3
        refine ⟨a, v, ?_, hl⟩
        rw [unframe_some 2 r _ _ (fun x hx => hd x (by simp [hx])) hu]
        rfl
      · simp [recParse, hu, hl] at h

/-! ## 握手消息（第 4 节）：类型 + 3 字节长度 + 内容 -/

def hsMsg (t : Nat) (body : List Nat) : List Nat := t :: frame 3 body

def hsParse : List Nat → Option (Nat × List Nat × List Nat)
  | t :: r => (unframe 3 r).map (fun p => (t, p.1, p.2))
  | [] => none

theorem hs_parse (t : Nat) (body r : List Nat) (h : body.length < 256 ^ 3) :
    hsParse (hsMsg t body ++ r) = some (t, body, r) := by
  show hsParse (t :: (frame 3 body ++ r)) = _
  simp [hsParse, unframe_frame 3 body r h]

theorem hs_parse_some (d : List Nat) (t : Nat) (b r : List Nat) (hd : ∀ x ∈ d, x < 256)
    (h : hsParse d = some (t, b, r)) : d = hsMsg t b ++ r := by
  match d, hd, h with
  | [], _, h => simp [hsParse] at h
  | t' :: r', hd, h =>
    cases hu : unframe 3 r' with
    | none => simp [hsParse, hu] at h
    | some p =>
      obtain ⟨b', r''⟩ := p
      simp [hsParse, hu] at h
      obtain ⟨h1, h2, h3⟩ := h
      subst h1 h2 h3
      rw [unframe_some 3 r' _ _ (fun x hx => hd x (by simp [hx])) hu]
      rfl

/-- 一段数据里接连的握手消息（对 RFC 8448 用） -/
def hsAll : Nat → List Nat → List (Nat × List Nat)
  | 0, _ => []
  | k + 1, d =>
    match hsParse d with
    | some (t, b, r) => (t, b) :: hsAll k r
    | none => []

/-! ## 内层明文（第 5.2、5.4 节）：内容 + 真正的类型 + 若干个 0 -/

def inner (c : List Nat) (t z : Nat) : List Nat := c ++ t :: List.replicate z 0

/-- 倒着看：跳过 0，第一个不是 0 的是类型 -/
def unpadRev : List Nat → Option (Nat × List Nat)
  | [] => none
  | t :: r => if t = 0 then unpadRev r else some (t, r)

def unpad (d : List Nat) : Option (List Nat × Nat) := (unpadRev d.reverse).map (fun p => (p.2.reverse, p.1))

theorem unpadRev_zeros : ∀ (z : Nat) (r : List Nat), unpadRev (List.replicate z 0 ++ r) = unpadRev r
  | 0, _ => rfl
  | z + 1, r => by
    show unpadRev (0 :: (List.replicate z 0 ++ r)) = _
    rw [unpadRev, ite_eq_left rfl]
    exact unpadRev_zeros z r

theorem unpad_inner (c : List Nat) (t z : Nat) (ht : t ≠ 0) : unpad (inner c t z) = some (c, t) := by
  have e : (inner c t z).reverse = List.replicate z 0 ++ (t :: c.reverse) := by
    simp [inner]
  unfold unpad
  rw [e, unpadRev_zeros]
  simp [unpadRev, ht]

/-- 全是 0（找不到类型）的拒绝 -/
theorem unpad_zeros (z : Nat) : unpad (List.replicate z 0) = none := by
  have h := unpadRev_zeros z []
  rw [List.append_nil] at h
  simp [unpad, h, unpadRev]

/-! ## 每条记录的 nonce（第 5.3 节）：iv 异或 序号（补成 12 字节大端） -/

def nonce (iv : List Nat) (sq : Nat) : List Nat := List.zipWith (· ^^^ ·) iv (be 12 sq)

theorem zx_inj : ∀ (iv a b : List Nat), a.length = iv.length → b.length = iv.length →
    List.zipWith (· ^^^ ·) iv a = List.zipWith (· ^^^ ·) iv b → a = b
  | [], [], [], _, _, _ => rfl
  | x :: iv, y :: a, z :: b, h1, h2, h => by
    simp only [List.zipWith_cons_cons, List.cons.injEq] at h
    simp only [List.length_cons, Nat.add_right_cancel_iff] at h1 h2
    have hyz : y = z := by
      have e1 : y = x ^^^ (x ^^^ y) := by rw [← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor]
      have e2 : z = x ^^^ (x ^^^ z) := by rw [← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor]
      rw [e1, e2, h.1]
    rw [hyz, zx_inj iv a b h1 h2 h.2]
  | [], _ :: _, _, h1, _, _ => by simp at h1
  | [], [], _ :: _, _, h2, _ => by simp at h2
  | _ :: _, [], _, h1, _, _ => by simp at h1
  | _ :: _, _ :: _, [], _, h2, _ => by simp at h2

/-- 序号小于 2^64 时，不同的序号给出不同的 nonce -/
theorem nonce_inj (iv : List Nat) (hiv : iv.length = 12) (s s' : Nat) (hs : s < 2 ^ 64) (hs' : s' < 2 ^ 64)
    (h : nonce iv s = nonce iv s') : s = s' := by
  have hb := zx_inj iv (be 12 s) (be 12 s') (by rw [be_len, hiv]) (by rw [be_len, hiv]) h
  have p : (2 : Nat) ^ 64 ≤ 256 ^ 12 := by decide
  rw [← unbe_be 12 s (Nat.lt_of_lt_of_le hs p), ← unbe_be 12 s' (Nat.lt_of_lt_of_le hs' p), hb]

/-! ## 加密的记录（第 5.2 节），ChaCha20-Poly1305 -/

theorem seal_len (key n p a : List Nat) : (sealA key n p a).length = p.length + 16 := by
  simp only [sealA, List.length_append, xorC_length, poly_len]

/-- 记录头：类型 23（application_data）、版本 3 3、长度（内层明文 + 16 字节标签）；它也是 AEAD 的 aad -/
def aadOf (n : Nat) : List Nat := [23, 3, 3] ++ be 2 n

def protect (key iv : List Nat) (sq : Nat) (inr : List Nat) : List Nat :=
  aadOf (inr.length + 16) ++ sealA key (nonce iv sq) inr (aadOf (inr.length + 16))

/-- 整条记录：前 5 字节是记录头（当 aad），后面是密文 + 标签 -/
def unprotect (key iv : List Nat) (sq : Nat) (d : List Nat) : Option (List Nat) :=
  openA key (nonce iv sq) (d.drop 5) (d.take 5)

theorem unprotect_protect (key iv : List Nat) (sq : Nat) (inr : List Nat) :
    unprotect key iv sq (protect key iv sq inr) = some inr := by
  have hl : (aadOf (inr.length + 16)).length = 5 := by simp [aadOf, be_len]
  unfold unprotect protect
  rw [take_app' _ _ _ hl, drop_app' _ _ _ hl]
  exact open_seal _ _ _ _

/-- 加密的记录就是类型 23、版本 3 3 的普通记录 -/
theorem protect_rec (key iv : List Nat) (sq : Nat) (inr : List Nat) :
    protect key iv sq inr = recWrite 23 3 3 (sealA key (nonce iv sq) inr (aadOf (inr.length + 16))) := by
  unfold protect recWrite frame
  rw [seal_len]
  simp only [aadOf, List.cons_append, List.nil_append]

/-! ## SHA-256 和 HMAC-SHA256（FIPS 180-4、RFC 2104） -/

def rotr (x n : Nat) : Nat := ((x >>> n) ||| (x <<< (32 - n))) % 2 ^ 32
def chf (e f g : Nat) : Nat := (e &&& f) ^^^ ((e ^^^ (2 ^ 32 - 1)) &&& g)
def maj (a b c : Nat) : Nat := (a &&& b) ^^^ (a &&& c) ^^^ (b &&& c)
def bs0 (a : Nat) : Nat := rotr a 2 ^^^ rotr a 13 ^^^ rotr a 22
def bs1 (e : Nat) : Nat := rotr e 6 ^^^ rotr e 11 ^^^ rotr e 25
def ss0 (x : Nat) : Nat := rotr x 7 ^^^ rotr x 18 ^^^ (x >>> 3)
def ss1 (x : Nat) : Nat := rotr x 17 ^^^ rotr x 19 ^^^ (x >>> 10)

def K256 : List Nat :=
  [0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
   0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
   0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
   0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
   0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
   0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
   0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
   0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2]

def H256 : List Nat := [0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19]

def wordsBE : Nat → List Nat → List Nat
  | 0, _ => []
  | k + 1, d => unbe (d.take 4) :: wordsBE k (d.drop 4)

/-- 消息扩展：16 个字扩成 64 个 -/
def sched : Nat → Array Nat → Array Nat
  | 0, w => w
  | k + 1, w =>
    let j := w.size
    sched k (w.push ((ss1 w[j - 2]! + w[j - 7]! + ss0 w[j - 15]! + w[j - 16]!) % 2 ^ 32))

def rnd (w : Array Nat) (s : List Nat) (i : Nat) : List Nat :=
  match s with
  | [a, b, c, d, e, f, g, h] =>
    let t1 := (h + bs1 e + chf e f g + K256.getD i 0 + w[i]!) % 2 ^ 32
    let t2 := (bs0 a + maj a b c) % 2 ^ 32
    [(t1 + t2) % 2 ^ 32, a, b, c, (d + t1) % 2 ^ 32, e, f, g]
  | _ => s

def compress (h blk : List Nat) : List Nat :=
  let w := sched 48 (wordsBE 16 blk).toArray
  List.zipWith (fun x y => (x + y) % 2 ^ 32) h ((List.range 64).foldl (rnd w) h)

def chunk64 : Nat → List Nat → List (List Nat)
  | 0, _ => []
  | _ + 1, [] => []
  | k + 1, d => d.take 64 :: chunk64 k (d.drop 64)

def padMsg (m : List Nat) : List Nat :=
  m ++ [0x80] ++ List.replicate ((119 - m.length % 64) % 64) 0 ++ be 8 (8 * m.length)

def serBE : List Nat → List Nat
  | [] => []
  | w :: r => be 4 w ++ serBE r

def sha256 (m : List Nat) : List Nat :=
  serBE ((chunk64 (padMsg m).length (padMsg m)).foldl compress H256)

def hmac (key msg : List Nat) : List Nat :=
  let k0 := if 64 < key.length then sha256 key else key
  let k := k0 ++ List.replicate (64 - k0.length) 0
  sha256 (k.map (· ^^^ 0x5c) ++ sha256 (k.map (· ^^^ 0x36) ++ msg))

#guard sha256 [] == hx "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"
#guard sha256 (ascii "abc") == hx "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"
-- RFC 4231 第 4.2 节
#guard hmac (List.replicate 20 0x0b) (ascii "Hi There") ==
  hx "b0344c61d8db38535ca8afceaf0bf12b881dc200c9833da726e9376c2e32cff7"
-- RFC 5869 附录 A.1：阶段 1 的 Tls.expand 配上真的 HMAC
#guard hmac (hx "000102030405060708090a0b0c") (List.replicate 22 0x0b) ==
  hx "077709362c2e32df0ddc3f0dc47bba6390b6c73bb50f9c3122ec844ad7c2b3e5"
#guard Tls.expand hmac (hx "077709362c2e32df0ddc3f0dc47bba6390b6c73bb50f9c3122ec844ad7c2b3e5") (hx "f0f1f2f3f4f5f6f7f8f9") 42 ==
  hx "3cb25f25faacd57a90434f64d0362f2a2d2d0a90cf1a5a4c5db02d56ecc4c5bf34007208d5b887185865"

/-! ## 密钥计算（第 7.1 节） -/

def extract (salt ikm : List Nat) : List Nat := hmac salt ikm
def expandLabel (s : List Nat) (l : String) (c : List Nat) (n : Nat) : List Nat :=
  Tls.expand hmac s (labelInfo n (ascii l) c) n
/-- Derive-Secret，直接给消息的摘要 -/
def deriveH (s : List Nat) (l : String) (th : List Nat) : List Nat := expandLabel s l th 32
def zeros32 : List Nat := List.replicate 32 0

def earlySecret : List Nat := extract zeros32 zeros32
def hsSecret (shared : List Nat) : List Nat := extract (deriveH earlySecret "derived" (sha256 [])) shared
def masterSecret (shared : List Nat) : List Nat := extract (deriveH (hsSecret shared) "derived" (sha256 [])) zeros32
def finishedMac (secret th : List Nat) : List Nat := hmac (expandLabel secret "finished" [] 32) th

/-! ## 客户端的握手状态机（附录 A.1） -/

inductive St where
  | start | waitSH | waitEE | waitCert | waitCV | waitFin | connected | failed
  deriving DecidableEq, Repr

/-- 事件。sh：检查都通过的 ServerHello；cert：验证通过的证书链；cv：签名对上的 CertificateVerify；
    fin：MAC 对上的 Finished；post：握手以后的消息（应用数据、NewSessionTicket、KeyUpdate）；
    other：别的一切（不认识的、检查没通过的、顺序不对的） -/
inductive Ev where
  | sendCH | sh | ee | cert | cv | fin | post | other
  deriving DecidableEq, Repr

/-- 每个状态只接受一种事件 -/
def next : St → Ev × St
  | .start => (.sendCH, .waitSH)
  | .waitSH => (.sh, .waitEE)
  | .waitEE => (.ee, .waitCert)
  | .waitCert => (.cert, .waitCV)
  | .waitCV => (.cv, .waitFin)
  | .waitFin => (.fin, .connected)
  | .connected => (.post, .connected)
  | .failed => (.other, .failed)

def step (s : St) (e : Ev) : St :=
  if s = .failed then .failed else if e = (next s).1 then (next s).2 else .failed

def run : St → List Ev → St
  | s, [] => s
  | s, e :: es => run (step s e) es

theorem run_failed : ∀ es, run .failed es = .failed
  | [] => rfl
  | e :: es => by
    have h : step .failed e = .failed := by simp [step]
    show run (step .failed e) es = .failed
    rw [h]
    exact run_failed es

theorem ne_failed {s : St} {e : Ev} {es : List Ev} (h : run s (e :: es) = .connected) : step s e ≠ .failed := by
  intro hf
  have h' : run (step s e) es = .connected := h
  rw [hf, run_failed] at h'
  cases h'

/-- connected 以后只能是握手以后的消息 -/
theorem run_conn : ∀ es, run .connected es = .connected → ∀ e ∈ es, e = .post
  | [], _ => by intro e he; cases he
  | e :: es, h => by
    have h' : run (step .connected e) es = .connected := h
    by_cases he : e = .post
    · have hs : step .connected e = .connected := by subst he; simp [step, next]
      rw [hs] at h'
      intro x hx
      rcases List.mem_cons.mp hx with hx | hx
      · rw [hx]; exact he
      · exact run_conn es h' x hx
    · have hs : step .connected e = .failed := by simp [step, next, he]
      rw [hs, run_failed] at h'
      cases h'

def rank : St → Nat
  | .start => 6 | .waitSH => 5 | .waitEE => 4 | .waitCert => 3 | .waitCV => 2 | .waitFin => 1
  | .connected => 0 | .failed => 0

/-- 从状态 s 走到 connected 必须经过的事件 -/
def needF : Nat → St → List Ev
  | 0, _ => []
  | k + 1, s => (next s).1 :: needF k (next s).2

theorem run_gen : ∀ (es : List Ev) (s : St), s ≠ .failed → run s es = .connected →
    ∃ rest, es = needF (rank s) s ++ rest ∧ ∀ e ∈ rest, e = .post
  | [], s, _, h => by
    have hc : s = .connected := h
    subst hc
    exact ⟨[], rfl, by intro e he; cases he⟩
  | e :: es, s, hs, h => by
    by_cases hc : s = .connected
    · subst hc
      exact ⟨e :: es, rfl, run_conn (e :: es) h⟩
    · have hstep := ne_failed h
      have he : e = (next s).1 := by
        by_cases hne : e = (next s).1
        · exact hne
        · exact absurd (by simp [step, hs, hne] : step s e = .failed) hstep
      have hs' : step s e = (next s).2 := by simp [step, hs, he]
      have hn : (next s).2 ≠ .failed := by rw [← hs']; exact hstep
      have h' : run (next s).2 es = .connected := by rw [← hs']; exact h
      obtain ⟨rest, h1, h2⟩ := run_gen es (next s).2 hn h'
      have hr : rank s = rank (next s).2 + 1 := by
        cases s <;> first | rfl | exact absurd rfl hc | exact absurd rfl hs
      refine ⟨rest, ?_, h2⟩
      rw [hr, h1, he]
      all_goals rfl

/-- 走到 connected，事件一定以完整的握手开头，后面只有握手以后的消息 -/
theorem handshake_order (es : List Ev) (h : run .start es = .connected) :
    ∃ rest, es = [.sendCH, .sh, .ee, .cert, .cv, .fin] ++ rest ∧ ∀ e ∈ rest, e = .post :=
  run_gen es .start (by decide) h

#guard run .start [.sendCH, .sh, .ee, .cert, .cv, .fin, .post, .post] == .connected
#guard run .start [.sendCH, .sh, .ee, .cv, .fin] == .failed            -- 跳过 Certificate
#guard run .start [.sendCH, .sh, .ee, .cert, .cv, .post] == .failed    -- Finished 之前的应用数据
#guard run .start [.sendCH, .sh, .ee, .cert, .cv, .other] == .failed   -- Finished 的 MAC 不对

/-! ## RFC 8448 第 3 节（简单的 1-RTT 握手） -/

def cPriv : List Nat := hx "49af42ba7f7994852d713ef2784bcbcaa7911de26adc5642cb634540e7ea5005"
def cPub : List Nat := hx "99381de560e4bd43d23d8e435a7dbafeb3c06e51c13cae4d5413691e529aaf2c"
def sPriv : List Nat := hx "b1580eeadf6dd589b8ef4f2d5652578cc810e9980191ec8d058308cea216a21e"
def sPub : List Nat := hx "c9828876112095fe66762bdbf7c672e156d6cc253b833df1dd69b1b04e751f0f"
def shared : List Nat := hx "8bd4054fb55b9d63fdfbacf9f04b9f0d35e6d63f537563efd46272900f89492d"

def CH : List Nat := hx "010000c00303cb34ecb1e78163ba1c38c6dacb196a6dffa21a8d9912ec18a2ef6283024dece7000006130113031302010000910000000b0009000006736572766572ff01000100000a00140012001d0017001800190100010101020103010400230000003300260024001d002099381de560e4bd43d23d8e435a7dbafeb3c06e51c13cae4d5413691e529aaf2c002b0003020304000d0020001e040305030603020308040805080604010501060102010402050206020202002d00020101001c00024001"
def SH : List Nat := hx "020000560303a6af06a4121860dc5e6e60249cd34c95930c8ac5cb1434dac155772ed3e2692800130100002e00330024001d0020c9828876112095fe66762bdbf7c672e156d6cc253b833df1dd69b1b04e751f0f002b00020304"
/-- EncryptedExtensions、Certificate、CertificateVerify、Finished -/
def flight : List Nat := hx "080000240022000a00140012001d00170018001901000101010201030104001c00024001000000000b0001b9000001b50001b0308201ac30820115a003020102020102300d06092a864886f70d01010b0500300e310c300a06035504031303727361301e170d3136303733303031323335395a170d3236303733303031323335395a300e310c300a0603550403130372736130819f300d06092a864886f70d010101050003818d0030818902818100b4bb498f8279303d980836399b36c6988c0c68de55e1bdb826d3901a2461eafd2de49a91d015abbc9a95137ace6c1af19eaa6af98c7ced43120998e187a80ee0ccb0524b1b018c3e0b63264d449a6d38e22a5fda430846748030530ef0461c8ca9d9efbfae8ea6d1d03e2bd193eff0ab9a8002c47428a6d35a8d88d79f7f1e3f0203010001a31a301830090603551d1304023000300b0603551d0f0404030205a0300d06092a864886f70d01010b05000381810085aad2a0e5b9276b908c65f73a7267170618a54c5f8a7b337d2df7a594365417f2eae8f8a58c8f8172f9319cf36b7fd6c55b80f21a03015156726096fd335e5e67f2dbf102702e608ccae6bec1fc63a42a99be5c3eb7107c3c54e9b9eb2bd5203b1c3b84e0a8b2f759409ba3eac9d91d402dcc0cc8f8961229ac9187b42b4de100000f000084080400805a747c5d88fa9bd2e55ab085a61015b7211f824cd484145ab3ff52f1fda8477b0b7abc90db78e2d33a5c141a078653fa6bef780c5ea248eeaaa785c4f394cab6d30bbe8d4859ee511f602957b15411ac027671459e46445c9ea58c181e818e95b8c3fb0bf3278409d3be152a3da5043e063dda65cdf5aea20d53dfacd42f74f3140000209b9b141d906337fbd2cbdce71df4deda4ab42c309572cb7fffee5454b78f0718"

-- X25519（阶段 1 的规格）算出公钥和共享的秘密
#guard x25519 cPriv (9 :: List.replicate 31 0) == cPub
#guard x25519 sPriv (9 :: List.replicate 31 0) == sPub
#guard x25519 cPriv sPub == shared
#guard x25519 sPriv cPub == shared

-- 记录和握手消息的格式
#guard CH.length == 196 && SH.length == 90 && flight.length == 657
#guard recWrite 22 3 1 CH == hx "16030100c4" ++ CH
#guard recWrite 22 3 3 SH == hx "160303005a" ++ SH
#guard recParse (recWrite 22 3 1 CH ++ [1, 2]) == some (22, CH, [1, 2])
#guard (hsAll 10 (CH ++ SH)).map (·.1) == [1, 2]
#guard (hsAll 10 flight).map (·.1) == [8, 11, 15, 20]
#guard (hsAll 10 flight).map (·.2.length) == [36, 441, 132, 32]
-- 加密记录的头：服务器的 657 字节 + 类型 1 字节 + 标签 16 字节；客户端的 Finished 36 + 1 + 16
#guard aadOf ((inner flight 22 0).length + 16) == hx "17030302a2"
#guard aadOf ((inner (flight.drop 621) 22 0).length + 16) == hx "1703030035"
#guard unpad (inner flight 22 3) == some (flight, 22)
#guard nonce (hx "5d313eb2671276ee13000b30") 0 == hx "5d313eb2671276ee13000b30"
#guard nonce (hx "5d313eb2671276ee13000b30") 1 == hx "5d313eb2671276ee13000b31"

-- HKDF-Expand-Label 的 info 和 RFC 里印出来的一样
#guard labelInfo 16 (ascii "key") [] == hx "001009746c733133206b657900"
#guard labelInfo 12 (ascii "iv") [] == hx "000c08746c73313320697600"
#guard labelInfo 32 (ascii "finished") [] == hx "00200e746c7331332066696e697368656400"

-- 消息的摘要
def th1 : List Nat := sha256 (CH ++ SH)
def thCV : List Nat := sha256 (CH ++ SH ++ flight.take 621)
def th2 : List Nat := sha256 (CH ++ SH ++ flight)
#guard th1 == hx "860c06edc07858ee8e78f0e7428c58edd6b43f2ca3e6e95f02ed063cf0e1cad8"
#guard th2 == hx "9608102a0f1ccc6db6250b7b7e417b1a000eaada3daae4777a7686c9ff83df13"

-- 各个秘密值
#guard earlySecret == hx "33ad0a1c607ec03b09e6cd9893680ce210adf300aa1f2660e1b22e10f170f92a"
#guard deriveH earlySecret "derived" (sha256 []) == hx "6f2615a108c702c5678f54fc9dbab69716c076189c48250cebeac3576c3611ba"
#guard hsSecret shared == hx "1dc826e93606aa6fdc0aadc12f741b01046aa6b99f691ed221a9f0ca043fbeac"
#guard deriveH (hsSecret shared) "c hs traffic" th1 == hx "b3eddb126e067f35a780b3abf45e2d8f3b1a950738f52e9600746a0e27a55a21"
#guard deriveH (hsSecret shared) "s hs traffic" th1 == hx "b67b7d690cc16c4e75e54213cb2d37b4e9c912bcded9105d42befd59d391ad38"
#guard masterSecret shared == hx "18df06843d13a08bf2a449844c5f8a478001bc4d4c627984d5a41da8d0402919"
#guard deriveH (masterSecret shared) "c ap traffic" th2 == hx "9e40646ce79a7f9dc05af8889bce6552875afa0b06df0087f792ebb7c17504a5"
#guard deriveH (masterSecret shared) "s ap traffic" th2 == hx "a11af9f05531f856ad47116b45a950328204b4f44bfb6b3a4b4f1f3fcb631643"
#guard deriveH (masterSecret shared) "exp master" th2 == hx "fe22f881176eda18eb8f44529e6792c50c9a3f89452f68d8ae311b4309d3cf50"

-- 流量密钥（AES-128 的 16 字节密钥；ChaCha20 时同样的算法取 32 字节）和 IV
def sHs : List Nat := hx "b67b7d690cc16c4e75e54213cb2d37b4e9c912bcded9105d42befd59d391ad38"
def cHs : List Nat := hx "b3eddb126e067f35a780b3abf45e2d8f3b1a950738f52e9600746a0e27a55a21"
def sAp : List Nat := hx "a11af9f05531f856ad47116b45a950328204b4f44bfb6b3a4b4f1f3fcb631643"
def cAp : List Nat := hx "9e40646ce79a7f9dc05af8889bce6552875afa0b06df0087f792ebb7c17504a5"
#guard expandLabel sHs "key" [] 16 == hx "3fce516009c21727d0f2e4e86ee403bc"
#guard expandLabel sHs "iv" [] 12 == hx "5d313eb2671276ee13000b30"
#guard expandLabel cHs "key" [] 16 == hx "dbfaa693d1762c5b666af5d950258d01"
#guard expandLabel cHs "iv" [] 12 == hx "5bd3c71b836e0b76bb73265f"
#guard expandLabel sAp "key" [] 16 == hx "9f02283b6c9c07efc26bb9f2ac92e356"
#guard expandLabel sAp "iv" [] 12 == hx "cf782b88dd83549aadf1e984"
#guard expandLabel cAp "key" [] 16 == hx "17422dda596ed5d9acd890e3c63f5051"
#guard expandLabel cAp "iv" [] 12 == hx "5b78923dee08579033e523d9"

-- Finished：服务器的对 CH..CertificateVerify 的摘要，正好是 flight 最后 36 字节；客户端的对 CH..服务器 Finished
#guard expandLabel sHs "finished" [] 32 == hx "008d3b66f816ea559f96b537e885c31fc068bf492c652f01f288a1d8cdc19fc8"
#guard hsMsg 20 (finishedMac sHs thCV) == flight.drop 621
#guard expandLabel cHs "finished" [] 32 == hx "b80ad01015fb2f0bd65ff7d4da5d6bf83f84821d1f87fdc7d3c75b5a7b42d9c4"
#guard hsMsg 20 (finishedMac cHs th2) == hx "14000020a8ec436d677634ae525ac1fcebe11a039ec17694fac6e98527b642f2edd5ce61"

end Tls13
end Lark
