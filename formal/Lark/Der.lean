/-
apps/ltls 的证明 · 阶段 4b（一）：DER 编码（X.690）、Ed25519 的公钥（SubjectPublicKeyInfo）和证书的最外层（RFC 5280、RFC 8410）
先证明，再写 apps/ltls/tls/der.lark 和 tls/x509.lark。

DER 要求同一个值只有一种写法（长度用最短的形式）。这里的做法简单：先按格式读出来，再写回去和输入比，不一样就拒绝。
所以“读成功时，输入正好是读出来的东西的标准写法”几乎是显然的（`decLen_some`、`parseTlv_some`），
另外证明标准写法一定读得回来（`decLen_encLen`、`parseTlv_tlv`）。长度最多用 3 个字节（小于 2^24，证书足够了）；
这里字节是 Nat，Lark 里另外检查每个字节小于 256。

证明了：
- 长度：`decLen_encLen` / `decLen_some`；一个元素（标签 + 长度 + 内容）：`parseTlv_tlv` / `parseTlv_some`；
- Ed25519 公钥（RFC 8410 第 4 节，30 2a 30 05 06 03 2b 65 70 03 21 00 + 32 字节）：`parseSpki_spki` / `parseSpki_some`；
- 证书的最外层（tbsCertificate、签名算法必须是 Ed25519、签名 64 字节）：`parseCert_certW` / `parseCert_some`。
用 #guard 对了 RFC 8410 第 10 节的例子：公钥、私钥算出的公钥、证书拆出来的各个部分、证书的 Ed25519 签名验证通过。
还没做：证书里的名字、有效期、扩展，证书链（下一步）。
-/
import Lark.Ed25519
import Lark.Base64

namespace Lark
namespace Der
open Lark.Tls Lark.Tls13

theorem iteT {α : Type} {c : Prop} {_ : Decidable c} {a b : α} (h : c) : (if c then a else b) = a :=
  by simp [h]
theorem iteF {α : Type} {c : Prop} {_ : Decidable c} {a b : α} (h : ¬c) : (if c then a else b) = b :=
  by simp [h]

/-! ## 长度 -/

/-- 最短的写法：< 128 一个字节；否则 0x81 / 0x82 / 0x83 后面跟 1 / 2 / 3 个字节 -/
def encLen (n : Nat) : List Nat :=
  if n < 128 then [n]
  else if n < 256 then [0x81, n]
  else if n < 65536 then [0x82, n / 256, n % 256]
  else [0x83, n / 65536, n / 256 % 256, n % 256]

/-- 照格式读，不管是不是最短的 -/
def decLenRaw : List Nat → Option (Nat × List Nat)
  | b :: r =>
    if b < 128 then some (b, r)
    else if b = 0x81 then (match r with | x :: r' => some (x, r') | [] => none)
    else if b = 0x82 then (match r with | x :: y :: r' => some (x * 256 + y, r') | _ => none)
    else if b = 0x83 then (match r with | x :: y :: z :: r' => some (x * 65536 + y * 256 + z, r') | _ => none)
    else none
  | [] => none

/-- 读出来再写回去，和输入一样才算（不是最短的写法就拒绝） -/
def decLen (d : List Nat) : Option (Nat × List Nat) :=
  match decLenRaw d with
  | some (n, r) => if encLen n ++ r = d then some (n, r) else none
  | none => none

theorem raw_enc (n : Nat) (r : List Nat) : decLenRaw (encLen n ++ r) = some (n, r) := by
  unfold encLen
  by_cases h1 : n < 128
  · simp [h1, decLenRaw]
  · by_cases h2 : n < 256
    · simp [h1, h2, decLenRaw]
    · by_cases h3 : n < 65536
      · simp [h1, h2, h3, decLenRaw] <;> omega
      · simp [h1, h2, h3, decLenRaw] <;> omega

theorem decLen_encLen (n : Nat) (r : List Nat) : decLen (encLen n ++ r) = some (n, r) := by
  simp [decLen, raw_enc]

theorem decLen_some (d : List Nat) (n : Nat) (r : List Nat) (h : decLen d = some (n, r)) : d = encLen n ++ r := by
  unfold decLen at h
  cases hr : decLenRaw d with
  | none => simp [hr] at h
  | some p =>
    obtain ⟨n', r'⟩ := p
    rw [hr] at h
    dsimp only at h
    by_cases hc : encLen n' ++ r' = d
    · rw [iteT hc] at h
      cases h
      exact hc.symm
    · rw [iteF hc] at h
      cases h

/-! ## 一个元素：标签 + 长度 + 内容 -/

def tlv (t : Nat) (v : List Nat) : List Nat := t :: (encLen v.length ++ v)

def parseTlv : List Nat → Option (Nat × List Nat × List Nat)
  | t :: r =>
    match decLen r with
    | some (n, r') => if n ≤ r'.length then some (t, r'.take n, r'.drop n) else none
    | none => none
  | [] => none

theorem parseTlv_tlv (t : Nat) (v rest : List Nat) : parseTlv (tlv t v ++ rest) = some (t, v, rest) := by
  have e : tlv t v ++ rest = t :: (encLen v.length ++ (v ++ rest)) := by
    simp [tlv]
  rw [e]
  simp [parseTlv, decLen_encLen]

theorem parseTlv_some (d : List Nat) (t : Nat) (v rest : List Nat) (h : parseTlv d = some (t, v, rest)) :
    d = tlv t v ++ rest := by
  cases d with
  | nil => simp [parseTlv] at h
  | cons t' r =>
    simp only [parseTlv] at h
    cases hd : decLen r with
    | none => simp [hd] at h
    | some p =>
      obtain ⟨n, r'⟩ := p
      rw [hd] at h
      dsimp only at h
      by_cases hn : n ≤ r'.length
      · rw [iteT hn] at h
        cases h
        have hr := decLen_some r n r' hd
        have hl : (r'.take n).length = n := by rw [List.length_take]; omega
        rw [hr]
        simp only [tlv, hl, List.cons_append, List.append_assoc, List.take_append_drop]
      · rw [iteF hn] at h
        cases h

/-- 一段内容里接连的元素，读到用完为止 -/
def tlvs : Nat → List Nat → Option (List (Nat × List Nat))
  | _, [] => some []
  | 0, _ :: _ => none
  | f + 1, a :: r =>
    match parseTlv (a :: r) with
    | some (t, v, rest) => (tlvs f rest).map ((t, v) :: ·)
    | none => none

/-! ## Ed25519 的公钥（RFC 8410 第 4 节） -/

/-- 1.3.101.112 -/
def edOid : List Nat := [43, 101, 112]

/-- SEQUENCE { SEQUENCE { OID 1.3.101.112 }, BIT STRING (0 个没用的位) 公钥 } -/
def spki (pk : List Nat) : List Nat := tlv 0x30 (tlv 0x30 (tlv 6 edOid) ++ tlv 3 (0 :: pk))

def spkiHdr : List Nat := [0x30, 42, 0x30, 5, 6, 3, 43, 101, 112, 3, 33, 0]

theorem spki_eq (pk : List Nat) (h : pk.length = 32) : spki pk = spkiHdr ++ pk := by
  simp [spki, tlv, encLen, edOid, spkiHdr, h]

/-- 只认 32 字节的 Ed25519 公钥，并且写法一个字节都不能差 -/
def parseSpki (d : List Nat) : Option (List Nat) :=
  if (d.drop 12).length = 32 ∧ spki (d.drop 12) = d then some (d.drop 12) else none

theorem parseSpki_spki (pk : List Nat) (h : pk.length = 32) : parseSpki (spki pk) = some pk := by
  have hd : (spki pk).drop 12 = pk := by
    rw [spki_eq pk h]
    exact drop_app' spkiHdr pk 12 rfl
  unfold parseSpki
  simp [hd, h]

theorem parseSpki_some (d pk : List Nat) (h : parseSpki d = some pk) : d = spki pk ∧ pk.length = 32 := by
  unfold parseSpki at h
  by_cases hc : (d.drop 12).length = 32 ∧ spki (d.drop 12) = d
  · rw [iteT hc] at h
    cases h
    exact ⟨hc.2.symm, hc.1⟩
  · rw [iteF hc] at h
    cases h

/-! ## 证书的最外层（RFC 5280 第 4.1 节；签名算法只认 Ed25519，RFC 8410 第 6 节） -/

def edAlg : List Nat := tlv 0x30 (tlv 6 edOid)

/-- SEQUENCE { tbsCertificate, AlgorithmIdentifier Ed25519, BIT STRING 签名 }；tbs 是完整的一个元素 -/
def certW (tbs sig : List Nat) : List Nat := tlv 0x30 (tbs ++ (edAlg ++ tlv 3 (0 :: sig)))

def tailHdr : List Nat := [0x30, 5, 6, 3, 43, 101, 112, 3, 65, 0]

theorem tail_eq (sig : List Nat) (h : sig.length = 64) : edAlg ++ tlv 3 (0 :: sig) = tailHdr ++ sig := by
  simp [edAlg, tlv, encLen, edOid, tailHdr, h]

/-- 返回 (tbsCertificate 的完整写法, 签名)。签名要验的就是 tbs 的完整写法 -/
def parseCert (d : List Nat) : Option (List Nat × List Nat) :=
  match parseTlv d with
  | some (t, body, rest) =>
    if t = 0x30 ∧ rest = [] then
      match parseTlv body with
      | some (t2, tv, r) =>
        if t2 = 0x30 ∧ (r.drop 10).length = 64 ∧ r = edAlg ++ tlv 3 (0 :: r.drop 10)
        then some (tlv 0x30 tv, r.drop 10) else none
      | none => none
    else none
  | none => none

theorem parseCert_certW (tv sig : List Nat) (hs : sig.length = 64) :
    parseCert (certW (tlv 0x30 tv) sig) = some (tlv 0x30 tv, sig) := by
  have h1 : parseTlv (certW (tlv 0x30 tv) sig) = some (0x30, tlv 0x30 tv ++ (edAlg ++ tlv 3 (0 :: sig)), []) := by
    have := parseTlv_tlv 0x30 (tlv 0x30 tv ++ (edAlg ++ tlv 3 (0 :: sig))) []
    rw [List.append_nil] at this
    exact this
  have h2 := parseTlv_tlv 0x30 tv (edAlg ++ tlv 3 (0 :: sig))
  have hd : (edAlg ++ tlv 3 (0 :: sig)).drop 10 = sig := by
    rw [tail_eq sig hs]
    exact drop_app' tailHdr sig 10 rfl
  have c1 : (0x30 : Nat) = 0x30 ∧ ([] : List Nat) = [] := ⟨rfl, rfl⟩
  have c2 : (0x30 : Nat) = 0x30 ∧ ((edAlg ++ tlv 3 (0 :: sig)).drop 10).length = 64 ∧
      edAlg ++ tlv 3 (0 :: sig) = edAlg ++ tlv 3 (0 :: (edAlg ++ tlv 3 (0 :: sig)).drop 10) := by
    rw [hd]
    exact ⟨rfl, hs, rfl⟩
  unfold parseCert
  rw [h1]
  dsimp only
  rw [iteT c1, h2]
  dsimp only
  rw [iteT c2, hd]

theorem parseCert_some (d tbs sig : List Nat) (h : parseCert d = some (tbs, sig)) :
    d = certW tbs sig ∧ sig.length = 64 ∧ ∃ tv, tbs = tlv 0x30 tv := by
  unfold parseCert at h
  cases h1 : parseTlv d with
  | none => simp [h1] at h
  | some p =>
    obtain ⟨t, body, rest⟩ := p
    rw [h1] at h
    dsimp only at h
    by_cases hc : t = 0x30 ∧ rest = []
    · rw [iteT hc] at h
      cases h2 : parseTlv body with
      | none => simp [h2] at h
      | some q =>
        obtain ⟨t2, tv, r⟩ := q
        rw [h2] at h
        dsimp only at h
        by_cases hc2 : t2 = 0x30 ∧ (r.drop 10).length = 64 ∧ r = edAlg ++ tlv 3 (0 :: r.drop 10)
        · rw [iteT hc2] at h
          cases h
          have ed := parseTlv_some d t body rest h1
          have eb := parseTlv_some body t2 tv r h2
          obtain ⟨rfl, rfl⟩ := hc
          obtain ⟨rfl, hlen, hr⟩ := hc2
          refine ⟨?_, hlen, tv, rfl⟩
          rw [ed, eb, List.append_nil, certW]
          rw [← hr]
        · rw [iteF hc2] at h
          cases h
    · rw [iteF hc] at h
      cases h

/-! ## RFC 8410 第 10 节的例子 -/

def b64 (s : String) : List Nat := (Base64.dec false (ascii s)).getD []

-- 第 10.1 节的公钥；第 10.3 节的私钥算出来的就是它
def rfcPub : List Nat := b64 "MCowBQYDK2VwAyEAGb9ECWmEzf6FQbrBZ9w7lshQhqowtrbLDFw4rXAxZuE="
def rfcPk : List Nat := hx "19bf44096984cdfe8541bac167dc3b96c85086aa30b6b6cb0c5c38ad703166e1"
#guard parseSpki rfcPub == some rfcPk
#guard spki rfcPk == rfcPub
#guard Ed25519.pubOf (hx "d4ee72dbf913584ad5b6d8f1f769f8ad3afe7c28cbf1d4fbe097a88f44755842") == rfcPk
-- 改一个字节、多一个字节、少一个字节都不认
#guard parseSpki (rfcPub.set 8 113) == none
#guard parseSpki (rfcPub ++ [0]) == none
#guard parseSpki (rfcPub.dropLast) == none

-- 第 10.2 节的证书（自己签发，用 Ed25519 签了一个 X25519 的公钥）
def rfcCert : List Nat := b64 ("MIIBLDCB36ADAgECAghWAUdKKo3DMDAFBgMrZXAwGTEXMBUGA1UEAwwOSUVURiBUZX" ++
  "N0IERlbW8wHhcNMTYwODAxMTIxOTI0WhcNNDAxMjMxMjM1OTU5WjAZMRcwFQYDVQQD" ++
  "DA5JRVRGIFRlc3QgRGVtbzAqMAUGAytlbgMhAIUg8AmJMKdUdIt93LQ+91oNvzoNJj" ++
  "ga9OukqY6qm05qo0UwQzAPBgNVHRMBAf8EBTADAQEAMA4GA1UdDwEBAAQEAwIDCDAg" ++
  "BgNVHQ4BAQAEFgQUmx9e7e0EM4Xk97xiPFl1uQvIuzswBQYDK2VwA0EAryMB/t3J5v" ++
  "/BzKc9dNZIpDmAgs3babFOTQbs+BolzlDUwsPrdGxO3YNGhW7Ibz3OGhhlxXrCe1Cg" ++
  "w1AH9efZBw==")
#guard rfcCert.length == 304
#guard (parseCert rfcCert).map (fun p => (p.1.length, p.2)) ==
  some (226, hx "af2301feddc9e6ffc1cca73d74d648a4398082cddb69b14e4d06ecf81a25ce50d4c2c3eb746c4edd8346856ec86f3dce1a1865c57ac27b50a0c35007f5e7d907")
-- tbsCertificate 里的 8 个元素：[0] 版本、序列号、签名算法、签发者、有效期、主体、公钥、[3] 扩展
#guard ((parseCert rfcCert).bind (fun p => (parseTlv p.1).bind (fun q => tlvs 20 q.2.1))).map (·.map (·.1)) ==
  some [0xa0, 0x02, 0x30, 0x30, 0x30, 0x30, 0x30, 0xa3]
-- 签名用的是第 10.3 节的私钥（公钥是第 10.1 节的）
#guard (parseCert rfcCert).map (fun p => Ed25519.verify rfcPk p.1 p.2) == some true
#guard (parseCert (rfcCert.set 100 0)).map (fun p => Ed25519.verify rfcPk p.1 p.2) != some true
-- 长度不是最短的写法：拒绝
#guard decLen [0x81, 5] == none
#guard decLen [0x82, 0, 200] == none
#guard decLen [0x81, 200, 7] == some (200, [7])

end Der
end Lark
