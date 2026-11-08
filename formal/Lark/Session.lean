/-
apps/ltls 的证明 · 阶段 3、4a：一次完整的握手，CertificateVerify 用 Ed25519 签名（先证明，再写 apps/ltls/tls/session.lark）

模型停在握手消息这一层（每条消息含 4 字节的头）；记录层的加密和解密在 Tls13.lean 里已经证明了（unprotect_protect）。
CertificateVerify（RFC 8446 第 4.4.3 节）= 签名算法 ed25519（0x0807，2 字节）+ 签名（2 字节长度），
签的是 Ed25519.cvContent（64 个空格 + 上下文 + 0 + 到 Certificate 为止的消息摘要）。
客户端用的公钥现在是事先知道的（钉住的公钥）；从证书里取公钥、验证证书链是阶段 4b。

一方看到的握手（`View`）：ClientHello、ServerHello、EncryptedExtensions、Certificate、CertificateVerify、服务器的 Finished，
加上它用 X25519 算出来的共享秘密。服务器按 `serverFlight` 算出后面两条；客户端按 `clientEvents` 核对，再交给状态机。

证明了：
- `cvOk_cvMsg`：服务器按格式写的 CertificateVerify，只要签名本身验证得过，客户端就认（格式拆得开、签名长度对）；
- `honest`：信道把字节原样送到、两边的共享秘密一样（X25519 两边一样靠测试）、Ed25519 签了再验通过（靠 RFC 8032 的向量，
  没有证明）时，客户端的状态机走到 connected，服务器接受客户端的 Finished，两边的应用流量密钥和 IV 一样；
- `honest_data`：于是客户端加密的应用数据，服务器解得开，反过来也一样；
- `bad_cv` / `bad_fin`：CertificateVerify 验证不过、或者服务器的 Finished 和客户端自己算的不一样时，状态机走不到 connected。
没有证明：改了任何一个字节就一定核对不过（要 HMAC 抗碰撞、Ed25519 不可伪造，是密码学假设）。
-/
import Lark.Hello
import Lark.Ed25519

namespace Lark
namespace Session
open Lark.Tls Lark.Tls13

structure View where
  ch : List Nat
  sh : List Nat
  ee : List Nat
  cert : List Nat
  cv : List Nat
  sfin : List Nat
  shared : List Nat

def th1V (v : View) : List Nat := sha256 (v.ch ++ v.sh)
/-- CertificateVerify 覆盖到 Certificate -/
def thCertV (v : View) : List Nat := sha256 (v.ch ++ v.sh ++ v.ee ++ v.cert)
/-- 服务器的 Finished 覆盖到 CertificateVerify -/
def thCVV (v : View) : List Nat := sha256 (v.ch ++ v.sh ++ v.ee ++ v.cert ++ v.cv)
/-- 客户端的 Finished 和应用流量密钥覆盖到服务器的 Finished -/
def th2V (v : View) : List Nat := sha256 (v.ch ++ v.sh ++ v.ee ++ v.cert ++ v.cv ++ v.sfin)

def cHsV (v : View) : List Nat := deriveH (hsSecret v.shared) "c hs traffic" (th1V v)
def sHsV (v : View) : List Nat := deriveH (hsSecret v.shared) "s hs traffic" (th1V v)
def cApV (v : View) : List Nat := deriveH (masterSecret v.shared) "c ap traffic" (th2V v)
def sApV (v : View) : List Nat := deriveH (masterSecret v.shared) "s ap traffic" (th2V v)

/-- 流量秘密 → ChaCha20-Poly1305 的 32 字节密钥和 12 字节 IV -/
def keyOf (s : List Nat) : List Nat := expandLabel s "key" [] 32
def ivOf (s : List Nat) : List Nat := expandLabel s "iv" [] 12

/-- 签名算法 ed25519 -/
def ed25519Scheme : Nat := 0x0807

/-- CertificateVerify：0x0807 + 签名（2 字节长度） -/
def cvMsg (sk : List Nat) (v : View) : List Nat :=
  hsMsg 15 (be 2 ed25519Scheme ++ frame 2 (Ed25519.sign sk (Ed25519.cvContent (thCertV v))))

/-- 客户端核对 CertificateVerify：类型 15、后面没有多的、算法是 0x0807、签名验证得过 -/
def cvOk (pk : List Nat) (v : View) : Bool :=
  match hsParse v.cv with
  | some (t, b, rest) =>
    t == 15 && rest.isEmpty && b.take 2 == be 2 ed25519Scheme &&
      (match unframe 2 (b.drop 2) with
       | some (sig, r2) => r2.isEmpty && Ed25519.verify pk (Ed25519.cvContent (thCertV v)) sig
       | none => false)
  | none => false

def sfinMsg (v : View) : List Nat := hsMsg 20 (finishedMac (sHsV v) (thCVV v))
def cfinMsg (v : View) : List Nat := hsMsg 20 (finishedMac (cHsV v) (th2V v))

/-- 服务器：前四条和共享秘密已经有了，算出 CertificateVerify 和 Finished -/
def serverFlight (sk ch sh ee cert shared : List Nat) : View :=
  let v0 : View := ⟨ch, sh, ee, cert, [], [], shared⟩
  let v1 : View := { v0 with cv := cvMsg sk v0 }
  { v1 with sfin := sfinMsg v1 }

/-- 客户端：核对 CertificateVerify 和服务器的 Finished，得到给状态机的事件 -/
def clientEvents (pk : List Nat) (v : View) : List Ev :=
  [.sendCH, .sh, .ee, .cert,
   if cvOk pk v then .cv else .other,
   if v.sfin = sfinMsg v then .fin else .other]

/-- 服务器核对客户端的 Finished -/
def serverAccepts (v : View) (cfin : List Nat) : Bool := cfin == cfinMsg v

theorem be_scheme : be 2 ed25519Scheme = [8, 7] := by decide

/-- 按格式写的 CertificateVerify，签名本身验证得过，客户端就认 -/
theorem cvOk_cvMsg (sk pk : List Nat) (v : View) (hv : v.cv = cvMsg sk v)
    (hsig : Ed25519.verify pk (Ed25519.cvContent (thCertV v)) (Ed25519.sign sk (Ed25519.cvContent (thCertV v))) = true) :
    cvOk pk v = true := by
  have hsl := Ed25519.sign_len sk (Ed25519.cvContent (thCertV v))
  have hu : unframe 2 (frame 2 (Ed25519.sign sk (Ed25519.cvContent (thCertV v)))) =
      some (Ed25519.sign sk (Ed25519.cvContent (thCertV v)), []) := by
    have := unframe_frame 2 (Ed25519.sign sk (Ed25519.cvContent (thCertV v))) [] (by rw [hsl]; decide)
    rwa [List.append_nil] at this
  have hbl : (be 2 ed25519Scheme ++ frame 2 (Ed25519.sign sk (Ed25519.cvContent (thCertV v)))).length < 256 ^ 3 := by
    simp only [List.length_append, be_len, frame, hsl]
    decide
  have hp : hsParse v.cv = some (15, be 2 ed25519Scheme ++ frame 2 (Ed25519.sign sk (Ed25519.cvContent (thCertV v))), []) := by
    have := hs_parse 15 _ [] hbl
    rw [List.append_nil] at this
    rw [hv]
    exact this
  have ht : (be 2 ed25519Scheme ++ frame 2 (Ed25519.sign sk (Ed25519.cvContent (thCertV v)))).take 2 = be 2 ed25519Scheme :=
    take_app' _ _ _ (be_len 2 _)
  have hd : (be 2 ed25519Scheme ++ frame 2 (Ed25519.sign sk (Ed25519.cvContent (thCertV v)))).drop 2 =
      frame 2 (Ed25519.sign sk (Ed25519.cvContent (thCertV v))) := drop_app' _ _ _ (be_len 2 _)
  unfold cvOk
  rw [hp]
  simp only [ht, hd, hu, hsig]
  decide

theorem sfin_ok (sk ch sh ee cert shared : List Nat) :
    (serverFlight sk ch sh ee cert shared).sfin = sfinMsg (serverFlight sk ch sh ee cert shared) := rfl

theorem cv_ok (sk ch sh ee cert shared : List Nat) :
    (serverFlight sk ch sh ee cert shared).cv = cvMsg sk (serverFlight sk ch sh ee cert shared) := rfl

/-- 正常的握手：客户端看到的就是服务器发的（只有共享秘密是各自算的，假设一样）；客户端用的公钥对得上服务器的私钥 -/
theorem honest (sk pk ch sh ee cert sc ss : List Nat) (hs : sc = ss)
    (hsig : ∀ m, Ed25519.verify pk m (Ed25519.sign sk m) = true) :
    let vs := serverFlight sk ch sh ee cert ss
    let vc := { vs with shared := sc }
    run .start (clientEvents pk vc) = .connected ∧ serverAccepts vs (cfinMsg vc) = true ∧
      keyOf (cApV vc) = keyOf (cApV vs) ∧ ivOf (cApV vc) = ivOf (cApV vs) ∧
      keyOf (sApV vc) = keyOf (sApV vs) ∧ ivOf (sApV vc) = ivOf (sApV vs) := by
  subst hs
  intro vs vc
  have hv : vc = vs := rfl
  rw [hv]
  have h1 : cvOk pk vs = true := cvOk_cvMsg sk pk vs (cv_ok sk ch sh ee cert sc) (hsig _)
  have h2 : vs.sfin = sfinMsg vs := sfin_ok sk ch sh ee cert sc
  refine ⟨?_, ?_, rfl, rfl, rfl, rfl⟩
  · simp only [clientEvents, h1, h2, ↓reduceIte]
    rfl
  · simp [serverAccepts]

/-- 于是应用数据两个方向都解得开 -/
theorem honest_data (sk ch sh ee cert sc ss : List Nat) (hs : sc = ss) (sq : Nat) (inr : List Nat) :
    let vs := serverFlight sk ch sh ee cert ss
    let vc := { vs with shared := sc }
    unprotect (keyOf (cApV vs)) (ivOf (cApV vs)) sq (protect (keyOf (cApV vc)) (ivOf (cApV vc)) sq inr) = some inr ∧
    unprotect (keyOf (sApV vc)) (ivOf (sApV vc)) sq (protect (keyOf (sApV vs)) (ivOf (sApV vs)) sq inr) = some inr := by
  subst hs
  intro vs vc
  exact ⟨unprotect_protect _ _ _ _, unprotect_protect _ _ _ _⟩

theorem run_other4 (a : Ev) :
    run .start [.sendCH, .sh, .ee, .cert, .other, a] = .failed := by cases a <;> rfl

theorem run_other5 :
    run .start [.sendCH, .sh, .ee, .cert, .cv, .other] = .failed := rfl

/-- CertificateVerify 验证不过：走不到 connected -/
theorem bad_cv (pk : List Nat) (v : View) (h : cvOk pk v = false) : run .start (clientEvents pk v) ≠ .connected := by
  simp only [clientEvents, h, Bool.false_eq_true, ↓reduceIte]
  rw [run_other4]
  intro h'
  cases h'

/-- 服务器的 Finished 对不上：走不到 connected -/
theorem bad_fin (pk : List Nat) (v : View) (h : v.sfin ≠ sfinMsg v) : run .start (clientEvents pk v) ≠ .connected := by
  cases hc : cvOk pk v
  · exact bad_cv pk v hc
  · simp only [clientEvents, hc, h, ↓reduceIte]
    rw [run_other5]
    intro h'
    cases h'

-- 例子：RFC 8032 TEST 1 的密钥当服务器的签名密钥，用 RFC 8448 的前四条消息（只是当作字节用）跑一次
def skEx : List Nat := Ed25519.sk1
def pkEx : List Nat := Ed25519.pk1
def vsEx : View := serverFlight skEx CH SH ((hsAll 10 flight).headD (0, [])).2 [] shared
#guard (vsEx.cv.take 6) == [15, 0, 0, 68, 8, 7]
#guard cvOk pkEx vsEx
#guard run .start (clientEvents pkEx vsEx) == .connected
#guard serverAccepts vsEx (cfinMsg vsEx)
#guard !cvOk Ed25519.pk2 vsEx
#guard run .start (clientEvents Ed25519.pk2 vsEx) == .failed
#guard run .start (clientEvents pkEx { vsEx with sfin := vsEx.sfin.set 10 ((vsEx.sfin.getD 10 0 + 1) % 256) }) == .failed
#guard (keyOf (cApV vsEx)).length == 32 && (ivOf (cApV vsEx)).length == 12

end Session
end Lark
