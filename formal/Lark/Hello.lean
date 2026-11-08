/-
apps/ltls 的证明 · 阶段 3：ClientHello、ServerHello 和扩展的格式（RFC 8446 第 4.1.2、4.1.3、4.2 节）
先证明，再写 apps/ltls/tls/hello.lark。

只取我们用到的子集，但字节格式就是真的 TLS 1.3：
  ClientHello = 3 3、32 字节随机数、session_id（1 字节长度）、cipher_suites（2 字节长度）、
                compression_methods（1 字节长度，内容是 [0]）、extensions（2 字节长度）
  ServerHello = 3 3、32 字节随机数、session_id（1 字节长度）、cipher_suite（2 字节）、0、extensions（2 字节长度）
  扩展 = 2 字节类型 + 内容（2 字节长度）

证明了：
- `unfields_fields`：接连几段带长度前缀的数据，写出来再按同样的长度宽度读回来不变，后面的原样留下；
- `extsP_extsW`：扩展列表写出来再读回来不变（类型 < 65536、内容 < 65536 字节）；
- `chP_chW` / `shP_shW`：ClientHello / ServerHello 写出来再读回来不变；
- `chP_some` / `shP_some`：读成功时，输入正好是用读出来的字段写出来的（不会有多的、漏掉的字节）。
没有覆盖：各个扩展内容（supported_versions、key_share……）自己的格式，它们在 hello.lark 里用同样的 frame 拼。
-/
import Lark.Tls13

namespace Lark
namespace Hello
open Lark.Tls Lark.Tls13

theorem e1 : (256 : Nat) ^ 1 = 256 := rfl
theorem e2 : (256 : Nat) ^ 2 = 65536 := by decide

/-- 2 字节大端 -/
theorem be2 (t : Nat) (h : t < 65536) : be 2 t = [t / 256, t % 256] := by
  have hm : t / 256 % 256 = t / 256 := Nat.mod_eq_of_lt (by omega)
  simp [be, enc, hm]

/-! ## 接连几段带长度前缀的数据 -/

def fields : List (Nat × List Nat) → List Nat
  | [] => []
  | (k, b) :: r => frame k b ++ fields r

def unfields : List Nat → List Nat → Option (List (List Nat) × List Nat)
  | [], d => some ([], d)
  | k :: ks, d =>
    match unframe k d with
    | some (b, r) => (unfields ks r).map (fun p => (b :: p.1, p.2))
    | none => none

theorem unfields_fields : ∀ (fs : List (Nat × List Nat)) (rest : List Nat),
    (∀ p ∈ fs, p.2.length < 256 ^ p.1) → unfields (fs.map (·.1)) (fields fs ++ rest) = some (fs.map (·.2), rest)
  | [], _, _ => rfl
  | (k, b) :: r, rest, h => by
    have hb : b.length < 256 ^ k := h (k, b) (by simp)
    have ih := unfields_fields r rest (fun p hp => h p (by simp [hp]))
    have hu : unframe k (frame k b ++ (fields r ++ rest)) = some (b, fields r ++ rest) := unframe_frame k b _ hb
    show unfields (k :: r.map (·.1)) ((frame k b ++ fields r) ++ rest) = some (b :: r.map (·.2), rest)
    rw [List.append_assoc]
    simp only [unfields, hu, ih, Option.map_some]

theorem unfields_some : ∀ (ks d : List Nat) (bs : List (List Nat)) (rest : List Nat), (∀ x ∈ d, x < 256) →
    unfields ks d = some (bs, rest) → bs.length = ks.length ∧ d = fields (ks.zip bs) ++ rest
  | [], d, bs, rest, _, h => by
    simp only [unfields, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨rfl, rfl⟩
  | k :: ks, d, bs, rest, hd, h => by
    simp only [unfields] at h
    split at h
    · rename_i b r hu
      have hdr := unframe_some k d b r hd hu
      have hr : ∀ x ∈ r, x < 256 := fun x hx => hd x (by rw [hdr]; simp [hx])
      cases hp : unfields ks r with
      | none => rw [hp] at h; cases h
      | some p =>
        rw [hp] at h
        simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨h1, h2⟩ := unfields_some ks r p.1 p.2 hr hp
        refine ⟨by simp [h1], ?_⟩
        rw [hdr, h2]
        simp [fields, List.append_assoc]
    · cases h

/-! ## 扩展 -/

def extsW : List (Nat × List Nat) → List Nat
  | [] => []
  | (t, d) :: r => be 2 t ++ (frame 2 d ++ extsW r)

/-- 读到数据用完为止；f 是最多读几个（每个扩展至少 4 字节，给数据长度就够） -/
def extsP : Nat → List Nat → Option (List (Nat × List Nat))
  | _, [] => some []
  | 0, _ :: _ => none
  | f + 1, a :: b :: r =>
    match unframe 2 r with
    | some (d, r') => (extsP f r').map ((a * 256 + b, d) :: ·)
    | none => none
  | _ + 1, [_] => none

def extOk (e : Nat × List Nat) : Prop := e.1 < 65536 ∧ e.2.length < 65536

theorem extsW_len : ∀ es : List (Nat × List Nat), 4 * es.length ≤ (extsW es).length
  | [] => by simp [extsW]
  | (t, d) :: r => by
    have ih := extsW_len r
    simp only [extsW, frame, List.length_append, be_len, List.length_cons]
    omega

theorem extsP_extsW : ∀ (es : List (Nat × List Nat)) (f : Nat), es.length ≤ f → (∀ e ∈ es, extOk e) →
    extsP f (extsW es) = some es
  | [], f, _, _ => by cases f <;> rfl
  | (t, d) :: r, f, hf, h => by
    obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by simp only [List.length_cons] at hf; omega⟩
    have h1 : extOk (t, d) := h (t, d) (by simp)
    have hr : ∀ e ∈ r, extOk e := fun e he => h e (by simp [he])
    have hu : unframe 2 (frame 2 d ++ extsW r) = some (d, extsW r) :=
      unframe_frame 2 d _ (by rw [e2]; exact h1.2)
    have ih := extsP_extsW r g (by simp only [List.length_cons] at hf; omega) hr
    have ht : t / 256 * 256 + t % 256 = t := by omega
    show extsP (g + 1) (be 2 t ++ (frame 2 d ++ extsW r)) = _
    rw [be2 t h1.1]
    simp only [List.cons_append, List.nil_append, extsP, hu, ih, Option.map_some, ht]

theorem extsP_some : ∀ (f : Nat) (d : List Nat) (es : List (Nat × List Nat)), (∀ x ∈ d, x < 256) →
    extsP f d = some es → extsW es = d ∧ ∀ e ∈ es, extOk e
  | 0, [], es, _, h => by
    simp only [extsP, Option.some.injEq] at h
    subst h
    exact ⟨rfl, by simp⟩
  | _ + 1, [], es, _, h => by
    simp only [extsP, Option.some.injEq] at h
    subst h
    exact ⟨rfl, by simp⟩
  | 0, _ :: _, _, _, h => by simp [extsP] at h
  | _ + 1, [_], _, _, h => by simp [extsP] at h
  | f + 1, a :: b :: r, es, hd, h => by
    simp only [extsP] at h
    split at h
    · rename_i d r' hu
      have hr : ∀ x ∈ r, x < 256 := fun x hx => hd x (by simp [hx])
      have hrr := unframe_some 2 r d r' hr hu
      have hr' : ∀ x ∈ r', x < 256 := fun x hx => hr x (by rw [hrr]; simp [hx])
      cases hp : extsP f r' with
      | none => rw [hp] at h; cases h
      | some es' =>
        rw [hp] at h
        simp only [Option.map_some, Option.some.injEq] at h
        subst h
        obtain ⟨h1, h2⟩ := extsP_some f r' es' hr' hp
        have ha : a < 256 := hd a (by simp)
        have hb : b < 256 := hd b (by simp)
        have hdl : d.length < 65536 := by
          have hlt : unbe (r.take 2) < 256 ^ 2 := by
            have := dec_lt (r.take 2).reverse (fun x hx => hr x (List.mem_of_mem_take (List.mem_reverse.mp hx)))
            simp only [List.length_reverse] at this
            have hl : (r.take 2).length ≤ 2 := by rw [List.length_take]; omega
            exact Nat.lt_of_lt_of_le this (Nat.pow_le_pow_right (by decide) hl)
          have hbl : d.length = unbe (r.take 2) := by
            unfold unframe at hu
            split at hu
            · cases hu
            · split at hu
              · cases hu
              · simp only [Option.some.injEq, Prod.mk.injEq] at hu
                rw [← hu.1, List.length_take, List.length_drop]
                omega
          rw [hbl, ← e2]
          exact hlt
        have hab : be 2 (a * 256 + b) = [a, b] := by
          rw [be2 _ (by omega)]
          have x1 : (a * 256 + b) / 256 = a := by omega
          have x2 : (a * 256 + b) % 256 = b := by omega
          rw [x1, x2]
        refine ⟨?_, ?_⟩
        · show be 2 (a * 256 + b) ++ (frame 2 d ++ extsW es') = a :: b :: r
          rw [hab, h1, ← hrr]
          rfl
        · intro e he
          rcases List.mem_cons.mp he with rfl | he
          · exact ⟨by omega, hdl⟩
          · exact h2 e he
    · cases h

/-! ## ClientHello -/

def chFields (sid suites : List Nat) (exts : List (Nat × List Nat)) : List (Nat × List Nat) :=
  [(1, sid), (2, suites), (1, [0]), (2, extsW exts)]

def chW (rnd sid suites : List Nat) (exts : List (Nat × List Nat)) : List Nat :=
  3 :: 3 :: (rnd ++ fields (chFields sid suites exts))

def chP : List Nat → Option (List Nat × List Nat × List Nat × List (Nat × List Nat))
  | a :: b :: r =>
    if a = 3 ∧ b = 3 ∧ 32 ≤ r.length then
      match unfields [1, 2, 1, 2] (r.drop 32) with
      | some ([sid, suites, comp, eb], []) =>
        if comp = [0] then (extsP eb.length eb).map (fun es => (r.take 32, sid, suites, es)) else none
      | _ => none
    else none
  | _ => none

theorem chP_chW (rnd sid suites : List Nat) (exts : List (Nat × List Nat)) (hr : rnd.length = 32)
    (hs : sid.length < 256) (hc : suites.length < 65536) (he : ∀ e ∈ exts, extOk e)
    (hl : (extsW exts).length < 65536) : chP (chW rnd sid suites exts) = some (rnd, sid, suites, exts) := by
  have hf := unfields_fields (chFields sid suites exts) []
    (by
      intro p hp
      simp only [chFields, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl <;> dsimp only <;> (try simp only [e1, e2, List.length_cons, List.length_nil]) <;> omega)
  rw [List.append_nil] at hf
  have hk : (chFields sid suites exts).map (·.1) = [1, 2, 1, 2] := rfl
  have hb : (chFields sid suites exts).map (·.2) = [sid, suites, [0], extsW exts] := rfl
  rw [hk, hb] at hf
  have hlen : 32 ≤ (rnd ++ fields (chFields sid suites exts)).length := by simp [hr]
  have hx := extsP_extsW exts (extsW exts).length (by have := extsW_len exts; omega) he
  unfold chW
  simp only [chP, hlen, and_self, ↓reduceIte]
  rw [drop_app' _ _ _ hr, hf, take_app' _ _ _ hr]
  simp [hx]

theorem chP_some (d rnd sid suites : List Nat) (exts : List (Nat × List Nat)) (hd : ∀ x ∈ d, x < 256)
    (h : chP d = some (rnd, sid, suites, exts)) : d = chW rnd sid suites exts ∧ rnd.length = 32 := by
  match d, hd, h with
  | [], _, h => simp [chP] at h
  | [_], _, h => simp [chP] at h
  | a :: b :: r, hd, h =>
    simp only [chP] at h
    split at h
    · rename_i hc
      obtain ⟨rfl, rfl, hlen⟩ := hc
      have hr : ∀ x ∈ r.drop 32, x < 256 := fun x hx => hd x (by simp [List.mem_of_mem_drop hx])
      split at h
      · rename_i sid' suites' comp eb hu
        split at h
        · rename_i hcomp
          cases hp : extsP eb.length eb with
          | none => rw [hp] at h; cases h
          | some es =>
            rw [hp] at h
            simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl, rfl, rfl⟩ := h
            obtain ⟨_, h2⟩ := unfields_some _ _ _ _ hr hu
            have heb : ∀ x ∈ eb, x < 256 := fun x hx => hr x (by rw [h2]; simp [fields, frame, hx])
            obtain ⟨h3, _⟩ := extsP_some _ eb es heb hp
            subst hcomp
            refine ⟨?_, by simp; omega⟩
            show 3 :: 3 :: r = 3 :: 3 :: (r.take 32 ++ fields (chFields sid' suites' es))
            have e : fields (chFields sid' suites' es) = r.drop 32 := by
              rw [h2]
              simp [chFields, fields, h3]
            rw [e, List.take_append_drop]
        · cases h
      · cases h
    · cases h

/-! ## ServerHello -/

def shW (rnd sid : List Nat) (suite : Nat) (exts : List (Nat × List Nat)) : List Nat :=
  3 :: 3 :: (rnd ++ (frame 1 sid ++ (be 2 suite ++ (0 :: frame 2 (extsW exts)))))

def shP : List Nat → Option (List Nat × List Nat × Nat × List (Nat × List Nat))
  | a :: b :: r =>
    if a = 3 ∧ b = 3 ∧ 32 ≤ r.length then
      match unframe 1 (r.drop 32) with
      | some (sid, x :: y :: z :: r2) =>
        if z = 0 then
          match unframe 2 r2 with
          | some (eb, []) => (extsP eb.length eb).map (fun es => (r.take 32, sid, x * 256 + y, es))
          | _ => none
        else none
      | _ => none
    else none
  | _ => none

theorem shP_shW (rnd sid : List Nat) (suite : Nat) (exts : List (Nat × List Nat)) (hr : rnd.length = 32)
    (hs : sid.length < 256) (hc : suite < 65536) (he : ∀ e ∈ exts, extOk e)
    (hl : (extsW exts).length < 65536) : shP (shW rnd sid suite exts) = some (rnd, sid, suite, exts) := by
  have h1 : unframe 1 (frame 1 sid ++ (be 2 suite ++ (0 :: frame 2 (extsW exts)))) =
      some (sid, be 2 suite ++ (0 :: frame 2 (extsW exts))) := unframe_frame 1 sid _ (by rw [e1]; exact hs)
  have h2 : unframe 2 (frame 2 (extsW exts)) = some (extsW exts, []) := by
    have := unframe_frame 2 (extsW exts) [] (by rw [e2]; exact hl)
    rwa [List.append_nil] at this
  have hlen : 32 ≤ (rnd ++ (frame 1 sid ++ (be 2 suite ++ (0 :: frame 2 (extsW exts))))).length := by simp [hr]
  have hx := extsP_extsW exts (extsW exts).length (by have := extsW_len exts; omega) he
  have hsu : suite / 256 * 256 + suite % 256 = suite := by omega
  unfold shW
  simp only [shP, hlen, and_self, ↓reduceIte]
  rw [drop_app' _ _ _ hr, h1, be2 suite hc, take_app' _ _ _ hr]
  simp only [List.cons_append, List.nil_append]
  simp [h2, hx, hsu]

theorem shP_some (d rnd sid : List Nat) (suite : Nat) (exts : List (Nat × List Nat)) (hd : ∀ x ∈ d, x < 256)
    (h : shP d = some (rnd, sid, suite, exts)) : d = shW rnd sid suite exts ∧ rnd.length = 32 := by
  match d, hd, h with
  | [], _, h => simp [shP] at h
  | [_], _, h => simp [shP] at h
  | a :: b :: r, hd, h =>
    simp only [shP] at h
    split at h
    · rename_i hc
      obtain ⟨rfl, rfl, hlen⟩ := hc
      have hr : ∀ x ∈ r.drop 32, x < 256 := fun x hx => hd x (by simp [List.mem_of_mem_drop hx])
      split at h
      · rename_i sid' x y z r2 hu
        have hq := unframe_some 1 _ _ _ hr hu
        have hxy : ∀ v ∈ x :: y :: z :: r2, v < 256 := fun v hv => hr v (by rw [hq]; simp [hv])
        split at h
        · rename_i hz
          subst hz
          split at h
          · rename_i eb hu2
            have hr2 : ∀ v ∈ r2, v < 256 := fun v hv => hxy v (by simp [hv])
            have hq2 := unframe_some 2 _ _ _ hr2 hu2
            cases hp : extsP eb.length eb with
            | none => rw [hp] at h; cases h
            | some es =>
              rw [hp] at h
              simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl, rfl, rfl⟩ := h
              have heb : ∀ v ∈ eb, v < 256 := fun v hv => hr2 v (by rw [hq2]; simp [frame, hv])
              obtain ⟨h3, _⟩ := extsP_some _ eb es heb hp
              have hxl : x < 256 := hxy x (by simp)
              have hyl : y < 256 := hxy y (by simp)
              have hab : be 2 (x * 256 + y) = [x, y] := by
                rw [be2 _ (by omega)]
                have x1 : (x * 256 + y) / 256 = x := by omega
                have x2 : (x * 256 + y) % 256 = y := by omega
                rw [x1, x2]
              refine ⟨?_, by simp; omega⟩
              show 3 :: 3 :: r = 3 :: 3 :: (r.take 32 ++ (frame 1 sid' ++ (be 2 (x * 256 + y) ++ (0 :: frame 2 (extsW es)))))
              rw [hab, h3]
              have e : frame 1 sid' ++ ([x, y] ++ (0 :: frame 2 eb)) = r.drop 32 := by
                rw [hq, hq2, List.append_nil]
                rfl
              rw [e, List.take_append_drop]
          · cases h
        · cases h
      · cases h
    · cases h

/-! ## 例子 -/

-- RFC 8448 第 3 节的 ServerHello（去掉 4 字节的握手消息头）：随机数、空的 session_id、0x1301、两个扩展
#guard (shP (SH.drop 4)).map (fun p => (p.2.2.1, p.2.2.2.map (·.1))) == some (0x1301, [51, 43])
#guard (shP (SH.drop 4)).map (fun p => shW p.1 p.2.1 p.2.2.1 p.2.2.2) == some (SH.drop 4)
-- ClientHello：三个套件、9 个扩展；写回去和原来一样
#guard (chP (CH.drop 4)).map (fun p => (p.2.2.1, p.2.2.2.length)) == some ([0x13, 0x01, 0x13, 0x03, 0x13, 0x02], 9)
#guard (chP (CH.drop 4)).map (fun p => chW p.1 p.2.1 p.2.2.1 p.2.2.2) == some (CH.drop 4)
#guard chP [3, 3] == none
#guard shP ((SH.drop 4).take 60) == none

end Hello
end Lark
