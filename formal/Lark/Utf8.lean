/-
标准库的证明 · UTF-8（std/utf8.lark）

照着 std/utf8.lark 写一份（字节串写成 List Nat，循环写成带燃料的递归，燃料 = 长度就够，因为每步至少前进一个字节），证明：

- `code_points_valid`：code_points 给出的每个码点都合法（不超过 U+10FFFF、不在代理区），所以交给 from_code_point 不会 panic。
  写这一条时发现原来的 utf8.lark 不满足：C3 41 会被解成一个字符 U+00C1（41 被吞掉），C0 80 解成 NUL，
  ED A0 80 解成代理区的 0xD800，F7 BF BF BF 解成 0x1FFFFF。现在照 Go 改成：不合法的地方每次一个字节，码点 U+FFFD。
- `chars_concat`：chars 切出来的字符拼回去就是原来的字节串，不管合不合法（一个字节也不丢、不重复）。
- `decode_encode`：合法码点编码以后再解，得到原来的码点，而且编码结果是合法的 UTF-8。
- `encode_decode`：合法的 UTF-8 解成码点再逐个编码、拼起来，得到原来的字节串。

valid_len 在 Lark 里按首字节查长度、再查第二个字节的范围 [lo, hi]；这里按首字节的四个区间分开写，
lo / hi 写成 (b0 ≠ E0 ∨ A0 ≤ b1) 这样的条件，两种写法逐字节等价。
-/

namespace Lark
namespace Utf8

/-- 从开头起的合法字符占几个字节；不合法（形状不对、被截断、过长编码、代理区、超过 U+10FFFF）时是 0 -/
def validLen : List Nat → Nat
  | [] => 0
  | b0 :: r =>
    if b0 < 0x80 then 1
    else if 0xC2 ≤ b0 ∧ b0 ≤ 0xDF then
      match r with
      | b1 :: _ => if 0x80 ≤ b1 ∧ b1 ≤ 0xBF then 2 else 0
      | [] => 0
    else if 0xE0 ≤ b0 ∧ b0 ≤ 0xEF then
      match r with
      | b1 :: b2 :: _ =>
        if 0x80 ≤ b1 ∧ b1 ≤ 0xBF ∧ (b0 ≠ 0xE0 ∨ 0xA0 ≤ b1) ∧ (b0 ≠ 0xED ∨ b1 ≤ 0x9F) ∧
          0x80 ≤ b2 ∧ b2 ≤ 0xBF then 3 else 0
      | _ => 0
    else if 0xF0 ≤ b0 ∧ b0 ≤ 0xF4 then
      match r with
      | b1 :: b2 :: b3 :: _ =>
        if 0x80 ≤ b1 ∧ b1 ≤ 0xBF ∧ (b0 ≠ 0xF0 ∨ 0x90 ≤ b1) ∧ (b0 ≠ 0xF4 ∨ b1 ≤ 0x8F) ∧
          0x80 ≤ b2 ∧ b2 ≤ 0xBF ∧ 0x80 ≤ b3 ∧ b3 ≤ 0xBF then 4 else 0
      | _ => 0
    else 0

/-- 一个字符的长度：不合法时算一个字节 -/
def lenAt (s : List Nat) : Nat := if validLen s = 0 then 1 else validLen s

def byteAt (s : List Nat) (i : Nat) : Nat := s.getD i 0

/-- 开头那个字符的码点：不合法时是 U+FFFD -/
def codeAt (s : List Nat) : Nat :=
  let k := validLen s
  let b := byteAt s
  if k = 1 then b 0
  else if k = 2 then b 0 % 32 * 64 + b 1 % 64
  else if k = 3 then b 0 % 16 * 4096 + b 1 % 64 * 64 + b 2 % 64
  else if k = 4 then b 0 % 8 * 262144 + b 1 % 64 * 4096 + b 2 % 64 * 64 + b 3 % 64
  else 0xFFFD

def cpsF : Nat → List Nat → List Nat
  | 0, _ => []
  | _ + 1, [] => []
  | n + 1, b :: r => codeAt (b :: r) :: cpsF n ((b :: r).drop (lenAt (b :: r)))

def charsF : Nat → List Nat → List (List Nat)
  | 0, _ => []
  | _ + 1, [] => []
  | n + 1, b :: r => (b :: r).take (lenAt (b :: r)) :: charsF n ((b :: r).drop (lenAt (b :: r)))

def validF : Nat → List Nat → Bool
  | 0, _ => true
  | _ + 1, [] => true
  | n + 1, b :: r => validLen (b :: r) != 0 && validF n ((b :: r).drop (validLen (b :: r)))

def codePoints (s : List Nat) : List Nat := cpsF s.length s
def chars (s : List Nat) : List (List Nat) := charsF s.length s
def isValid (s : List Nat) : Bool := validF s.length s

/-- from_code_point（合法码点的部分；不合法的码点 Lark 里 panic） -/
def enc (cp : Nat) : List Nat :=
  if cp < 128 then [cp]
  else if cp < 2048 then [192 + cp / 64, 128 + cp % 64]
  else if cp < 65536 then [224 + cp / 4096, 128 + cp / 64 % 64, 128 + cp % 64]
  else [240 + cp / 262144, 128 + cp / 4096 % 64, 128 + cp / 64 % 64, 128 + cp % 64]

/-- from_code_point 不 panic 的码点 -/
def ValidCP (cp : Nat) : Prop := cp ≤ 1114111 ∧ ¬(55296 ≤ cp ∧ cp ≤ 57343)

/-- join(chars, "") -/
def joinAll : List (List Nat) → List Nat
  | [] => []
  | c :: cs => c ++ joinAll cs

/-- 逐个 from_code_point 再拼起来 -/
def encAll : List Nat → List Nat
  | [] => []
  | c :: cs => enc c ++ encAll cs

/-! ## 例子：和 tests/unit/utf8.lark 对上 -/

example : codePoints [0xE4, 0xB8, 0xAD, 0x61] = [20013, 97] := by decide
example : codePoints [0xC3, 0x41] = [0xFFFD, 0x41] := by decide
example : codePoints [0xC0, 0x80] = [0xFFFD, 0xFFFD] := by decide
example : codePoints [0xED, 0xA0, 0x80] = [0xFFFD, 0xFFFD, 0xFFFD] := by decide
example : codePoints [0xF7, 0xBF, 0xBF, 0xBF] = [0xFFFD, 0xFFFD, 0xFFFD, 0xFFFD] := by decide
example : chars [0xC3, 0x41] = [[0xC3], [0x41]] := by decide
example : isValid [0xED, 0x9F, 0xBF] = true := by decide
example : isValid [0xF4, 0x90, 0x80, 0x80] = false := by decide

/-! ## validLen 不是 0 时，开头的字节是什么样 -/

theorem vl_inv (s : List Nat) :
    validLen s = 0 ∨
    (∃ a r, s = a :: r ∧ validLen s = 1 ∧ a < 0x80) ∨
    (∃ a b r, s = a :: b :: r ∧ validLen s = 2 ∧ 0xC2 ≤ a ∧ a ≤ 0xDF ∧ 0x80 ≤ b ∧ b ≤ 0xBF) ∨
    (∃ a b c r, s = a :: b :: c :: r ∧ validLen s = 3 ∧ 0xE0 ≤ a ∧ a ≤ 0xEF ∧
      0x80 ≤ b ∧ b ≤ 0xBF ∧ (a ≠ 0xE0 ∨ 0xA0 ≤ b) ∧ (a ≠ 0xED ∨ b ≤ 0x9F) ∧ 0x80 ≤ c ∧ c ≤ 0xBF) ∨
    (∃ a b c d r, s = a :: b :: c :: d :: r ∧ validLen s = 4 ∧ 0xF0 ≤ a ∧ a ≤ 0xF4 ∧
      0x80 ≤ b ∧ b ≤ 0xBF ∧ (a ≠ 0xF0 ∨ 0x90 ≤ b) ∧ (a ≠ 0xF4 ∨ b ≤ 0x8F) ∧
      0x80 ≤ c ∧ c ≤ 0xBF ∧ 0x80 ≤ d ∧ d ≤ 0xBF) := by
  generalize hk : validLen s = k
  rcases s with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, r⟩⟩⟩⟩
  all_goals
    simp only [validLen] at hk
    repeat' split at hk
    all_goals
      first
        | (left; omega)
        | (right; left; exact ⟨_, _, rfl, by omega, by omega⟩)
        | (right; right; left; exact ⟨_, _, _, rfl, by omega, by omega⟩)
        | (right; right; right; left; exact ⟨_, _, _, _, rfl, by omega, by omega⟩)
        | (right; right; right; right; exact ⟨_, _, _, _, _, rfl, by omega, by omega⟩)

theorem code0 {s : List Nat} (h : validLen s = 0) : codeAt s = 0xFFFD := by
  simp [codeAt, h]

theorem code1 {a : Nat} {r : List Nat} (h : validLen (a :: r) = 1) : codeAt (a :: r) = a := by
  simp [codeAt, byteAt, h]

theorem code2 {a b : Nat} {r : List Nat} (h : validLen (a :: b :: r) = 2) :
    codeAt (a :: b :: r) = a % 32 * 64 + b % 64 := by
  simp [codeAt, byteAt, h]

theorem code3 {a b c : Nat} {r : List Nat} (h : validLen (a :: b :: c :: r) = 3) :
    codeAt (a :: b :: c :: r) = a % 16 * 4096 + b % 64 * 64 + c % 64 := by
  simp [codeAt, byteAt, h]

theorem code4 {a b c d : Nat} {r : List Nat} (h : validLen (a :: b :: c :: d :: r) = 4) :
    codeAt (a :: b :: c :: d :: r) = a % 8 * 262144 + b % 64 * 4096 + c % 64 * 64 + d % 64 := by
  simp [codeAt, byteAt, h]

theorem lenAt_pos (s : List Nat) : 0 < lenAt s := by
  unfold lenAt
  split <;> omega

/-! ## code_points 给出的码点都合法 -/

theorem codeAt_valid (s : List Nat) : ValidCP (codeAt s) := by
  unfold ValidCP
  rcases vl_inv s with h | ⟨a, r, rfl, h, h1⟩ | ⟨a, b, r, rfl, h, h1⟩ | ⟨a, b, c, r, rfl, h, h1⟩ |
      ⟨a, b, c, d, r, rfl, h, h1⟩
  · rw [code0 h]; omega
  · rw [code1 h]; omega
  · rw [code2 h]; omega
  · rw [code3 h]; omega
  · rw [code4 h]; omega

theorem cpsF_valid : ∀ (n : Nat) (s : List Nat), ∀ cp ∈ cpsF n s, ValidCP cp
  | 0, _, cp, h => by simp [cpsF] at h
  | _ + 1, [], cp, h => by simp [cpsF] at h
  | n + 1, b :: r, cp, h => by
    simp only [cpsF, List.mem_cons] at h
    rcases h with e | h
    · rw [e]; exact codeAt_valid _
    · exact cpsF_valid n _ cp h

theorem code_points_valid (s : List Nat) : ∀ cp ∈ codePoints s, ValidCP cp :=
  cpsF_valid _ _

/-! ## chars 切出来的拼回去就是原来的字节 -/

theorem charsF_concat : ∀ (n : Nat) (s : List Nat), s.length ≤ n → joinAll (charsF n s) = s
  | 0, [], _ => rfl
  | 0, _ :: _, h => by simp at h
  | _ + 1, [], _ => rfl
  | n + 1, b :: r, h => by
    have hp : 0 < lenAt (b :: r) := lenAt_pos _
    have ih := charsF_concat n ((b :: r).drop (lenAt (b :: r)))
      (by simp only [List.length_drop, List.length_cons] at h ⊢; omega)
    simp only [charsF, joinAll, ih, List.take_append_drop]

theorem chars_concat (s : List Nat) : joinAll (chars s) = s :=
  charsF_concat _ _ (Nat.le_refl _)

/-! ## 合法码点：编码再解码 -/

theorem enc_ok (cp : Nat) (h : ValidCP cp) :
    validLen (enc cp) = (enc cp).length ∧ codeAt (enc cp) = cp := by
  unfold ValidCP at h
  by_cases h1 : cp < 128
  · have he : enc cp = [cp] := by unfold enc; rw [ite_eq_left h1]
    have hv : validLen [cp] = 1 := by simp only [validLen]; (repeat' split) <;> omega
    rw [he, code1 hv, hv]; exact ⟨rfl, rfl⟩
  by_cases h2 : cp < 2048
  · have he : enc cp = [192 + cp / 64, 128 + cp % 64] := by
      unfold enc; rw [ite_eq_right h1, ite_eq_left h2]
    have hv : validLen [192 + cp / 64, 128 + cp % 64] = 2 := by
      simp only [validLen]; (repeat' split) <;> omega
    rw [he, code2 hv, hv]; exact ⟨rfl, by omega⟩
  by_cases h3 : cp < 65536
  · have he : enc cp = [224 + cp / 4096, 128 + cp / 64 % 64, 128 + cp % 64] := by
      unfold enc; rw [ite_eq_right h1, ite_eq_right h2, ite_eq_left h3]
    have hv : validLen [224 + cp / 4096, 128 + cp / 64 % 64, 128 + cp % 64] = 3 := by
      simp only [validLen]; (repeat' split) <;> omega
    rw [he, code3 hv, hv]; exact ⟨rfl, by omega⟩
  · have he : enc cp = [240 + cp / 262144, 128 + cp / 4096 % 64, 128 + cp / 64 % 64, 128 + cp % 64] := by
      unfold enc; rw [ite_eq_right h1, ite_eq_right h2, ite_eq_right h3]
    have hv : validLen [240 + cp / 262144, 128 + cp / 4096 % 64, 128 + cp / 64 % 64, 128 + cp % 64] = 4 := by
      simp only [validLen]; (repeat' split) <;> omega
    rw [he, code4 hv, hv]; exact ⟨rfl, by omega⟩

theorem cpsF_nil (n : Nat) : cpsF n [] = [] := by cases n <;> rfl

theorem validF_nil (n : Nat) : validF n [] = true := by cases n <;> rfl

/-- 整个字节串正好是一个合法字符 -/
theorem one_char {s : List Nat} (h : validLen s = s.length) (h0 : s ≠ []) :
    codePoints s = [codeAt s] ∧ isValid s = true := by
  cases s with
  | nil => exact absurd rfl h0
  | cons b r =>
    have hl : lenAt (b :: r) = r.length + 1 := by simp [lenAt, h]
    have hd : (b :: r).drop (r.length + 1) = [] := by simp
    constructor
    · simp [codePoints, cpsF, hl, hd, cpsF_nil]
    · simp [isValid, validF, h, hd, validF_nil]

theorem decode_encode (cp : Nat) (h : ValidCP cp) :
    codePoints (enc cp) = [cp] ∧ isValid (enc cp) = true := by
  obtain ⟨hv, hc⟩ := enc_ok cp h
  have hne : enc cp ≠ [] := by unfold enc; (repeat' split) <;> simp
  obtain ⟨h1, h2⟩ := one_char hv hne
  rw [hc] at h1
  exact ⟨h1, h2⟩

/-! ## 合法的 UTF-8：解码再编码 -/

/-- 开头是合法字符时，把它的码点编码回去就是开头那几个字节 -/
theorem char_enc (s : List Nat) (h0 : validLen s ≠ 0) : enc (codeAt s) = s.take (validLen s) := by
  rcases vl_inv s with h | ⟨a, r, rfl, h, h1⟩ | ⟨a, b, r, rfl, h, h1⟩ | ⟨a, b, c, r, rfl, h, h1⟩ |
      ⟨a, b, c, d, r, rfl, h, h1⟩
  · exact absurd h h0
  · rw [code1 h, h]
    show enc a = [a]
    unfold enc
    rw [ite_eq_left h1]
  · rw [code2 h, h]
    show enc _ = [a, b]
    generalize hx : a % 32 * 64 + b % 64 = x
    have e1 : ¬ x < 128 := by omega
    have e2 : x < 2048 := by omega
    unfold enc
    rw [ite_eq_right e1, ite_eq_left e2]
    have f1 : 192 + x / 64 = a := by omega
    have f2 : 128 + x % 64 = b := by omega
    rw [f1, f2]
  · rw [code3 h, h]
    show enc _ = [a, b, c]
    generalize hx : a % 16 * 4096 + b % 64 * 64 + c % 64 = x
    have e1 : ¬ x < 128 := by omega
    have e2 : ¬ x < 2048 := by omega
    have e3 : x < 65536 := by omega
    unfold enc
    rw [ite_eq_right e1, ite_eq_right e2, ite_eq_left e3]
    have f1 : 224 + x / 4096 = a := by omega
    have f2 : 128 + x / 64 % 64 = b := by omega
    have f3 : 128 + x % 64 = c := by omega
    rw [f1, f2, f3]
  · rw [code4 h, h]
    show enc _ = [a, b, c, d]
    generalize hx : a % 8 * 262144 + b % 64 * 4096 + c % 64 * 64 + d % 64 = x
    have e1 : ¬ x < 128 := by omega
    have e2 : ¬ x < 2048 := by omega
    have e3 : ¬ x < 65536 := by omega
    unfold enc
    rw [ite_eq_right e1, ite_eq_right e2, ite_eq_right e3]
    have f1 : 240 + x / 262144 = a := by omega
    have f2 : 128 + x / 4096 % 64 = b := by omega
    have f3 : 128 + x / 64 % 64 = c := by omega
    have f4 : 128 + x % 64 = d := by omega
    rw [f1, f2, f3, f4]

theorem cpsF_enc : ∀ (n : Nat) (s : List Nat), s.length ≤ n → validF n s = true →
    encAll (cpsF n s) = s
  | 0, [], _, _ => rfl
  | 0, _ :: _, h, _ => by simp at h
  | _ + 1, [], _, _ => rfl
  | n + 1, b :: r, h, hv => by
    by_cases h0 : validLen (b :: r) = 0
    · simp [validF, h0] at hv
    · have hv2 : validF n ((b :: r).drop (validLen (b :: r))) = true := by
        simpa [validF, h0] using hv
      have hl : lenAt (b :: r) = validLen (b :: r) := by simp [lenAt, h0]
      have hp : 0 < validLen (b :: r) := Nat.pos_of_ne_zero h0
      have ih := cpsF_enc n _ (by simp only [List.length_drop, List.length_cons] at h ⊢; omega) hv2
      simp only [cpsF, encAll, hl, ih, char_enc (b :: r) h0, List.take_append_drop]

theorem encode_decode (s : List Nat) (h : isValid s = true) : encAll (codePoints s) = s :=
  cpsF_enc _ _ (Nat.le_refl _) h

end Utf8
end Lark
