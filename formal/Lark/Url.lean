/-
标准库的证明 · URL 查询串（std/url.lark，先证明再写库）

照 Go 的 net/url：QueryEscape / QueryUnescape / ParseQuery / Values.Encode（Lark 里叫
escape_query / unescape_query / parse_query / format_query）。字符串记成字节的列表；Lean 的 none 是 Lark 的 Err。

- escape：字母、数字和 -._~ 不变，空格写成 +，别的字节写成 %XX（大写）。
  写出来的只有这些字节和 % +（`esc_safe`），所以没有 & = ;，可以直接放进查询串。
- unescape：%XX 解码（大小写都行），+ 是空格；% 后面不是两个十六进制数字时出错。
  `unesc_esc`：任意字节串 escape 再 unescape 回到原样。
- format_query：每对写成 k=v（两边 escape），用 & 连起来；parse_query：按 & 切开、跳过空的段，
  每段在第一个 = 处分成键和值（没有 = 时值是空串），两边 unescape；有 ; 时出错（照 Go 1.17）。
  `parse_format`：任意键值对列表（可以有重复的键、空串）format 再 parse 回到原样，顺序不变。
-/

namespace Lark
namespace Url

/-- 每个都是字节 -/
def Bytes (s : List Nat) : Prop := ∀ c ∈ s, c < 256

/-- 不用编码的字节：A-Z a-z 0-9 - . _ ~ -/
def unres (c : Nat) : Bool :=
  decide ((65 ≤ c ∧ c ≤ 90) ∨ (97 ≤ c ∧ c ≤ 122) ∨ (48 ≤ c ∧ c ≤ 57) ∨ c = 45 ∨ c = 46 ∨ c = 95 ∨ c = 126)

/-- 0..15 写成十六进制数字（大写） -/
def hexd (d : Nat) : Nat := if d < 10 then 48 + d else 55 + d

/-- 十六进制数字的值（大小写都行） -/
def hexv (c : Nat) : Option Nat :=
  if 48 ≤ c ∧ c ≤ 57 then some (c - 48)
  else if 65 ≤ c ∧ c ≤ 70 then some (c - 55)
  else if 97 ≤ c ∧ c ≤ 102 then some (c - 87)
  else none

def esc1 (c : Nat) : List Nat :=
  if unres c = true then [c] else if c = 32 then [43] else [37, hexd (c / 16), hexd (c % 16)]

def escape : List Nat → List Nat
  | [] => []
  | c :: r => esc1 c ++ escape r

def unesc : List Nat → Option (List Nat)
  | [] => some []
  | c :: r =>
    if c = 37 then
      match r with
      | a :: b :: r' =>
        match hexv a, hexv b with
        | some x, some y => (unesc r').map (fun t => (16 * x + y) :: t)
        | _, _ => none
      | _ => none
    else (unesc r).map (fun t => (if c = 43 then 32 else c) :: t)

-- escape_query("a b&=") = "a+b%26%3D"
#guard escape [97, 32, 38, 61] == [97, 43, 37, 50, 54, 37, 51, 68]
#guard unesc [97, 43, 37, 50, 54, 37, 51, 100] == some [97, 32, 38, 61]
#guard unesc [37, 52] == none

/-! ## escape 再 unescape 回到原样 -/

theorem hexv_hexd (d : Nat) (h : d < 16) : hexv (hexd d) = some d := by
  by_cases h1 : d < 10
  · simp only [hexd, h1, ↓reduceIte, hexv]
    repeat' split
    all_goals first | rfl | omega | (simp only [Option.some.injEq]; omega)
  · simp only [hexd, h1, ↓reduceIte, hexv]
    repeat' split
    all_goals first | rfl | omega | (simp only [Option.some.injEq]; omega)

theorem hexd_unres (d : Nat) (h : d < 16) : unres (hexd d) = true := by
  by_cases h1 : d < 10 <;> simp only [hexd, h1, ↓reduceIte, unres, decide_eq_true_eq] <;> omega

/-- 不是 % 的字节：+ 换成空格，别的原样，接着解后面的 -/
theorem unesc_plain (c : Nat) (r : List Nat) (h : c ≠ 37) :
    unesc (c :: r) = (unesc r).map (fun t => (if c = 43 then 32 else c) :: t) := by
  rw [unesc.eq_def]
  exact ite_eq_right h

theorem unesc_esc : ∀ s : List Nat, Bytes s → unesc (escape s) = some s
  | [], _ => by simp [escape, unesc]
  | c :: r, hs => by
    have hc := hs c (List.mem_cons_self ..)
    have ih := unesc_esc r (fun x hx => hs x (List.mem_cons_of_mem _ hx))
    by_cases h1 : unres c = true
    · have hn : c ≠ 37 ∧ c ≠ 43 := by simp only [unres, decide_eq_true_eq] at h1; omega
      have e : esc1 c = [c] := ite_eq_left h1
      simp only [escape, e, List.cons_append, List.nil_append]
      rw [unesc_plain c _ hn.1, ih]
      simp [hn.2]
    · by_cases h2 : c = 32
      · subst h2
        have e : esc1 32 = [43] := rfl
        have h43 : (43 : Nat) ≠ 37 := by decide
        simp only [escape, e, List.cons_append, List.nil_append]
        rw [unesc_plain 43 _ h43, ih]
        simp
      · have e : esc1 c = [37, hexd (c / 16), hexd (c % 16)] := by
          unfold esc1
          rw [ite_eq_right h1, ite_eq_right h2]
        have e1 := hexv_hexd (c / 16) (by omega)
        have e2 := hexv_hexd (c % 16) (by omega)
        have e3 : 16 * (c / 16) + c % 16 = c := by omega
        simp only [escape, e, List.cons_append, List.nil_append, unesc, ↓reduceIte, e1, e2]
        rw [ih]
        simp [e3]

/-- escape 写出来的只有不用编码的字节和 % + -/
theorem esc_safe : ∀ s : List Nat, Bytes s → ∀ c ∈ escape s, unres c = true ∨ c = 37 ∨ c = 43
  | [], _, c, h => by simp [escape] at h
  | x :: r, hs, c, h => by
    have hx := hs x (List.mem_cons_self ..)
    simp only [escape, esc1, List.mem_append] at h
    rcases h with h | h
    · split at h
      · rename_i hu
        simp at h
        rw [h]
        exact Or.inl hu
      · split at h
        · simp at h
          exact Or.inr (Or.inr h)
        · simp at h
          rcases h with h | h | h
          · exact Or.inr (Or.inl h)
          · rw [h]; exact Or.inl (hexd_unres (x / 16) (by omega))
          · rw [h]; exact Or.inl (hexd_unres (x % 16) (by omega))
    · exact esc_safe r (fun y hy => hs y (List.mem_cons_of_mem _ hy)) c h

/-- 所以 escape 写出来的没有 & = ; -/
theorem esc_not (s : List Nat) (hs : Bytes s) (c : Nat) (h : c ∈ escape s) : c ≠ 38 ∧ c ≠ 61 ∧ c ≠ 59 := by
  rcases esc_safe s hs c h with h | h | h
  · simp only [unres, decide_eq_true_eq] at h
    omega
  · omega
  · omega

/-! ## 按 & 切开、用 & 连起来、在第一个 = 处分开 -/

/-- 和 str.split 一样：保留空的段，没有分隔符时是一整段 -/
def splitOn (sep : Nat) : List Nat → List (List Nat)
  | [] => [[]]
  | c :: r =>
    if c = sep then [] :: splitOn sep r
    else match splitOn sep r with
      | [] => [[c]]
      | x :: xs => (c :: x) :: xs

/-- 和 join 一样 -/
def joinL (sep : Nat) : List (List Nat) → List Nat
  | [] => []
  | [x] => x
  | x :: y :: r => x ++ sep :: joinL sep (y :: r)

/-- 在第一个 =（61）处分成两半；没有 = 时第二半是空的 -/
def cutEq : List Nat → List Nat × List Nat
  | [] => ([], [])
  | c :: r => if c = 61 then ([], r) else (c :: (cutEq r).1, (cutEq r).2)

theorem split_free (sep : Nat) : ∀ x : List Nat, sep ∉ x → splitOn sep x = [x]
  | [], _ => rfl
  | c :: r, h => by
    have hc : ¬c = sep := fun e => h (by simp [e])
    have ih := split_free sep r (fun m => h (List.mem_cons_of_mem _ m))
    simp only [splitOn, hc, ↓reduceIte, ih]

theorem split_app (sep : Nat) (y : List Nat) : ∀ x : List Nat, sep ∉ x → splitOn sep (x ++ sep :: y) = x :: splitOn sep y
  | [], _ => by simp [splitOn]
  | c :: r, h => by
    have hc : ¬c = sep := fun e => h (by simp [e])
    have ih := split_app sep y r (fun m => h (List.mem_cons_of_mem _ m))
    simp only [List.cons_append, splitOn, hc, ↓reduceIte, ih]

theorem split_join (sep : Nat) : ∀ xs : List (List Nat), xs ≠ [] → (∀ x ∈ xs, sep ∉ x) →
    splitOn sep (joinL sep xs) = xs
  | [], h, _ => absurd rfl h
  | [x], _, hx => split_free sep x (hx x (List.mem_singleton_self _))
  | x :: y :: r, _, hx => by
    simp only [joinL]
    rw [split_app sep _ x (hx x (List.mem_cons_self ..)),
      split_join sep (y :: r) (List.cons_ne_nil _ _) (fun z hz => hx z (List.mem_cons_of_mem _ hz))]

theorem mem_joinL (sep c : Nat) : ∀ xs : List (List Nat), c ∈ joinL sep xs → c = sep ∨ ∃ x ∈ xs, c ∈ x
  | [], h => by simp [joinL] at h
  | [x], h => Or.inr ⟨x, List.mem_singleton_self _, h⟩
  | x :: y :: r, h => by
    simp only [joinL, List.mem_append, List.mem_cons] at h
    rcases h with h | h | h
    · exact Or.inr ⟨x, List.mem_cons_self .., h⟩
    · exact Or.inl h
    · rcases mem_joinL sep c (y :: r) h with h | ⟨z, hz, hc⟩
      · exact Or.inl h
      · exact Or.inr ⟨z, List.mem_cons_of_mem _ hz, hc⟩

theorem cutEq_app (y : List Nat) : ∀ x : List Nat, 61 ∉ x → cutEq (x ++ 61 :: y) = (x, y)
  | [], _ => by simp [cutEq]
  | c :: r, h => by
    have hc : ¬c = 61 := fun e => h (by simp [e])
    simp only [List.cons_append, cutEq, hc, ↓reduceIte, cutEq_app y r (fun m => h (List.mem_cons_of_mem _ m))]

/-! ## format_query / parse_query -/

def fmtPair (p : List Nat × List Nat) : List Nat := escape p.1 ++ 61 :: escape p.2

def formatQ (ps : List (List Nat × List Nat)) : List Nat := joinL 38 (ps.map fmtPair)

def parsePart (p : List Nat) : Option (List Nat × List Nat) :=
  match unesc (cutEq p).1, unesc (cutEq p).2 with
  | some k, some v => some (k, v)
  | _, _ => none

/-- 跳过空的段 -/
def parseParts : List (List Nat) → Option (List (List Nat × List Nat))
  | [] => some []
  | x :: xs =>
    if x = [] then parseParts xs
    else match parsePart x, parseParts xs with
      | some p, some ps => some (p :: ps)
      | _, _ => none

/-- 有 ;（59）时出错，否则按 &（38）切开 -/
def parseQ (q : List Nat) : Option (List (List Nat × List Nat)) :=
  if 59 ∈ q then none else parseParts (splitOn 38 q)

-- parse_query("a=1&&b=%26&c") = [("a", "1"), ("b", "&"), ("c", "")]
#guard parseQ [97, 61, 49, 38, 38, 98, 61, 37, 50, 54, 38, 99] == some [([97], [49]), ([98], [38]), ([99], [])]
#guard parseQ [97, 59, 98] == none

theorem parsePart_fmt (k v : List Nat) (hk : Bytes k) (hv : Bytes v) : parsePart (fmtPair (k, v)) = some (k, v) := by
  have h61 : 61 ∉ escape k := fun m => (esc_not k hk 61 m).2.1 rfl
  unfold parsePart fmtPair
  simp only [cutEq_app _ _ h61, unesc_esc k hk, unesc_esc v hv]

theorem fmt_not (k v : List Nat) (hk : Bytes k) (hv : Bytes v) (c : Nat) (hc : c ∈ fmtPair (k, v)) :
    c ≠ 38 ∧ c ≠ 59 := by
  simp only [fmtPair, List.mem_append, List.mem_cons] at hc
  rcases hc with hc | hc | hc
  · have := esc_not k hk c hc
    omega
  · omega
  · have := esc_not v hv c hc
    omega

theorem parseParts_map : ∀ ps : List (List Nat × List Nat), (∀ p ∈ ps, Bytes p.1 ∧ Bytes p.2) →
    parseParts (ps.map fmtPair) = some ps
  | [], _ => rfl
  | (k, v) :: ps, h => by
    have hp := h (k, v) (List.mem_cons_self ..)
    have ne : fmtPair (k, v) ≠ [] := by simp [fmtPair]
    simp only [List.map_cons, parseParts, ne, ↓reduceIte, parsePart_fmt k v hp.1 hp.2,
      parseParts_map ps (fun p hp' => h p (List.mem_cons_of_mem _ hp'))]

/-- format_query 再 parse_query 回到原样（键值可以是任意字节串，可以重复、可以是空串） -/
theorem parse_format (ps : List (List Nat × List Nat)) (h : ∀ p ∈ ps, Bytes p.1 ∧ Bytes p.2) :
    parseQ (formatQ ps) = some ps := by
  have hx : ∀ x ∈ ps.map fmtPair, ∀ c ∈ x, c ≠ 38 ∧ c ≠ 59 := by
    intro x hx c hc
    obtain ⟨⟨k, v⟩, hp, e⟩ := List.mem_map.1 hx
    subst e
    exact fmt_not k v (h _ hp).1 (h _ hp).2 c hc
  have h59 : ¬59 ∈ formatQ ps := by
    intro m
    rcases mem_joinL 38 59 (ps.map fmtPair) m with e | ⟨x, hx', hc⟩
    · omega
    · exact (hx x hx' 59 hc).2 rfl
  unfold parseQ
  rw [ite_eq_right h59]
  cases ps with
  | nil => simp [formatQ, joinL, splitOn, parseParts]
  | cons p ps' =>
    unfold formatQ
    rw [split_join 38 ((p :: ps').map fmtPair) (by simp) (fun x hx' m => (hx x hx' 38 m).1 rfl)]
    exact parseParts_map _ h

end Url
end Lark
