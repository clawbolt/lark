/-
标准库的证明 · CSV（std/csv.lark）

照着 std/csv.lark 写一份：字节串写成 List Nat，字段是 List Nat，一行是字段的列表；错误信息不写，出错就是 none。
parse_sep 的主循环写成带燃料的递归（loop），每走一步至少吃掉一个字节，燃料给 长度 + 1。

要证的（分几步）：
- `field_fmt`：format_field 写出来的字段，后面跟着分隔符或换行时，parse 读回来的正好是原来的字段，停在分隔符或换行上。
- 每行至少一列、分隔符不是 \r \n " 时，parse(format(rows)) = rows（README 和 csv.lark 开头说的前提）。
-/

namespace Lark
namespace Csv

/-! ## 读：parse_sep -/

/-- 引号括起来的字段（开头的引号已经吃掉）：读到结束的引号，"" 是一个引号。返回字段和后面剩下的 -/
def qf (acc : List Nat) : List Nat → Option (List Nat × List Nat)
  | [] => none
  | c :: r =>
    if c = 34 then
      match r with
      | d :: r' => if d = 34 then qf (acc ++ [34]) r' else some (acc, r)
      | [] => some (acc, [])
    else qf (acc ++ [c]) r

/-- 结束的引号后面：\r 后面是 \n 或者结尾时跳过 \r；然后必须是分隔符、换行或结尾 -/
def afterQ (sep : Nat) (f r : List Nat) : Option (List Nat × List Nat) :=
  let r' := match r with
    | c :: t => if c = 13 ∧ (t = [] ∨ t.head? = some 10) then t else c :: t
    | [] => []
  match r' with
  | [] => some (f, [])
  | c :: t => if c = sep ∨ c = 10 then some (f, c :: t) else none

/-- 最后一个字节是不是 \r -/
def lastCR : List Nat → Bool
  | [] => false
  | [b] => b == 13
  | _ :: b :: r => lastCR (b :: r)

/-- 没括起来的字段：后面是 \n 或者结尾时去掉末尾的 \r -/
def strip (acc rest : List Nat) : List Nat :=
  if lastCR acc = true ∧ (rest = [] ∨ rest.head? = some 10) then acc.dropLast else acc

/-- 没括起来的字段：读到分隔符、换行或结尾；中间有引号是错误 -/
def uf (sep : Nat) (acc : List Nat) : List Nat → Option (List Nat × List Nat)
  | [] => some (strip acc [], [])
  | c :: r =>
    if c = sep ∨ c = 10 then some (strip acc (c :: r), c :: r)
    else if c = 34 then none
    else uf sep (acc ++ [c]) r

/-- 读一个字段：以引号开头时按括起来的读 -/
def field (sep : Nat) : List Nat → Option (List Nat × List Nat)
  | c :: r =>
    if c = 34 then
      match qf [] r with
      | none => none
      | some (f, r') => afterQ sep f r'
    else uf sep [] (c :: r)
  | [] => uf sep [] []

/-- parse_sep 的 for true 循环：row 是正在读的行，rows 是读完的行 -/
def loop (sep : Nat) : Nat → List (List Nat) → List (List (List Nat)) → List Nat →
    Option (List (List (List Nat)))
  | 0, _, _, _ => none
  | n + 1, row, rows, s =>
    match field sep s with
    | none => none
    | some (f, []) => some (rows ++ [row ++ [f]])
    | some (f, c :: t) =>
      if c = 10 then
        (if t = [] then some (rows ++ [row ++ [f]]) else loop sep n [] (rows ++ [row ++ [f]]) t)
      else loop sep n (row ++ [f]) rows t

def parse (sep : Nat) (s : List Nat) : Option (List (List (List Nat))) :=
  if s = [] then some [] else loop sep (s.length + 1) [] [] s

/-! ## 写：format_sep -/

/-- 含有分隔符、引号、\r 或 \n 时要括起来 -/
def need (sep : Nat) : List Nat → Bool
  | [] => false
  | b :: r => if b = sep ∨ b = 34 ∨ b = 10 ∨ b = 13 then true else need sep r

/-- 引号写成 "" -/
def esc : List Nat → List Nat
  | [] => []
  | b :: r => if b = 34 then 34 :: 34 :: esc r else b :: esc r

def fmtField (sep : Nat) (s : List Nat) : List Nat := if need sep s = true then 34 :: esc s ++ [34] else s

def fmtRow (sep : Nat) : List (List Nat) → List Nat
  | [] => []
  | [f] => fmtField sep f
  | f :: g :: fs => fmtField sep f ++ sep :: fmtRow sep (g :: fs)

def fmt (sep : Nat) : List (List (List Nat)) → List Nat
  | [] => []
  | r :: rs => fmtRow sep r ++ 10 :: fmt sep rs

/-! ## 例子：和 tests/unit/csv.lark 对上（, 是 44，a b c 是 97 98 99） -/

example : fmt 44 [[[97], [98, 44, 99]]] = [97, 44, 34, 98, 44, 99, 34, 10] := by decide
example : parse 44 [97, 44, 34, 98, 44, 99, 34, 10] = some [[[97], [98, 44, 99]]] := by decide
example : parse 44 [] = some [] := by decide
-- 空行是只有一个空字段的行
example : parse 44 [10] = some [[[]]] := by decide
-- \r\n 也是换行；最后一行没有换行也行
example : parse 44 [97, 13, 10, 98] = some [[[97]], [[98]]] := by decide
-- "" 是一个引号
example : parse 44 [34, 34, 34, 34, 10] = some [[[34]]] := by decide
-- 引号没有结束、没括起来的字段里有引号、结束的引号后面跟着别的
example : parse 44 [34, 97] = none := by decide
example : parse 44 [97, 34] = none := by decide
example : parse 44 [34, 97, 34, 98] = none := by decide

/-! ## 一个字段：写出来再读回去 -/

/-- 括起来的部分：esc f 后面是结束的引号，再后面不是引号 -/
theorem qf_esc (c : Nat) (hc : c ≠ 34) (t : List Nat) : ∀ (f acc : List Nat),
    qf acc (esc f ++ 34 :: c :: t) = some (acc ++ f, c :: t)
  | [], acc => by simp [esc, qf, hc]
  | b :: f, acc => by
    by_cases hb : b = 34
    · subst hb
      have ih := qf_esc c hc t f (acc ++ [34])
      simp [esc, qf, ih]
    · have ih := qf_esc c hc t f (acc ++ [b])
      simp only [esc, hb, ↓reduceIte, List.cons_append]
      first
        | (rw [qf, ite_eq_right hb, ih]; simp)
        | (simp only [qf, hb, ↓reduceIte, ih]; simp)
        | (unfold qf; simp [hb, ih])

theorem need_head {sep b : Nat} {f : List Nat} (h : need sep (b :: f) = false) :
    ¬(b = sep ∨ b = 34 ∨ b = 10 ∨ b = 13) ∧ need sep f = false := by
  have hb : ¬(b = sep ∨ b = 34 ∨ b = 10 ∨ b = 13) := by
    intro hb
    simp [need, hb] at h
  exact ⟨hb, by simpa [need, hb] using h⟩

theorem lastCR_plain {sep : Nat} : ∀ f : List Nat, need sep f = false → lastCR f = false
  | [], _ => rfl
  | [b], h => by
    have hb := (need_head h).1
    have : b ≠ 13 := by omega
    simp [lastCR, this]
  | _ :: b :: f, h => by
    simp only [lastCR]
    exact lastCR_plain (b :: f) (need_head h).2

theorem strip_plain {sep : Nat} {f : List Nat} (rest : List Nat) (h : need sep f = false) : strip f rest = f := by
  simp [strip, lastCR_plain f h]

/-- 没括起来的部分：读到分隔符或换行为止 -/
theorem uf_plain {sep c : Nat} (hc : c = sep ∨ c = 10) (t : List Nat) : ∀ (f acc : List Nat), need sep f = false →
    uf sep acc (f ++ c :: t) = some (strip (acc ++ f) (c :: t), c :: t)
  | [], acc, _ => by simp [uf, hc]
  | b :: f, acc, h => by
    obtain ⟨hb, hf⟩ := need_head h
    have ih := uf_plain hc t f (acc ++ [b]) hf
    have h1 : ¬(b = sep ∨ b = 10) := by omega
    have h2 : ¬b = 34 := by omega
    simp only [List.cons_append, uf, h1, h2, ↓reduceIte, ih, List.append_assoc, List.nil_append]

/-- format_field 写出来的字段，后面跟着分隔符或换行，读回来不变 -/
theorem field_fmt {sep c : Nat} (hs : sep ≠ 10 ∧ sep ≠ 13 ∧ sep ≠ 34) (hc : c = sep ∨ c = 10) (t f : List Nat) :
    field sep (fmtField sep f ++ c :: t) = some (f, c :: t) := by
  have hc34 : c ≠ 34 := by omega
  have hc13 : c ≠ 13 := by omega
  unfold fmtField
  by_cases hn : need sep f = true
  · rw [ite_eq_left hn]
    have e : (34 :: esc f) ++ [34] ++ c :: t = 34 :: (esc f ++ 34 :: c :: t) := by simp
    rw [e]
    simp [field, qf_esc c hc34 t f [], afterQ, hc13, hc]
  · have hn' : need sep f = false := by simpa using hn
    rw [ite_eq_right hn]
    cases f with
    | nil => simp [field, uf, hc, hc34, strip, lastCR]
    | cons b g =>
      have hb : b ≠ 34 := by
        intro hb
        simp [need, hb] at hn'
      simp only [List.cons_append, field, hb, ↓reduceIte]
      rw [← List.cons_append, uf_plain hc t (b :: g) [] hn', List.nil_append, strip_plain _ hn']

/-! ## 一行、整段：parse(format(rows)) = rows -/

theorem fmtRow_len (sep : Nat) : ∀ (f : List Nat) (fs : List (List Nat)), fs.length ≤ (fmtRow sep (f :: fs)).length
  | _, [] => Nat.zero_le _
  | f, g :: gs => by
    have ih := fmtRow_len sep g gs
    simp only [fmtRow, List.length_append, List.length_cons]
    omega

/-- 一行 f :: fs 写出来再接上换行：读完这一行，接着读后面的 t（t 是空的就结束） -/
theorem rowL {sep : Nat} (hs : sep ≠ 10 ∧ sep ≠ 13 ∧ sep ≠ 34) (t : List Nat) :
    ∀ (fs : List (List Nat)) (f : List Nat) (row : List (List Nat)) (acc : List (List (List Nat))) (n : Nat),
    fs.length < n →
    loop sep n row acc (fmtRow sep (f :: fs) ++ 10 :: t) =
      if t = [] then some (acc ++ [row ++ f :: fs])
      else loop sep (n - (fs.length + 1)) [] (acc ++ [row ++ f :: fs]) t
  | _, _, _, _, 0, h => absurd h (Nat.not_lt_zero _)
  | [], f, row, acc, n + 1, _ => by
    simp only [fmtRow]
    rw [loop, field_fmt hs (Or.inr rfl)]
    simp
  | g :: gs, f, row, acc, n + 1, hn => by
    have ih := rowL hs t gs g (row ++ [f]) acc n (by simp at hn; omega)
    simp only [fmtRow, List.append_assoc, List.cons_append]
    rw [loop, field_fmt hs (Or.inl rfl)]
    simp only [hs.1, ↓reduceIte]
    rw [ih]
    simp

theorem rowsL {sep : Nat} (hs : sep ≠ 10 ∧ sep ≠ 13 ∧ sep ≠ 34) :
    ∀ (rs : List (List (List Nat))) (acc : List (List (List Nat))) (n : Nat),
    rs ≠ [] → (∀ r ∈ rs, r ≠ []) → (fmt sep rs).length < n → loop sep n [] acc (fmt sep rs) = some (acc ++ rs)
  | [], _, _, h, _, _ => absurd rfl h
  | [] :: _, _, _, _, hr, _ => absurd rfl (hr [] (by simp))
  | (f :: fs) :: rs, acc, n, _, hr, hl => by
    have hlen := fmtRow_len sep f fs
    simp only [fmt, List.length_append, List.length_cons] at hl
    simp only [fmt]
    rw [rowL hs (fmt sep rs) fs f [] acc n (by omega)]
    by_cases ht : rs = []
    · subst ht
      simp [fmt]
    · have hne : fmt sep rs ≠ [] := by
        obtain ⟨r, rs', rfl⟩ := List.exists_cons_of_ne_nil ht
        simp [fmt]
      rw [ite_eq_right hne,
        rowsL hs rs (acc ++ [[] ++ f :: fs]) (n - (fs.length + 1)) ht
          (fun r h => hr r (List.mem_cons_of_mem _ h)) (by omega)]
      simp

/-- 分隔符不是 \r \n "、每行至少一列时，parse(format(rows)) = rows -/
theorem parse_format {sep : Nat} (hs : sep ≠ 10 ∧ sep ≠ 13 ∧ sep ≠ 34) (rows : List (List (List Nat)))
    (hr : ∀ r ∈ rows, r ≠ []) : parse sep (fmt sep rows) = some rows := by
  cases rows with
  | nil => simp [parse, fmt]
  | cons r rs =>
    have hne : fmt sep (r :: rs) ≠ [] := by simp [fmt]
    unfold parse
    rw [ite_eq_right hne]
    exact (rowsL hs (r :: rs) [] _ (List.cons_ne_nil _ _) hr (Nat.lt_succ_self _)).trans (by simp)

/-- 零列的行写出来是空行，读回来是一个空字段（csv.lark 开头说的例外） -/
example : parse 44 (fmt 44 [[]]) = some [[[]]] := by decide

end Csv
end Lark
