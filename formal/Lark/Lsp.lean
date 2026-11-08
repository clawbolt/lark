/-
apps/lsp 的证明 · 阶段 1：LSP 基础协议的分帧、位置（UTF-16）和字节偏移的换算、增量修改文档
先证明，再写 apps/llsp/lsp/frame.lark、lsp/pos.lark、lsp/edit.lark。

1. 分帧（LSP 规范 “Base Protocol”）：每条消息是若干行消息头（每行以 \r\n 结尾）、一个空行、再是 JSON 内容。
   必须有 Content-Length（只能有一个），别的头（Content-Type）不管。
   - `undig_digs`：长度写成十进制再读回来不变；
   - `parse_frame`：parse (frame b ++ rest) = some (b, rest)，所以接连的消息一条不丢、一个字节不多读；
   - `parse_some`：读成功时，内容和剩下的正好是输入的一段后缀：d = 消息头 ++ b ++ rest。
2. 位置：LSP 的位置是（行，列），列默认数 UTF-16 单元；换行有 \n、\r\n、\r 三种。
   文档按 Utf8.chars 切成字符，再把 \r\n 并成一个（`norm`）。列的单位写成参数 u（UTF-16 或 UTF-8 都行）。
   - `off_boundary`：offOf 给出的偏移总在字符的边界上（不会切开一个 UTF-8 字符或者 \r\n）；
   - `pos_off`：边界上的偏移换成位置再换回来不变；`off_pos`：文档里真有的位置换成偏移再换回来不变；
   - `norm_join`、`blen_doc`：切开、合并以后字节一个不丢，偏移不会超过文档长度。
3. 修改：`edit` 把 [s, e) 换成新的文字，`change` 先把范围的两头换成偏移（反过来的范围按从小到大）。
   `edit_len`、`change_len`：长度对；`edit_noop`、`edit_all`：空修改不变、整个替换就是新文字。
   用 #guard 对了 a😀b\r\nc 的各个位置（代理对中间、\r 和 \n 之间、超出行尾、超出最后一行）。
没证：不合法的 UTF-8 客户端和这里是否一样数（这里每个坏字节算 U+FFFD，1 个单元）；JSON-RPC 的内容（阶段 2）。
-/
import Lark.Utf8

namespace Lark
namespace Lsp

def bs (s : String) : List Nat := s.toList.map Char.toNat

theorem iteT {α : Type} {c : Prop} {_ : Decidable c} {a b : α} (h : c) : (if c then a else b) = a := by simp [h]
theorem iteF {α : Type} {c : Prop} {_ : Decidable c} {a b : α} (h : ¬c) : (if c then a else b) = b := by simp [h]
theorem dropApp (l x : List Nat) : (l ++ x).drop l.length = x := by simp
theorem takeApp (l x : List Nat) : (l ++ x).take l.length = l := by simp

/-! ## 十进制 -/

/-- n 的十进制数字（高位在前），没有多余的 0 -/
def digs (n : Nat) : List Nat :=
  if n < 10 then [n] else digs (n / 10) ++ [n % 10]
termination_by n
decreasing_by omega

def undig (ds : List Nat) : Nat := ds.foldl (fun a d => a * 10 + d) 0

theorem undig_snoc (ds : List Nat) (d : Nat) : undig (ds ++ [d]) = undig ds * 10 + d := by
  simp [undig, List.foldl_append]

theorem undig_digs_aux : ∀ k n, n < k → undig (digs n) = n
  | 0, _, h => absurd h (Nat.not_lt_zero _)
  | k + 1, n, h => by
    rw [digs]
    by_cases h10 : n < 10
    · simp [h10, undig]
    · simp only [h10, ↓reduceIte]
      rw [undig_snoc, undig_digs_aux k (n / 10) (by omega)]
      omega

theorem undig_digs (n : Nat) : undig (digs n) = n := undig_digs_aux (n + 1) n (by omega)

theorem digs_lt_aux : ∀ k n, n < k → ∀ d ∈ digs n, d < 10
  | 0, _, h => absurd h (Nat.not_lt_zero _)
  | k + 1, n, h => by
    rw [digs]
    by_cases h10 : n < 10
    · simp [h10]
    · simp only [h10, ↓reduceIte, List.mem_append, List.mem_singleton]
      intro d hd
      rcases hd with hd | hd
      · exact digs_lt_aux k (n / 10) (by omega) d hd
      · omega

theorem digs_lt (n : Nat) : ∀ d ∈ digs n, d < 10 := digs_lt_aux (n + 1) n (by omega)

theorem digs_ne (n : Nat) : digs n ≠ [] := by
  rw [digs]
  by_cases h10 : n < 10 <;> simp [h10]

/-- 数字写成 ASCII -/
def asc (ds : List Nat) : List Nat := ds.map (· + 48)

def isDig (x : Nat) : Bool := 48 ≤ x && x ≤ 57

/-- 一串 ASCII 数字的值（可以有开头的 0）；空的或者有别的字符时是 none -/
def num (s : List Nat) : Option Nat :=
  if s ≠ [] ∧ s.all isDig = true then some (undig (s.map (· - 48))) else none

theorem asc_sub (ds : List Nat) : (asc ds).map (· - 48) = ds := by
  induction ds with
  | nil => rfl
  | cons a l ih =>
    simp only [asc, List.map_cons] at ih ⊢
    rw [ih]
    simp

theorem num_asc (n : Nat) : num (asc (digs n)) = some n := by
  have h1 : asc (digs n) ≠ [] := by simp [asc, digs_ne]
  have h2 : (asc (digs n)).all isDig = true := by
    simp only [asc, List.all_map, List.all_eq_true]
    intro d hd
    have := digs_lt n d hd
    simp [isDig]
    omega
  have h3 : (asc (digs n)).map (· - 48) = digs n := asc_sub _
  simp [num, h1, h2, h3, undig_digs]

/-! ## 一行（到第一个 \r\n 为止） -/

def line : List Nat → Option (List Nat × List Nat)
  | [] => none
  | a :: r => if a = 13 ∧ r.head? = some 10 then some ([], r.tail) else (line r).map (fun p => (a :: p.1, p.2))

theorem line_app (l r : List Nat) (h : 13 ∉ l) : line (l ++ 13 :: 10 :: r) = some (l, r) := by
  induction l with
  | nil => simp [line]
  | cons a l ih =>
    have ha : a ≠ 13 := by intro e; exact h (by simp [e])
    have hl : 13 ∉ l := by intro e; exact h (by simp [e])
    simp [line, ha, ih hl]

theorem line_some : ∀ (d l r : List Nat), line d = some (l, r) → d = l ++ 13 :: 10 :: r
  | [], _, _, h => by simp [line] at h
  | a :: d, l, r, h => by
    simp only [line] at h
    by_cases hc : a = 13 ∧ d.head? = some 10
    · rw [iteT hc] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨rfl, h2⟩ := hc
      cases d with
      | nil => simp at h2
      | cons b d => simp at h2; simp [h2]
    · rw [iteF hc] at h
      cases hl : line d with
      | none => rw [hl] at h; simp at h
      | some p =>
        obtain ⟨l', r'⟩ := p
        rw [hl] at h
        simp at h
        obtain ⟨rfl, rfl⟩ := h
        rw [line_some d l' r' hl]
        simp

/-! ## 消息头和消息 -/

/-- "Content-Length: " -/
def hdrName : List Nat := [67, 111, 110, 116, 101, 110, 116, 45, 76, 101, 110, 103, 116, 104, 58, 32]

theorem hdrName_len : hdrName.length = 16 := by decide

/-- 内容最长 64 MiB（再长的消息拒绝，Lark 里累加数字时超过就停，不会溢出） -/
def maxLen : Nat := 67108864

theorem isPrefix_app (l x : List Nat) : l.isPrefixOf (l ++ x) = true := by
  induction l with
  | nil => simp [List.isPrefixOf]
  | cons a l ih => simp [ih]

/-- 一行一行读到空行：len 是读到的 Content-Length。返回 (长度, 空行之后的字节) -/
def headers : Nat → Option Nat → List Nat → Option (Nat × List Nat)
  | 0, _, _ => none
  | f + 1, len, d =>
    match line d with
    | none => none
    | some (l, r) =>
      if l = [] then len.map (fun n => (n, r))
      else if hdrName.isPrefixOf l = true then
        match len, num (l.drop 16) with
        | none, some n => headers f (some n) r
        | _, _ => none
      else headers f len r

/-- 读一条消息：返回 (内容, 剩下的字节)。数据还不够、格式不对都是 none（Lark 里分开报） -/
def parse (d : List Nat) : Option (List Nat × List Nat) :=
  match headers d.length none d with
  | some (n, r) => if n ≤ maxLen ∧ n ≤ r.length then some (r.take n, r.drop n) else none
  | none => none

/-- 写一条消息 -/
def frame (b : List Nat) : List Nat := hdrName ++ asc (digs b.length) ++ 13 :: 10 :: 13 :: 10 :: b

theorem no_cr_hdr (n : Nat) : 13 ∉ hdrName ++ asc (digs n) := by
  intro h
  rw [List.mem_append] at h
  rcases h with h | h
  · revert h; decide
  · simp only [asc, List.mem_map] at h
    obtain ⟨d, _, hd⟩ := h
    omega

theorem parse_frame (b rest : List Nat) (hb : b.length ≤ maxLen) : parse (frame b ++ rest) = some (b, rest) := by
  have e : frame b ++ rest = (hdrName ++ asc (digs b.length)) ++ 13 :: 10 :: (13 :: 10 :: (b ++ rest)) := by
    simp [frame]
  have l1 := line_app (hdrName ++ asc (digs b.length)) (13 :: 10 :: (b ++ rest)) (no_cr_hdr _)
  have l2 : line (13 :: 10 :: (b ++ rest)) = some ([], b ++ rest) := by simp [line]
  have hne : hdrName ++ asc (digs b.length) ≠ [] := by simp [hdrName]
  have hn : num ((hdrName ++ asc (digs b.length)).drop 16) = some b.length := by
    rw [← hdrName_len, dropApp, num_asc]
  have H1 : ∀ f, headers (f + 1 + 1) none ((hdrName ++ asc (digs b.length)) ++ 13 :: 10 :: (13 :: 10 :: (b ++ rest))) =
      headers (f + 1) (some b.length) (13 :: 10 :: (b ++ rest)) := by
    intro f
    rw [headers, l1]
    dsimp only
    simp only [iteF hne, iteT (isPrefix_app _ _), hn]
  have H2 : ∀ f, headers (f + 1) (some b.length) (13 :: 10 :: (b ++ rest)) = some (b.length, b ++ rest) := by
    intro f
    rw [headers, l2]
    simp
  obtain ⟨f, hf⟩ : ∃ f, (frame b ++ rest).length = f + 1 + 1 :=
    ⟨(frame b ++ rest).length - 2, by simp [frame]; omega⟩
  unfold parse
  rw [hf, e, H1, H2]
  simp [hb]

theorem headers_some : ∀ (f : Nat) (len : Option Nat) (d : List Nat) (n : Nat) (r : List Nat),
    headers f len d = some (n, r) → ∃ h, d = h ++ r
  | 0, _, _, _, _, h => by simp [headers] at h
  | f + 1, len, d, n, r, h => by
    simp only [headers] at h
    cases hl : line d with
    | none => rw [hl] at h; simp at h
    | some p =>
      obtain ⟨l, r'⟩ := p
      rw [hl] at h
      have ed := line_some d l r' hl
      dsimp only at h
      by_cases h0 : l = []
      · rw [iteT h0] at h
        cases len with
        | none => simp at h
        | some m =>
          simp at h
          obtain ⟨rfl, rfl⟩ := h
          exact ⟨l ++ [13, 10], by rw [ed]; simp⟩
      · rw [iteF h0] at h
        by_cases hp : hdrName.isPrefixOf l = true
        · rw [iteT hp] at h
          cases len with
          | some _ => simp at h
          | none =>
            cases hm : num (l.drop 16) with
            | none => rw [hm] at h; simp at h
            | some m =>
              rw [hm] at h
              obtain ⟨h', eh⟩ := headers_some f (some m) r' n r h
              exact ⟨l ++ 13 :: 10 :: h', by rw [ed, eh]; simp⟩
        · rw [iteF hp] at h
          obtain ⟨h', eh⟩ := headers_some f len r' n r h
          exact ⟨l ++ 13 :: 10 :: h', by rw [ed, eh]; simp⟩

theorem parse_some (d b rest : List Nat) (h : parse d = some (b, rest)) :
    (∃ hd, d = hd ++ b ++ rest) ∧ b.length ≤ maxLen := by
  unfold parse at h
  cases hh : headers d.length none d with
  | none => rw [hh] at h; simp at h
  | some p =>
    obtain ⟨n, r⟩ := p
    rw [hh] at h
    dsimp only at h
    by_cases hc : n ≤ maxLen ∧ n ≤ r.length
    · rw [iteT hc] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨hd, ed⟩ := headers_some _ _ _ _ _ hh
      refine ⟨⟨hd, ?_⟩, ?_⟩
      · rw [ed, List.append_assoc, List.take_append_drop]
      · simp only [List.length_take]; omega
    · rw [iteF hc] at h; simp at h

-- 两条消息接在一起：一条一条读出来
#guard parse (frame (bs "{}") ++ frame (bs "[1]")) == some (bs "{}", frame (bs "[1]"))
#guard parse (bs "Content-Length: 2\r\n\r\n{}") == some (bs "{}", [])
#guard parse (bs "Content-Type: application/vscode-jsonrpc; charset=utf-8\r\nContent-Length: 2\r\n\r\n{}x") == some (bs "{}", bs "x")
#guard parse (bs "Content-Length: 2\r\nContent-Length: 2\r\n\r\n{}") == none
#guard parse (bs "Content-Length: 3\r\n\r\n{}") == none
#guard parse (bs "Content-Length: x\r\n\r\n{}") == none
#guard parse (bs "\r\n{}") == none


/-! ## 文档：按字符切开，\r\n 并成一个 -/

theorem joinApp : ∀ (a b : List (List Nat)), Utf8.joinAll (a ++ b) = Utf8.joinAll a ++ Utf8.joinAll b
  | [], _ => rfl
  | x :: a, b => by simp [Utf8.joinAll, joinApp a b]

def isEol (e : List Nat) : Bool := e == [10] || e == [13] || e == [13, 10]

/-- \r 后面紧跟的 \n 并进同一个元素，这样 \r\n 中间不是边界 -/
def norm : List (List Nat) → List (List Nat)
  | [] => []
  | [c] => [c]
  | c :: d :: r' => if c = [13] ∧ d = [10] then [13, 10] :: norm r' else c :: norm (d :: r')

theorem norm_cc (c d : List Nat) (r : List (List Nat)) :
    norm (c :: d :: r) = if c = [13] ∧ d = [10] then [13, 10] :: norm r else c :: norm (d :: r) := by
  rw [norm]

theorem norm_one (c : List Nat) : norm [c] = [c] := by rw [norm]

theorem norm_join_aux : ∀ (n : Nat) (cs : List (List Nat)), cs.length ≤ n → Utf8.joinAll (norm cs) = Utf8.joinAll cs
  | _, [], _ => by simp [norm]
  | _, [c], _ => by simp [norm_one, Utf8.joinAll]
  | 0, _ :: _ :: _, h => by simp at h
  | n + 1, c :: d :: r, h => by
    by_cases hc : c = [13] ∧ d = [10]
    · obtain ⟨rfl, rfl⟩ := hc
      have ih := norm_join_aux n r (by simp at h; omega)
      rw [norm_cc]
      simp [Utf8.joinAll, ih]
    · have ih := norm_join_aux n (d :: r) (by simp at h; omega)
      rw [norm_cc]
      rw [iteF hc]
      simp only [Utf8.joinAll] at ih ⊢
      rw [ih]

theorem norm_join (cs : List (List Nat)) : Utf8.joinAll (norm cs) = Utf8.joinAll cs :=
  norm_join_aux _ cs (Nat.le_refl _)

theorem norm_ne_aux : ∀ (n : Nat) (cs : List (List Nat)), cs.length ≤ n → (∀ c ∈ cs, c ≠ []) →
    ∀ e ∈ norm cs, e ≠ []
  | _, [], _, _ => by simp [norm]
  | _, [c], _, h => by simpa [norm_one] using h
  | 0, _ :: _ :: _, h, _ => by simp at h
  | n + 1, c :: d :: r, hl, h => by
    by_cases hc : c = [13] ∧ d = [10]
    · obtain ⟨rfl, rfl⟩ := hc
      have ih := norm_ne_aux n r (by simp at hl; omega)
        (fun x hx => h x (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hx)))
      intro e he
      rw [norm_cc] at he
      simp at he
      rcases he with rfl | he
      · simp
      · exact ih e he
    · have ih := norm_ne_aux n (d :: r) (by simp at hl; omega) (fun x hx => h x (List.mem_cons_of_mem _ hx))
      intro e he
      rw [norm_cc] at he
      rw [iteF hc] at he
      rcases List.mem_cons.mp he with rfl | he
      · exact h _ (by simp)
      · exact ih e he

theorem charsF_ne : ∀ (n : Nat) (s : List Nat), ∀ c ∈ Utf8.charsF n s, c ≠ []
  | 0, _, c, h => by simp [Utf8.charsF] at h
  | _ + 1, [], c, h => by simp [Utf8.charsF] at h
  | n + 1, b :: r, c, h => by
    simp only [Utf8.charsF, List.mem_cons] at h
    rcases h with e | h
    · rw [e]
      obtain ⟨k, hk⟩ : ∃ k, Utf8.lenAt (b :: r) = k + 1 :=
        ⟨Utf8.lenAt (b :: r) - 1, by have := Utf8.lenAt_pos (b :: r); omega⟩
      rw [hk]
      simp
    · exact charsF_ne n _ c h

/-- 文档的字节切成的元素：字符，\r\n 算一个 -/
def doc (d : List Nat) : List (List Nat) := norm (Utf8.chars d)

theorem doc_ne (d : List Nat) : ∀ e ∈ doc d, e ≠ [] :=
  norm_ne_aux _ _ (Nat.le_refl _) (charsF_ne _ _)

def blen : List (List Nat) → Nat
  | [] => 0
  | e :: xs => e.length + blen xs

theorem blen_join : ∀ (xs : List (List Nat)), blen xs = (Utf8.joinAll xs).length
  | [] => rfl
  | e :: xs => by simp [blen, Utf8.joinAll, blen_join xs]

theorem blen_doc (d : List Nat) : blen (doc d) = d.length := by
  rw [blen_join, doc, norm_join, Utf8.chars_concat]

/-- 在第 k 个元素处切开文档：前面的字节 ++ 后面的字节就是原来的文档，前面正好 blen (take k) 个字节 -/
theorem doc_split (d : List Nat) (k : Nat) :
    d = Utf8.joinAll ((doc d).take k) ++ Utf8.joinAll ((doc d).drop k) ∧
    blen ((doc d).take k) = (Utf8.joinAll ((doc d).take k)).length := by
  refine ⟨?_, blen_join _⟩
  rw [← joinApp, List.take_append_drop, doc, norm_join, Utf8.chars_concat]

theorem blen_take_le : ∀ (xs : List (List Nat)) (k : Nat), blen (xs.take k) ≤ blen xs
  | [], _ => by simp [blen]
  | _ :: _, 0 => by simp [blen]
  | e :: xs, k + 1 => by
    have := blen_take_le xs k
    simp [blen]
    omega

theorem drop_ne (xs : List (List Nat)) (hx : ∀ e ∈ xs, e ≠ []) (k : Nat) : ∀ e ∈ xs.drop k, e ≠ [] := by
  intro e he
  apply hx e
  rw [← List.take_append_drop k xs]
  exact List.mem_append.mpr (Or.inr he)

/-! ## 位置 ↔ 偏移。u 是一个元素占几个列单位（UTF-16 或 UTF-8） -/

/-- UTF-16：4 字节的 UTF-8 字符（U+10000 以上）是一对代理，2 个单元；别的 1 个（不合法的字节当 U+FFFD） -/
def u16 (e : List Nat) : Nat := if e.length = 4 then 2 else 1

/-- UTF-8（客户端支持 positionEncoding = "utf-8" 时）：按字节数 -/
def u8 (e : List Nat) : Nat := e.length

theorem u16_pos : ∀ e : List Nat, e ≠ [] → 0 < u16 e := by
  intro e _
  unfold u16
  split <;> omega

theorem u8_pos : ∀ e : List Nat, e ≠ [] → 0 < u8 e := by
  intro e he
  cases e with
  | nil => exact absurd rfl he
  | cons _ _ => simp [u8]

/-- (行, 列) → 偏移：先跳过 l 行，再在这一行里走 ch 个单元。
    列超过这一行时停在行尾（不跨到下一行），落在字符中间（比如代理对的中间）时往前取到字符的开头，行超过文档时是文档末尾 -/
def offGo (u : List Nat → Nat) : List (List Nat) → Nat → Nat → Nat
  | [], _, _ => 0
  | e :: xs, l + 1, ch => if isEol e = true then e.length + offGo u xs l ch else e.length + offGo u xs (l + 1) ch
  | e :: xs, 0, ch => if isEol e = true ∨ ch < u e then 0 else e.length + offGo u xs 0 (ch - u e)

/-- 偏移 → (行, 列)：落在元素中间（字符中间、\r 和 \n 之间）时取这个元素开头的位置 -/
def posGo (u : List Nat → Nat) : List (List Nat) → Nat → Nat → Nat → Nat × Nat
  | [], _, l, ch => (l, ch)
  | e :: xs, o, l, ch =>
    if o < e.length then (l, ch)
    else if isEol e = true then posGo u xs (o - e.length) (l + 1) 0
    else posGo u xs (o - e.length) l (ch + u e)

/-- 从 (l, ch) 开始走完 p 以后的位置 -/
def posEnd (u : List Nat → Nat) : List (List Nat) → Nat → Nat → Nat × Nat
  | [], l, ch => (l, ch)
  | e :: p, l, ch => if isEol e = true then posEnd u p (l + 1) 0 else posEnd u p l (ch + u e)

def offOf (u : List Nat → Nat) (xs : List (List Nat)) (p : Nat × Nat) : Nat := offGo u xs p.1 p.2
def posOf (u : List Nat → Nat) (xs : List (List Nat)) (o : Nat) : Nat × Nat := posGo u xs o 0 0

theorem posGo_end (u : List Nat → Nat) : ∀ (p s : List (List Nat)) (l ch : Nat), (∀ e ∈ s, e ≠ []) →
    posGo u (p ++ s) (blen p) l ch = posEnd u p l ch
  | [], [], l, ch, _ => by simp [posGo, posEnd, blen]
  | [], e :: s, l, ch, hs => by
    have he : e ≠ [] := hs e (by simp)
    cases e with
    | nil => exact absurd rfl he
    | cons a e => simp [posGo, posEnd, blen]
  | e :: p, s, l, ch, hs => by
    have ih1 := posGo_end u p s (l + 1) 0 hs
    have ih2 := posGo_end u p s l (ch + u e) hs
    have h1 : ¬ (e.length + blen p < e.length) := by omega
    have h2 : e.length + blen p - e.length = blen p := by omega
    simp only [List.cons_append, posGo, blen, posEnd, h1, ↓reduceIte, h2]
    by_cases he : isEol e = true
    · rw [iteT he, iteT he, ih1]
    · rw [iteF he, iteF he, ih2]

theorem posEnd_ge (u : List Nat → Nat) : ∀ (p : List (List Nat)) (l ch : Nat), l ≤ (posEnd u p l ch).1
  | [], l, ch => by simp [posEnd]
  | e :: p, l, ch => by
    simp only [posEnd]
    by_cases he : isEol e = true
    · rw [iteT he]; have := posEnd_ge u p (l + 1) 0; omega
    · rw [iteF he]; exact posEnd_ge u p l (ch + u e)

theorem posEnd_same (u : List Nat → Nat) : ∀ (p : List (List Nat)) (l ch : Nat),
    (posEnd u p l ch).1 = l → ch ≤ (posEnd u p l ch).2
  | [], l, ch, _ => by simp [posEnd]
  | e :: p, l, ch, h => by
    simp only [posEnd] at h ⊢
    by_cases he : isEol e = true
    · rw [iteT he] at h; have := posEnd_ge u p (l + 1) 0; omega
    · rw [iteF he] at h ⊢; have := posEnd_same u p l (ch + u e) h; omega

/-- 走到 posEnd 给出的位置，offGo 正好停在 p 的末尾（下一个元素不是空的，所以列走完时一定停） -/
theorem offGo_end (u : List Nat → Nat) (hu : ∀ e : List Nat, e ≠ [] → 0 < u e) :
    ∀ (p s : List (List Nat)) (l ch : Nat), (∀ e ∈ s, e ≠ []) →
    ((posEnd u p l ch).1 = l → offGo u (p ++ s) 0 ((posEnd u p l ch).2 - ch) = blen p) ∧
    (l < (posEnd u p l ch).1 → offGo u (p ++ s) ((posEnd u p l ch).1 - l) (posEnd u p l ch).2 = blen p)
  | [], s, l, ch, hs => by
    simp only [posEnd, List.nil_append, blen]
    refine ⟨fun _ => ?_, fun h => absurd h (by omega)⟩
    rw [Nat.sub_self]
    cases s with
    | nil => simp [offGo]
    | cons e s =>
      have h0 := hu e (hs e (by simp))
      simp only [offGo]
      rw [iteT (Or.inr h0)]
  | e :: p, s, l, ch, hs => by
    by_cases he : isEol e = true
    · have ih := offGo_end u hu p s (l + 1) 0 hs
      have hpe : posEnd u (e :: p) l ch = posEnd u p (l + 1) 0 := by simp only [posEnd]; rw [iteT he]
      have hge := posEnd_ge u p (l + 1) 0
      rw [hpe]
      refine ⟨fun h => absurd h (by omega), fun _ => ?_⟩
      obtain ⟨m, hm⟩ : ∃ m, (posEnd u p (l + 1) 0).1 - l = m + 1 := ⟨(posEnd u p (l + 1) 0).1 - l - 1, by omega⟩
      rw [hm, List.cons_append]
      simp only [offGo, blen]
      rw [iteT he]
      congr 1
      by_cases hL : (posEnd u p (l + 1) 0).1 = l + 1
      · have := ih.1 hL
        have hm0 : m = 0 := by omega
        rw [hm0]
        simpa using this
      · have := ih.2 (by omega)
        have hm' : m = (posEnd u p (l + 1) 0).1 - (l + 1) := by omega
        rw [hm']
        exact this
    · have ih := offGo_end u hu p s l (ch + u e) hs
      have hpe : posEnd u (e :: p) l ch = posEnd u p l (ch + u e) := by simp only [posEnd]; rw [iteF he]
      rw [hpe, List.cons_append]
      refine ⟨fun h => ?_, fun h => ?_⟩
      · have hc := posEnd_same u p l (ch + u e) h
        have := ih.1 h
        simp only [offGo, blen]
        have hn : ¬ (isEol e = true ∨ (posEnd u p l (ch + u e)).2 - ch < u e) := by
          intro hh
          rcases hh with hh | hh
          · exact he hh
          · omega
        rw [iteF hn]
        have hs' : (posEnd u p l (ch + u e)).2 - ch - u e = (posEnd u p l (ch + u e)).2 - (ch + u e) := by omega
        rw [hs', this]
      · have := ih.2 h
        obtain ⟨m, hm⟩ : ∃ m, (posEnd u p l (ch + u e)).1 - l = m + 1 :=
          ⟨(posEnd u p l (ch + u e)).1 - l - 1, by omega⟩
        rw [hm] at this ⊢
        simp only [offGo, blen]
        rw [iteF he, this]

/-- offGo 的结果总是某个元素的边界 -/
theorem offGo_bound (u : List Nat → Nat) : ∀ (xs : List (List Nat)) (l ch : Nat),
    ∃ k, k ≤ xs.length ∧ offGo u xs l ch = blen (xs.take k)
  | [], _, _ => ⟨0, by simp, by simp [offGo, blen]⟩
  | e :: xs, l + 1, ch => by
    by_cases he : isEol e = true
    · obtain ⟨k, hk, h⟩ := offGo_bound u xs l ch
      refine ⟨k + 1, by simp; omega, ?_⟩
      simp only [offGo]
      rw [iteT he, h]
      simp [blen]
    · obtain ⟨k, hk, h⟩ := offGo_bound u xs (l + 1) ch
      refine ⟨k + 1, by simp; omega, ?_⟩
      simp only [offGo]
      rw [iteF he, h]
      simp [blen]
  | e :: xs, 0, ch => by
    by_cases hs : isEol e = true ∨ ch < u e
    · refine ⟨0, by simp, ?_⟩
      simp only [offGo]
      rw [iteT hs]
      simp [blen]
    · obtain ⟨k, hk, h⟩ := offGo_bound u xs 0 (ch - u e)
      refine ⟨k + 1, by simp; omega, ?_⟩
      simp only [offGo]
      rw [iteF hs, h]
      simp [blen]

theorem posOf_blen (u : List Nat → Nat) (xs : List (List Nat)) (hx : ∀ e ∈ xs, e ≠ []) (k : Nat) :
    posOf u xs (blen (xs.take k)) = posEnd u (xs.take k) 0 0 := by
  have h1 := posGo_end u (xs.take k) (xs.drop k) 0 0 (drop_ne xs hx k)
  rw [List.take_append_drop] at h1
  exact h1

/-- 边界上的偏移 → 位置 → 偏移，不变 -/
theorem pos_off (u : List Nat → Nat) (hu : ∀ e : List Nat, e ≠ [] → 0 < u e)
    (xs : List (List Nat)) (hx : ∀ e ∈ xs, e ≠ []) (k : Nat) :
    offOf u xs (posOf u xs (blen (xs.take k))) = blen (xs.take k) := by
  have h2 := offGo_end u hu (xs.take k) (xs.drop k) 0 0 (drop_ne xs hx k)
  rw [List.take_append_drop] at h2
  rw [posOf_blen u xs hx k]
  unfold offOf
  by_cases hL : (posEnd u (xs.take k) 0 0).1 = 0
  · have := h2.1 hL
    simp only [Nat.sub_zero] at this
    rw [hL]
    exact this
  · have := h2.2 (by omega)
    simp only [Nat.sub_zero] at this
    exact this

/-- 文档里真有的位置 → 偏移 → 位置，不变 -/
theorem off_pos (u : List Nat → Nat) (hu : ∀ e : List Nat, e ≠ [] → 0 < u e)
    (xs : List (List Nat)) (hx : ∀ e ∈ xs, e ≠ []) (k : Nat) :
    posOf u xs (offOf u xs (posEnd u (xs.take k) 0 0)) = posEnd u (xs.take k) 0 0 := by
  rw [← posOf_blen u xs hx k, pos_off u hu xs hx k]

/-- 任何位置（包括超出范围的）换成的偏移都在字符边界上，并且不超过文档的长度 -/
theorem off_boundary (u : List Nat → Nat) (d : List Nat) (p : Nat × Nat) :
    ∃ k, offOf u (doc d) p = blen ((doc d).take k) ∧
      d.take (offOf u (doc d) p) = Utf8.joinAll ((doc d).take k) ∧ offOf u (doc d) p ≤ d.length := by
  obtain ⟨k, _, h⟩ := offGo_bound u (doc d) p.1 p.2
  obtain ⟨hs, hb⟩ := doc_split d k
  have hle := blen_take_le (doc d) k
  rw [blen_doc] at hle
  refine ⟨k, h, ?_, ?_⟩
  · unfold offOf
    rw [h, hb]
    generalize Utf8.joinAll ((doc d).take k) = A at hs ⊢
    generalize Utf8.joinAll ((doc d).drop k) = B at hs
    rw [hs]
    simp
  · unfold offOf
    rw [h]
    exact hle

/-! ## 修改文档（textDocument/didChange）：把 [s, e) 换成 t -/

def edit (d : List Nat) (s e : Nat) (t : List Nat) : List Nat := d.take s ++ t ++ d.drop e

/-- 一处修改：范围的两头换成偏移，反过来的范围也按从小到大处理 -/
def change (u : List Nat → Nat) (d : List Nat) (a b : Nat × Nat) (t : List Nat) : List Nat :=
  edit d (min (offOf u (doc d) a) (offOf u (doc d) b)) (max (offOf u (doc d) a) (offOf u (doc d) b)) t

theorem edit_len (d t : List Nat) (s e : Nat) (h1 : s ≤ e) (h2 : e ≤ d.length) :
    (edit d s e t).length = d.length - (e - s) + t.length := by
  simp [edit]
  omega

theorem edit_noop (d : List Nat) (s : Nat) : edit d s s [] = d := by simp [edit]

theorem edit_all (d t : List Nat) : edit d 0 d.length t = t := by simp [edit]

theorem change_len (u : List Nat → Nat) (d t : List Nat) (a b : Nat × Nat) :
    (change u d a b t).length =
      d.length - (max (offOf u (doc d) a) (offOf u (doc d) b) - min (offOf u (doc d) a) (offOf u (doc d) b)) + t.length := by
  obtain ⟨_, _, _, ha⟩ := off_boundary u d a
  obtain ⟨_, _, _, hb⟩ := off_boundary u d b
  unfold change
  apply edit_len
  · omega
  · omega

/-! ## 例子：a😀b\r\nc（😀 是 F0 9F 98 80，UTF-16 里占 2 个单元） -/

def ex : List Nat := [97, 0xF0, 0x9F, 0x98, 0x80, 98, 13, 10, 99]
#guard (doc ex).length == 5
#guard posOf u16 (doc ex) 5 == (0, 3)
#guard posOf u16 (doc ex) 6 == (0, 4)
#guard posOf u16 (doc ex) 7 == (0, 4)   -- \r 和 \n 之间：取 \r\n 的开头
#guard posOf u16 (doc ex) 8 == (1, 0)
#guard posOf u16 (doc ex) 9 == (1, 1)
#guard posOf u16 (doc ex) 3 == (0, 1)   -- 😀 的中间：取 😀 的开头
#guard offOf u16 (doc ex) (0, 2) == 1   -- 代理对的中间：取 😀 的开头
#guard offOf u16 (doc ex) (0, 3) == 5
#guard offOf u16 (doc ex) (0, 99) == 6  -- 超过行尾：停在 \r\n 之前
#guard offOf u16 (doc ex) (1, 0) == 8
#guard offOf u16 (doc ex) (5, 0) == 9   -- 超过最后一行：文档末尾
#guard offOf u8 (doc ex) (0, 5) == 5
#guard posOf u8 (doc ex) 5 == (0, 5)
#guard posOf u16 (doc [97, 13, 98]) 2 == (1, 0)   -- 单独的 \r 也是换行
#guard change u16 ex (0, 1) (0, 3) (bs "x") == bs "axb\r\nc"
#guard change u16 ex (0, 3) (0, 1) (bs "x") == bs "axb\r\nc"

end Lsp
end Lark
