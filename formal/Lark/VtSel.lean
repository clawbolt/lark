/-
apps/lterm 的证明 · 阶段 12：鼠标选中、复制
先证明，再写 apps/lterm/vt/sel.lark。

格子按"行号 × 列数 + 列"排成一条线（行号是滚动缓冲和屏幕连起来以后的行号，所以翻看历史时也能选），
选中的是两个位置之间（含两头）的一段，和别的终端一样按行连着选。
一格是码点：宽字符的右半是 0（sp，和 vt/screen 的 cell_ch 一样），空白是 32。
复制的文字：每一行取选中的那一段，去掉宽字符的右半（noSp），去掉行尾的空白（trim），行之间用换行（10）连起来。
双击选一个词：从点的位置往左、往右，一直到不是词里的字符（空白、标点）为止。

证明了：
- `mk_symm`、`mk_in`：从哪头往哪头拖都一样，选中的正好是两个位置之间的格子；
- `trim_split`、`trim_end`、`trim_pad`：去掉行尾空白以后，原来的行就是它接上若干空白，它自己不以空白结尾，
  行尾多几个空白不影响结果；
- `split_join`：复制的文字按换行切开，正好是每一行选中的部分（格子里没有换行时）；
  `copy_lines`：所以复制出来的是 最后一行 - 第一行 + 1 行，一行一行对得上；
- `left_le`、`left_word`、`left_stop`、`right_ge`、`right_word`、`right_stop`：双击选的词包含点的位置，
  里面都是词里的字符，两头再往外一格就不是了（或者到了行的两头）——选到的是最长的那个词。
例子（#guard）里检查了：拖着选、反着拖、跨行、宽字符、行尾空白、双击选词。
-/
import Lark.Lsp

namespace Lark
namespace VtSel

def sp : Nat := 0
def blank : Nat := 32
def nl : Nat := 10

/-! ## 选中的范围 -/

structure Sel where
  lo : Nat
  hi : Nat
  deriving DecidableEq, Repr

def mk (a b : Nat) : Sel := ⟨min a b, max a b⟩

def inSel (s : Sel) (i : Nat) : Bool := decide (s.lo ≤ i) && decide (i ≤ s.hi)

theorem mk_symm (a b : Nat) : mk a b = mk b a := by
  unfold mk
  rw [Nat.min_comm, Nat.max_comm]

theorem mk_in (a b i : Nat) : inSel (mk a b) i = true ↔ (a ≤ i ∧ i ≤ b) ∨ (b ≤ i ∧ i ≤ a) := by
  have e : inSel (mk a b) i = (decide (min a b ≤ i) && decide (i ≤ max a b)) := rfl
  rw [e, Bool.and_eq_true, decide_eq_true_iff, decide_eq_true_iff]
  by_cases hab : a ≤ b
  · rw [Nat.min_eq_left hab, Nat.max_eq_right hab]
    omega
  · rw [Nat.min_eq_right (by omega), Nat.max_eq_left (by omega)]
    omega

theorem mk_le (a b : Nat) : (mk a b).lo ≤ (mk a b).hi := by
  simp only [mk]
  omega

/-! ## 一行：取一段、去掉宽字符的右半、去掉行尾空白 -/

def cellAt : List Nat → Nat → Nat
  | [], _ => blank
  | c :: _, 0 => c
  | _ :: r, i + 1 => cellAt r i

theorem cellAt_mem : ∀ (r : List Nat) (i : Nat), cellAt r i = blank ∨ cellAt r i ∈ r
  | [], _ => Or.inl rfl
  | _ :: _, 0 => Or.inr (List.mem_cons_self ..)
  | _ :: r, i + 1 => by
    rcases cellAt_mem r i with h | h
    · exact Or.inl h
    · exact Or.inr (List.mem_cons_of_mem _ h)

/-- 第 a 到第 b 格（含两头） -/
def seg (r : List Nat) (a b : Nat) : List Nat := (List.range (b + 1 - a)).map (fun k => cellAt r (a + k))

def noSp (r : List Nat) : List Nat := r.filter (fun c => c != sp)

def dropB : List Nat → List Nat
  | [] => []
  | c :: r => if c = blank then dropB r else c :: r

def trim (r : List Nat) : List Nat := (dropB r.reverse).reverse

theorem dropB_split : ∀ l : List Nat, ∃ n, l = List.replicate n blank ++ dropB l
  | [] => ⟨0, rfl⟩
  | c :: r => by
    by_cases h : c = blank
    · obtain ⟨n, hn⟩ := dropB_split r
      refine ⟨n + 1, ?_⟩
      have e : dropB (c :: r) = dropB r := by simp only [dropB, Lsp.iteT h]
      rw [e, List.replicate_succ, List.cons_append, ← hn, h]
    · exact ⟨0, by simp only [dropB, Lsp.iteF h, List.replicate_zero, List.nil_append]⟩

theorem dropB_head : ∀ (l t : List Nat) (c : Nat), dropB l = c :: t → c ≠ blank
  | [], _, _, h => by simp [dropB] at h
  | x :: r, t, c, h => by
    by_cases hx : x = blank
    · simp only [dropB, Lsp.iteT hx] at h
      exact dropB_head r t c h
    · simp only [dropB, Lsp.iteF hx, List.cons.injEq] at h
      rw [← h.1]
      exact hx

theorem dropB_rep (n : Nat) (l : List Nat) : dropB (List.replicate n blank ++ l) = dropB l := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [List.replicate_succ, List.cons_append, dropB]
    exact ih

theorem trim_split (r : List Nat) : ∃ n, r = trim r ++ List.replicate n blank := by
  obtain ⟨n, hn⟩ := dropB_split r.reverse
  refine ⟨n, ?_⟩
  have e := congrArg List.reverse hn
  rw [List.reverse_reverse, List.reverse_append, List.reverse_replicate] at e
  exact e

theorem trim_end (r u : List Nat) : trim r ≠ u ++ [blank] := by
  intro h
  have e := congrArg List.reverse h
  simp only [trim, List.reverse_reverse, List.reverse_append, List.reverse_cons, List.reverse_nil,
    List.nil_append, List.singleton_append] at e
  exact dropB_head _ _ _ e rfl

theorem trim_pad (r : List Nat) (n : Nat) : trim (r ++ List.replicate n blank) = trim r := by
  simp only [trim, List.reverse_append, List.reverse_replicate, dropB_rep]

theorem trim_mem {r : List Nat} {c : Nat} (h : c ∈ trim r) : c ∈ r := by
  obtain ⟨n, hn⟩ := trim_split r
  rw [hn]
  exact List.mem_append_left _ h

theorem noSp_mem {r : List Nat} {c : Nat} (h : c ∈ noSp r) : c ∈ r := by
  simp only [noSp, List.mem_filter] at h
  exact h.1

theorem seg_mem {r : List Nat} {a b c : Nat} (h : c ∈ seg r a b) : c = blank ∨ c ∈ r := by
  simp only [seg, List.mem_map] at h
  obtain ⟨k, _, hk⟩ := h
  rw [← hk]
  exact cellAt_mem r (a + k)

/-! ## 换行连起来、按换行切开 -/

def joinNl : List (List Nat) → List Nat
  | [] => []
  | [l] => l
  | l :: m :: r => l ++ nl :: joinNl (m :: r)

def addHead (c : Nat) : List (List Nat) → List (List Nat)
  | [] => [[c]]
  | l :: ls => (c :: l) :: ls

def split10 : List Nat → List (List Nat)
  | [] => [[]]
  | c :: r => if c = nl then [] :: split10 r else addHead c (split10 r)

def prep (l : List Nat) : List (List Nat) → List (List Nat)
  | [] => [l]
  | m :: ms => (l ++ m) :: ms

theorem split_cons : ∀ x : List Nat, ∃ m ms, split10 x = m :: ms
  | [] => ⟨[], [], rfl⟩
  | c :: r => by
    by_cases h : c = nl
    · exact ⟨[], split10 r, by simp only [split10, Lsp.iteT h]⟩
    · obtain ⟨m, ms, e⟩ := split_cons r
      exact ⟨c :: m, ms, by simp only [split10, Lsp.iteF h, e, addHead]⟩

theorem split_pre : ∀ (l x : List Nat), (∀ c ∈ l, c ≠ nl) → split10 (l ++ x) = prep l (split10 x)
  | [], x, _ => by
    obtain ⟨m, ms, e⟩ := split_cons x
    simp only [List.nil_append, e, prep]
  | c :: l, x, h => by
    have hc : c ≠ nl := h c (List.mem_cons_self ..)
    have ih := split_pre l x (fun d hd => h d (List.mem_cons_of_mem _ hd))
    obtain ⟨m, ms, e⟩ := split_cons x
    rw [List.cons_append]
    simp only [split10, Lsp.iteF hc, ih, e, prep, addHead, List.cons_append]

theorem split_join : ∀ ls : List (List Nat), ls ≠ [] → (∀ l ∈ ls, ∀ c ∈ l, c ≠ nl) → split10 (joinNl ls) = ls
  | [], h, _ => absurd rfl h
  | [l], _, h => by
    have e := split_pre l [] (h l (List.mem_singleton_self _))
    rw [List.append_nil] at e
    simp only [joinNl, e, split10, prep, List.append_nil]
  | l :: m :: r, _, h => by
    have hl := h l (List.mem_cons_self ..)
    have ih := split_join (m :: r) (List.cons_ne_nil _ _) (fun x hx => h x (List.mem_cons_of_mem _ hx))
    simp only [joinNl]
    rw [split_pre l _ hl]
    simp only [split10, ↓reduceIte, ih, prep, List.append_nil]

/-! ## 复制 -/

def rowAt : List (List Nat) → Nat → List Nat
  | [], _ => []
  | r :: _, 0 => r
  | _ :: rs, i + 1 => rowAt rs i

theorem rowAt_mem : ∀ (g : List (List Nat)) (i : Nat), rowAt g i = [] ∨ rowAt g i ∈ g
  | [], _ => Or.inl rfl
  | _ :: _, 0 => Or.inr (List.mem_cons_self ..)
  | _ :: rs, i + 1 => by
    rcases rowAt_mem rs i with h | h
    · exact Or.inl h
    · exact Or.inr (List.mem_cons_of_mem _ h)

/-- 第 y 行选中的部分（C 列） -/
def lineOf (g : List (List Nat)) (C : Nat) (s : Sel) (y : Nat) : List Nat :=
  let a := if y = s.lo / C then s.lo % C else 0
  let b := if y = s.hi / C then s.hi % C else C - 1
  trim (noSp (seg (rowAt g y) a b))

def rows (C : Nat) (s : Sel) : List Nat := List.range' (s.lo / C) (s.hi / C + 1 - s.lo / C)

def copy (g : List (List Nat)) (C : Nat) (s : Sel) : List Nat := joinNl ((rows C s).map (lineOf g C s))

/-- 格子里没有换行 -/
def noNl (g : List (List Nat)) : Prop := ∀ r ∈ g, ∀ c ∈ r, c ≠ nl

theorem line_noNl {g : List (List Nat)} (hg : noNl g) (C : Nat) (s : Sel) (y : Nat) : ∀ c ∈ lineOf g C s y, c ≠ nl := by
  intro c hc
  have h1 := noSp_mem (trim_mem hc)
  rcases seg_mem h1 with h2 | h2
  · rw [h2]
    decide
  · rcases rowAt_mem g y with h3 | h3
    · rw [h3] at h2
      simp at h2
    · exact hg _ h3 c h2

theorem rows_len (C : Nat) (s : Sel) : (rows C s).length = s.hi / C + 1 - s.lo / C := by
  simp [rows]

theorem copy_lines {g : List (List Nat)} (hg : noNl g) (C : Nat) (s : Sel) (hs : s.lo ≤ s.hi) :
    split10 (copy g C s) = (rows C s).map (lineOf g C s) ∧
    ((rows C s).map (lineOf g C s)).length = s.hi / C - s.lo / C + 1 := by
  have hd : s.lo / C ≤ s.hi / C := Nat.div_le_div_right hs
  have hl : ((rows C s).map (lineOf g C s)).length = s.hi / C - s.lo / C + 1 := by
    rw [List.length_map, rows_len]
    omega
  refine ⟨?_, hl⟩
  unfold copy
  apply split_join
  · intro e
    rw [e] at hl
    simp at hl
  · intro l hl2 c hc
    simp only [List.mem_map] at hl2
    obtain ⟨y, _, hy⟩ := hl2
    rw [← hy] at hc
    exact line_noNl hg C s y c hc

/-! ## 双击选词 -/

def seps : List Nat := [blank, 0x09, 0x22, 0x27, 0x28, 0x29, 0x2C, 0x3A, 0x3B, 0x3C, 0x3E, 0x5B, 0x5D, 0x60, 0x7B, 0x7C, 0x7D]

/-- 词里的字符：不是空白、引号、括号、逗号这些（宽字符的右半 sp 也算，中文连着选） -/
def isWord (c : Nat) : Bool := !(seps.contains c)

/-- 往左：第 i - 1 格还是词里的字符就继续 -/
def left (r : List Nat) : Nat → Nat
  | 0 => 0
  | i + 1 => if isWord (cellAt r i) = true then left r i else i + 1

/-- 往右最多走 k 格：第 x + 1 格还是词里的字符就继续 -/
def right (r : List Nat) (x : Nat) : Nat → Nat
  | 0 => x
  | k + 1 => if isWord (cellAt r (x + 1)) = true then right r (x + 1) k else x

theorem left_le (r : List Nat) : ∀ x, left r x ≤ x
  | 0 => Nat.le_refl 0
  | i + 1 => by
    simp only [left]
    by_cases h : isWord (cellAt r i) = true
    · rw [Lsp.iteT h]
      have := left_le r i
      omega
    · rw [Lsp.iteF h]
      exact Nat.le_refl _

theorem left_word (r : List Nat) : ∀ x j, left r x ≤ j → j < x → isWord (cellAt r j) = true
  | 0, _, _, h2 => absurd h2 (Nat.not_lt_zero _)
  | i + 1, j, h1, h2 => by
    simp only [left] at h1
    by_cases h : isWord (cellAt r i) = true
    · rw [Lsp.iteT h] at h1
      by_cases hj : j = i
      · rw [hj]
        exact h
      · exact left_word r i j h1 (by omega)
    · rw [Lsp.iteF h] at h1
      omega

theorem left_stop (r : List Nat) : ∀ x, left r x = 0 ∨ isWord (cellAt r (left r x - 1)) = false
  | 0 => Or.inl rfl
  | i + 1 => by
    simp only [left]
    by_cases h : isWord (cellAt r i) = true
    · rw [Lsp.iteT h]
      exact left_stop r i
    · rw [Lsp.iteF h]
      right
      simpa using h

theorem right_ge (r : List Nat) : ∀ k x, x ≤ right r x k ∧ right r x k ≤ x + k
  | 0, x => ⟨Nat.le_refl x, Nat.le_refl x⟩
  | k + 1, x => by
    simp only [right]
    by_cases h : isWord (cellAt r (x + 1)) = true
    · rw [Lsp.iteT h]
      have := right_ge r k (x + 1)
      omega
    · rw [Lsp.iteF h]
      omega

theorem right_word (r : List Nat) : ∀ k x j, x < j → j ≤ right r x k → isWord (cellAt r j) = true
  | 0, _, _, h1, h2 => by
    simp only [right] at h2
    omega
  | k + 1, x, j, h1, h2 => by
    simp only [right] at h2
    by_cases h : isWord (cellAt r (x + 1)) = true
    · rw [Lsp.iteT h] at h2
      by_cases hj : j = x + 1
      · rw [hj]
        exact h
      · exact right_word r k (x + 1) j (by omega) h2
    · rw [Lsp.iteF h] at h2
      omega

theorem right_stop (r : List Nat) : ∀ k x, right r x k = x + k ∨ isWord (cellAt r (right r x k + 1)) = false
  | 0, x => Or.inl rfl
  | k + 1, x => by
    simp only [right]
    by_cases h : isWord (cellAt r (x + 1)) = true
    · rw [Lsp.iteT h]
      rcases right_stop r k (x + 1) with e | e
      · left
        omega
      · exact Or.inr e
    · rw [Lsp.iteF h]
      right
      simpa using h

/-- 双击第 x 格（一行 C 格）：点在词里时选中的词是 [left, right]，点在空白、标点上时就是那一格 -/
def word (r : List Nat) (C x : Nat) : Nat × Nat :=
  if isWord (cellAt r x) = true then (left r x, right r x (C - 1 - x)) else (x, x)

/-! ## 例子 -/

def bs (s : String) : List Nat := s.toList.map Char.toNat

-- 两行、每行 5 格："ab   " / "cd ef"
def g1 : List (List Nat) := [bs "ab   ", bs "cd ef"]

-- 从 (0,1) 拖到 (1,1)：第一行从 b 到行尾（行尾空白去掉），第二行到 d
#guard copy g1 5 (mk 1 6) == bs "b" ++ [nl] ++ bs "cd"
-- 反着拖一样
#guard copy g1 5 (mk 6 1) == copy g1 5 (mk 1 6)
-- 只选一格
#guard copy g1 5 (mk 8 8) == bs "e"
-- 只选了空白：空的一行
#guard copy g1 5 (mk 2 4) == []
-- 宽字符："中" 占两格（右半是 sp），复制出来只有一个字
#guard copy [[0x4E2D, sp, 0x41]] 3 (mk 0 2) == [0x4E2D, 0x41]
-- 按换行切开正好是每一行
#guard split10 (copy g1 5 (mk 0 9)) == [bs "ab", bs "cd ef"]
-- 双击选词：在 "cd ef" 的 e 上是 [3, 4]，在 c 上是 [0, 1]，在空白上就是那一格
#guard word (bs "cd ef") 5 3 == (3, 4)
#guard word (bs "cd ef") 5 0 == (0, 1)
#guard word (bs "a(bc)d") 6 2 == (2, 3)
#guard word (bs "cd ef") 5 2 == (2, 2)
#guard word [0x4E2D, sp, 0x6587, sp] 4 1 == (0, 3)

end VtSel
end Lark
