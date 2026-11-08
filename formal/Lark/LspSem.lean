/-
apps/llsp 的证明 · 阶段 9：语义高亮（LSP 规范的 “textDocument/semanticTokens/full”）
先证明，再写 apps/llsp/lsp/semantic.lark。

做法分两步：
1. 找出代码里的每个标识符（scan）：一个字节一个字节地走，记着现在是在代码里、字符串里（"…"，\ 转义）、
   注释里（// 到行尾）还是字符字面量里（'…'）；只在代码里、上一个字节不是标识符的字节、自己不是数字时开始一个词。
   字符串里的插值 #{…} 是代码，照样出词：和 compiler/lex.lark 一样数花括号，配对的 } 回到字符串里，插值里的字符串还能再有插值。
2. 每个词按上下文定种类（函数、类型、参数、局部变量、字段、模块、关键字，Lark 里，没证），
   再按 LSP 的规定写成相对前一个的差（encode）：行差、列差（同一行时）、长度、种类、修饰（一个位掩码，原样写出）。

证明了：
- `scan_word`：找出的每个词，在它的偏移上正好是一串标识符的字节、非空、往右已经到头（LspDef.idLen）；
- `scan_disjoint`：词按位置排好、互不重叠（后一个从前一个的结尾或者更后面开始）；
- 字符串、注释、字符字面量里面不出词，插值里出词：只在 #guard 里检查了（模式的切换写在 scan 里，一看就明白）；
- `decode_encode`：位置按顺序排好时，编码以后按 LSP 的规则解回来，正好是原来的位置、长度、种类和修饰。
没证：每个词是什么种类、带什么修饰（看上下文猜的）。
-/
import Lark.Lsp
import Lark.LspDef

namespace Lark
namespace LspSem

open LspDef

def isDigit (c : Nat) : Bool := 48 ≤ c && c ≤ 57

/-- hash：字符串里刚走过 #，下一个字节是 {（进插值） -/
inductive M
  | code | str | esc | cmt | chr | chrEsc | hash
deriving DecidableEq, Repr

/-- 插值里多了一层没配对的 { -/
def depthUp : List Nat → List Nat
  | d :: ks => (d + 1) :: ks
  | [] => []

/-- 插值里配对了一个 } -/
def depthDown : List Nat → List Nat
  | (d + 1) :: ks => d :: ks
  | ks => ks

/-- (偏移, 长度) 的列表。p：上一个字节是不是标识符的字节；
st：现在在几层插值 #{…} 里，每层记着里面还没配对的 { 有几个（和 compiler/lex.lark 一样数花括号）。
插值里是代码，里面的字符串还能再有插值；这一层的 { 都配对了时遇到 }，回到外面的字符串里。 -/
def scan : M → Bool → List Nat → Nat → List Nat → List (Nat × Nat)
  | _, _, _, _, [] => []
  | .code, p, st, o, c :: r =>
    if c = 47 ∧ r.head? = some 47 then scan .cmt false st (o + 1) r
    else if c = 34 then scan .str false st (o + 1) r
    else if c = 39 then scan .chr false st (o + 1) r
    else if c = 123 then scan .code false (depthUp st) (o + 1) r
    else if c = 125 ∧ st.head? = some 0 then scan .str false st.tail (o + 1) r
    else if c = 125 then scan .code false (depthDown st) (o + 1) r
    else if isId c then
      (if p || isDigit c then scan .code true st (o + 1) r else (o, idLen (c :: r)) :: scan .code true st (o + 1) r)
    else scan .code false st (o + 1) r
  | .str, _, st, o, c :: r =>
    if c = 92 then scan .esc false st (o + 1) r
    else if c = 34 then scan .code false st (o + 1) r
    else if c = 35 ∧ r.head? = some 123 then scan .hash false st (o + 1) r
    else scan .str false st (o + 1) r
  | .hash, _, st, o, _ :: r => scan .code false (0 :: st) (o + 1) r
  | .esc, _, st, o, _ :: r => scan .str false st (o + 1) r
  | .cmt, _, st, o, c :: r => if c = 10 then scan .code false st (o + 1) r else scan .cmt false st (o + 1) r
  | .chr, _, st, o, c :: r =>
    if c = 92 then scan .chrEsc false st (o + 1) r else if c = 39 then scan .code false st (o + 1) r else scan .chr false st (o + 1) r
  | .chrEsc, _, st, o, _ :: r => scan .chr false st (o + 1) r

def words (d : List Nat) : List (Nat × Nat) := scan .code false [] 0 d

/-- 走一个字节：要么什么都不出，要么（只在代码里）在 o 出一个词，之后上一个字节是标识符的字节 -/
theorem scan_cons (m : M) (p : Bool) (st : List Nat) (o c : Nat) (r : List Nat) :
    (∃ m' p' st', scan m p st o (c :: r) = scan m' p' st' (o + 1) r) ∨
      (isId c = true ∧ scan m p st o (c :: r) = (o, idLen (c :: r)) :: scan .code true st (o + 1) r) := by
  cases m with
  | code =>
    by_cases h1 : c = 47 ∧ r.head? = some 47
    · exact Or.inl ⟨.cmt, false, st, by simp only [scan]; rw [Lsp.iteT h1]⟩
    · by_cases h2 : c = 34
      · exact Or.inl ⟨.str, false, st, by simp only [scan]; rw [Lsp.iteF h1, Lsp.iteT h2]⟩
      · by_cases h3 : c = 39
        · exact Or.inl ⟨.chr, false, st, by simp only [scan]; rw [Lsp.iteF h1, Lsp.iteF h2, Lsp.iteT h3]⟩
        · by_cases h4 : c = 123
          · exact Or.inl ⟨.code, false, depthUp st, by
              simp only [scan]; rw [Lsp.iteF h1, Lsp.iteF h2, Lsp.iteF h3, Lsp.iteT h4]⟩
          · by_cases h5 : c = 125 ∧ st.head? = some 0
            · exact Or.inl ⟨.str, false, st.tail, by
                simp only [scan]; rw [Lsp.iteF h1, Lsp.iteF h2, Lsp.iteF h3, Lsp.iteF h4, Lsp.iteT h5]⟩
            · by_cases h6 : c = 125
              · exact Or.inl ⟨.code, false, depthDown st, by
                  simp only [scan]; rw [Lsp.iteF h1, Lsp.iteF h2, Lsp.iteF h3, Lsp.iteF h4, Lsp.iteF h5, Lsp.iteT h6]⟩
              · by_cases h7 : isId c = true
                · by_cases h8 : (p || isDigit c) = true
                  · exact Or.inl ⟨.code, true, st, by
                      simp only [scan]
                      rw [Lsp.iteF h1, Lsp.iteF h2, Lsp.iteF h3, Lsp.iteF h4, Lsp.iteF h5, Lsp.iteF h6, Lsp.iteT h7, Lsp.iteT h8]⟩
                  · exact Or.inr ⟨h7, by
                      simp only [scan]
                      rw [Lsp.iteF h1, Lsp.iteF h2, Lsp.iteF h3, Lsp.iteF h4, Lsp.iteF h5, Lsp.iteF h6, Lsp.iteT h7, Lsp.iteF h8]⟩
                · exact Or.inl ⟨.code, false, st, by
                    simp only [scan]
                    rw [Lsp.iteF h1, Lsp.iteF h2, Lsp.iteF h3, Lsp.iteF h4, Lsp.iteF h5, Lsp.iteF h6, Lsp.iteF h7]⟩
  | str =>
    by_cases h1 : c = 92
    · exact Or.inl ⟨.esc, false, st, by simp only [scan]; rw [Lsp.iteT h1]⟩
    · by_cases h2 : c = 34
      · exact Or.inl ⟨.code, false, st, by simp only [scan]; rw [Lsp.iteF h1, Lsp.iteT h2]⟩
      · by_cases h3 : c = 35 ∧ r.head? = some 123
        · exact Or.inl ⟨.hash, false, st, by simp only [scan]; rw [Lsp.iteF h1, Lsp.iteF h2, Lsp.iteT h3]⟩
        · exact Or.inl ⟨.str, false, st, by simp only [scan]; rw [Lsp.iteF h1, Lsp.iteF h2, Lsp.iteF h3]⟩
  | hash => exact Or.inl ⟨.code, false, 0 :: st, by simp only [scan]⟩
  | esc => exact Or.inl ⟨.str, false, st, by simp only [scan]⟩
  | cmt =>
    by_cases h1 : c = 10
    · exact Or.inl ⟨.code, false, st, by simp only [scan]; rw [Lsp.iteT h1]⟩
    · exact Or.inl ⟨.cmt, false, st, by simp only [scan]; rw [Lsp.iteF h1]⟩
  | chr =>
    by_cases h1 : c = 92
    · exact Or.inl ⟨.chrEsc, false, st, by simp only [scan]; rw [Lsp.iteT h1]⟩
    · by_cases h2 : c = 39
      · exact Or.inl ⟨.code, false, st, by simp only [scan]; rw [Lsp.iteF h1, Lsp.iteT h2]⟩
      · exact Or.inl ⟨.chr, false, st, by simp only [scan]; rw [Lsp.iteF h1, Lsp.iteF h2]⟩
  | chrEsc => exact Or.inl ⟨.chr, false, st, by simp only [scan]⟩

theorem scan_nil (m : M) (p : Bool) (st : List Nat) (o : Nat) : scan m p st o [] = [] := by
  cases m <;> simp [scan]

theorem scan_ge : ∀ (l : List Nat) (m : M) (p : Bool) (st : List Nat) (o : Nat), ∀ x ∈ scan m p st o l, o ≤ x.1
  | [], m, p, st, o => by
    intro x hx
    rw [scan_nil] at hx
    simp at hx
  | c :: r, m, p, st, o => by
    intro x hx
    rcases scan_cons m p st o c r with ⟨m', p', st', h⟩ | ⟨_, h⟩
    · rw [h] at hx
      have := scan_ge r m' p' st' (o + 1) x hx
      omega
    · rw [h] at hx
      rcases List.mem_cons.mp hx with hx | hx
      · rw [hx]
        exact Nat.le_refl _
      · have := scan_ge r .code true st (o + 1) x hx
        omega

theorem scan_word : ∀ (l : List Nat) (m : M) (p : Bool) (st : List Nat) (o : Nat), ∀ x ∈ scan m p st o l,
    o ≤ x.1 ∧ x.2 = idLen (l.drop (x.1 - o)) ∧ 0 < x.2
  | [], m, p, st, o => by
    intro x hx
    rw [scan_nil] at hx
    simp at hx
  | c :: r, m, p, st, o => by
    intro x hx
    rcases scan_cons m p st o c r with ⟨m', p', st', h⟩ | ⟨hc, h⟩
    · rw [h] at hx
      obtain ⟨h1, h2, h3⟩ := scan_word r m' p' st' (o + 1) x hx
      refine ⟨by omega, ?_, h3⟩
      rw [show x.1 - o = (x.1 - (o + 1)) + 1 by omega, List.drop_succ_cons]
      exact h2
    · rw [h] at hx
      rcases List.mem_cons.mp hx with hx | hx
      · rw [hx]
        refine ⟨Nat.le_refl _, by simp, ?_⟩
        simp [idLen, hc]
      · obtain ⟨h1, h2, h3⟩ := scan_word r .code true st (o + 1) x hx
        refine ⟨by omega, ?_, h3⟩
        rw [show x.1 - o = (x.1 - (o + 1)) + 1 by omega, List.drop_succ_cons]
        exact h2

theorem scan_code_id (st : List Nat) (o c : Nat) (r : List Nat) (hc : isId c = true) :
    scan .code true st o (c :: r) = scan .code true st (o + 1) r := by
  have h1 : c ≠ 47 := by
    intro e
    rw [e] at hc
    simp [isId] at hc
  have h2 : c ≠ 34 := by
    intro e
    rw [e] at hc
    simp [isId] at hc
  have h3 : c ≠ 39 := by
    intro e
    rw [e] at hc
    simp [isId] at hc
  have h4 : c ≠ 123 := by
    intro e
    rw [e] at hc
    simp [isId] at hc
  have h5 : c ≠ 125 := by
    intro e
    rw [e] at hc
    simp [isId] at hc
  simp [scan, h1, h2, h3, h4, h5, hc]

/-- 上一个字节是标识符的字节时，这一串标识符的字节里不会开始新的词 -/
theorem run_skip : ∀ (l : List Nat) (st : List Nat) (o : Nat), ∀ x ∈ scan .code true st o l, o + idLen l ≤ x.1
  | [], st, o => by
    intro x hx
    rw [scan_nil] at hx
    simp at hx
  | c :: r, st, o => by
    intro x hx
    by_cases hc : isId c = true
    · rw [scan_code_id st o c r hc] at hx
      have := run_skip r st (o + 1) x hx
      simp only [idLen, hc, ↓reduceIte]
      omega
    · have := scan_ge (c :: r) .code true st o x hx
      have e : idLen (c :: r) = 0 := by simp [idLen, hc]
      rw [e]
      omega

theorem scan_disjoint : ∀ (l : List Nat) (m : M) (p : Bool) (st : List Nat) (o : Nat),
    (scan m p st o l).Pairwise (fun a b => a.1 + a.2 ≤ b.1)
  | [], m, p, st, o => by
    rw [scan_nil]
    exact List.Pairwise.nil
  | c :: r, m, p, st, o => by
    rcases scan_cons m p st o c r with ⟨m', p', st', h⟩ | ⟨hc, h⟩
    · rw [h]
      exact scan_disjoint r m' p' st' (o + 1)
    · rw [h]
      refine List.Pairwise.cons ?_ (scan_disjoint r .code true st (o + 1))
      intro x hx
      -- 出了词以后上一个字节是标识符的字节，这一串里不会再出词
      have := run_skip r st (o + 1) x hx
      have e : idLen (c :: r) = idLen r + 1 := by simp [idLen, hc]
      show o + idLen (c :: r) ≤ x.1
      rw [e]
      omega

/-! ## LSP 的编码：相对前一个的差 -/

/-- 一个词：(行, 列, 长度, 种类, 修饰) -/
abbrev Tok := Nat × Nat × Nat × Nat × Nat

def encode : Nat × Nat → List Tok → List Nat
  | _, [] => []
  | (l0, c0), (l, c, n, t, md) :: ts => (l - l0) :: (if l = l0 then c - c0 else c) :: n :: t :: md :: encode (l, c) ts

def decode : Nat × Nat → List Nat → List Tok
  | (l0, c0), dl :: dc :: n :: t :: md :: rest =>
    (l0 + dl, (if dl = 0 then c0 + dc else dc), n, t, md) :: decode (l0 + dl, if dl = 0 then c0 + dc else dc) rest
  | _, _ => []

/-- 按位置排好：行变大，或者同一行里列不变小 -/
def sorted : Nat × Nat → List Tok → Prop
  | _, [] => True
  | (l0, c0), (l, c, _, _, _) :: ts => (l0 < l ∨ (l = l0 ∧ c0 ≤ c)) ∧ sorted (l, c) ts

theorem decode_encode : ∀ (ts : List Tok) (s : Nat × Nat), sorted s ts → decode s (encode s ts) = ts
  | [], s, _ => by
    obtain ⟨l0, c0⟩ := s
    simp [encode, decode]
  | (l, c, n, t, md) :: ts, (l0, c0), h => by
    obtain ⟨h1, h2⟩ := h
    simp only [encode, decode]
    have hl : l0 + (l - l0) = l := by omega
    have hc : (if l - l0 = 0 then c0 + (if l = l0 then c - c0 else c) else (if l = l0 then c - c0 else c)) = c := by
      by_cases e : l = l0
      · rw [Lsp.iteT (show l - l0 = 0 by omega), Lsp.iteT e]
        omega
      · rw [Lsp.iteF (show ¬(l - l0 = 0) by omega), Lsp.iteF e]
    rw [hl, hc, decode_encode ts (l, c) h2]

/-! ## 例子 -/

#guard words (Lsp.bs "fn f(x: int) { x }") == [(0, 2), (3, 1), (5, 1), (8, 3), (15, 1)]
-- 字符串、注释、字符字面量里面不出词；转义的引号不结束字符串
#guard words (Lsp.bs "a \"b \\\" c\" d // e f\ng 'h' i") == [(0, 1), (11, 1), (20, 1), (26, 1)]
-- 数字开头的不是词（0xff、1_000、2e5）；标识符里的数字是词的一部分
#guard words (Lsp.bs "0xff 1_000 x1 2e5") == [(11, 2)]
#guard words (Lsp.bs "a/b") == [(0, 1), (2, 1)]
-- 插值里是代码：x、f、g 出词，插值外面的字符串（a、b、h）不出；插值里的 {…} 配对了才回到字符串；\# 不是插值
#guard words (Lsp.bs "\"a #{x} b\" y") == [(5, 1), (11, 1)]
#guard words (Lsp.bs "\"#{f(\"#{g}\")} {h}\" k") == [(3, 1), (8, 1), (19, 1)]
#guard words (Lsp.bs "\"#{ {a} }b\" c") == [(5, 1), (12, 1)]
#guard words (Lsp.bs "\"\\#{x}\" y") == [(8, 1)]
#guard encode (0, 0) [(0, 3, 4, 1, 0), (0, 10, 2, 2, 1), (2, 4, 1, 3, 2)] == [0, 3, 4, 1, 0, 0, 7, 2, 2, 1, 2, 4, 1, 3, 2]
#guard decode (0, 0) [0, 3, 4, 1, 0, 0, 7, 2, 2, 1, 2, 4, 1, 3, 2] == [(0, 3, 4, 1, 0), (0, 10, 2, 2, 1), (2, 4, 1, 3, 2)]

end LspSem
end Lark
