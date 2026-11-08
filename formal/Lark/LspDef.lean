/-
apps/llsp 的证明 · 阶段 5：跳到定义（LSP 规范的 “textDocument/definition”）
先证明，再写 apps/llsp/lsp/defn.lark。

做法：llsp 自己扫描源文件，不经过编译器：
- 光标下的词：往左、往右数标识符的字节（和 compiler/lex.lark 一样：ASCII 字母、数字、_）；
- 声明：行首（可以先写 `pub `）是 `fn `、`type `、`enum `、`const `、`interface ` 时，后面的标识符是声明的名字；
- 找名字：第一个同名的声明。`模块.名字` 时先找 import 进来的那个文件（Lark 里，没证）。

证明了：
- `word_bounds`：光标下的词包含光标，不超出文档；`word_end`：词往右已经到头（下一个字节不是标识符）；
- `decls_word`：扫出来的每个声明，在它的偏移上正好是这个名字，名字非空、都是标识符的字节，并且是完整的词
  （后面不是标识符的字节，不会把 `add1` 当成 `add`）；
- `find_word`：找到的定义满足同样的性质，名字就是要找的那个；`find_line`：定义在某一行的开头之后、同一行上。
没证：import 的路径怎么对应到文件；方法、枚举的变体、局部变量（以后再加）。
-/
import Lark.Lsp

namespace Lark
namespace LspDef

/-! ## 标识符 -/

def isId (c : Nat) : Bool := (97 ≤ c && c ≤ 122) || (65 ≤ c && c ≤ 90) || c == 95 || (48 ≤ c && c ≤ 57)

/-- 开头有几个标识符的字节 -/
def idLen : List Nat → Nat
  | [] => 0
  | x :: r => if isId x then idLen r + 1 else 0

theorem idLen_le : ∀ l : List Nat, idLen l ≤ l.length
  | [] => by simp [idLen]
  | x :: r => by
    have := idLen_le r
    by_cases hx : isId x = true <;> simp [idLen, hx] <;> omega

theorem idLen_all : ∀ l : List Nat, (l.take (idLen l)).all isId = true
  | [] => by simp [idLen]
  | x :: r => by
    by_cases hx : isId x = true
    · simp [idLen, hx, idLen_all r]
    · simp [idLen, hx]

theorem idLen_stop : ∀ (l : List Nat) (y : Nat), (l.drop (idLen l)).head? = some y → isId y = false
  | [], y, h => by simp [idLen] at h
  | x :: r, y, h => by
    by_cases hx : isId x = true
    · simp only [idLen, hx, ↓reduceIte, List.drop_succ_cons] at h
      exact idLen_stop r y h
    · have hf : isId x = false := by simpa using hx
      simp [idLen, hf] at h
      subst h
      exact hf

theorem dropdrop : ∀ (d : List Nat) (o k : Nat), (d.drop o).drop k = d.drop (o + k)
  | d, 0, k => by simp
  | [], o + 1, k => by simp
  | x :: r, o + 1, k => by
    rw [show o + 1 + k = (o + k) + 1 by omega, List.drop_succ_cons, List.drop_succ_cons, dropdrop r o k]

/-! ## 光标下的词：[wordStart, wordEnd) -/

def wordEnd (d : List Nat) (o : Nat) : Nat := o + idLen (d.drop o)
def wordStart (d : List Nat) (o : Nat) : Nat := o - idLen (d.take o).reverse
def word (d : List Nat) (o : Nat) : List Nat := (d.drop (wordStart d o)).take (wordEnd d o - wordStart d o)

theorem word_bounds (d : List Nat) (o : Nat) (h : o ≤ d.length) :
    wordStart d o ≤ o ∧ o ≤ wordEnd d o ∧ wordEnd d o ≤ d.length := by
  have := idLen_le (d.drop o)
  simp only [List.length_drop] at this
  unfold wordStart wordEnd
  omega

theorem word_end (d : List Nat) (o y : Nat) (h : (d.drop (wordEnd d o)).head? = some y) : isId y = false := by
  unfold wordEnd at h
  rw [← dropdrop] at h
  exact idLen_stop _ y h

/-! ## 声明 -/

def kws : List (List Nat) := [Lsp.bs "fn ", Lsp.bs "type ", Lsp.bs "enum ", Lsp.bs "const ", Lsp.bs "interface "]

/-- 开头是哪个关键字，关键字（连同空格）有多长 -/
def afterKw (l : List Nat) : Option Nat := (kws.find? (fun k => k.isPrefixOf l)).map List.length

/-- 开头的 `pub ` 有多长 -/
def pre (l : List Nat) : Nat := if (Lsp.bs "pub ").isPrefixOf l = true then 4 else 0

def nameAt (l : List Nat) (k : Nat) : List Nat := (l.drop k).take (idLen (l.drop k))

/-- 一行开头的声明：(名字在这一行里的偏移, 名字) -/
def declAt (l : List Nat) : Option (Nat × List Nat) :=
  match afterKw (l.drop (pre l)) with
  | some k => if nameAt l (pre l + k) = [] then none else some (pre l + k, nameAt l (pre l + k))
  | none => none

theorem declAt_some (l : List Nat) (k : Nat) (n : List Nat) (h : declAt l = some (k, n)) :
    n = (l.drop k).take (idLen (l.drop k)) ∧ n ≠ [] := by
  unfold declAt at h
  split at h
  · split at h
    · simp at h
    · rename_i hc
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨rfl, hc⟩
  · simp at h

def lineStart (d : List Nat) (o : Nat) : Bool := o == 0 || (d.drop (o - 1)).head? == some 10

/-- 文档里所有的声明：(名字, 名字的偏移)，按位置排 -/
def decls (d : List Nat) : List (List Nat × Nat) :=
  (List.range (d.length + 1)).filterMap
    (fun o => if lineStart d o = true then (declAt (d.drop o)).map (fun q => (q.2, o + q.1)) else none)

/-- 名字正好在 x 的开头，是完整的词 -/
def wordAtHead (x n : List Nat) : Prop :=
  x.take n.length = n ∧ n ≠ [] ∧ n.all isId = true ∧ ∀ y, (x.drop n.length).head? = some y → isId y = false

theorem word_prop (x m : List Nat) (hm : m = x.take (idLen x)) (hne : m ≠ []) : wordAtHead x m := by
  have hl : m.length = idLen x := by
    rw [hm, List.length_take]
    have := idLen_le x
    omega
  refine ⟨?_, hne, ?_, ?_⟩
  · rw [hl]
    exact hm.symm
  · rw [hm]
    exact idLen_all x
  · rw [hl]
    exact idLen_stop x

theorem decls_mem (d : List Nat) (n : List Nat) (p : Nat) (h : (n, p) ∈ decls d) :
    ∃ o k, lineStart d o = true ∧ declAt (d.drop o) = some (k, n) ∧ p = o + k := by
  unfold decls at h
  rw [List.mem_filterMap] at h
  obtain ⟨o, _, ho0⟩ := h
  have ho : (if lineStart d o = true then (declAt (d.drop o)).map (fun q => (q.2, o + q.1)) else none) = some (n, p) := ho0
  by_cases hl : lineStart d o = true
  · rw [Lsp.iteT hl] at ho
    cases hd : declAt (d.drop o) with
    | none =>
      rw [hd] at ho
      simp at ho
    | some q =>
      obtain ⟨k, m⟩ := q
      rw [hd] at ho
      simp at ho
      obtain ⟨rfl, rfl⟩ := ho
      exact ⟨o, k, hl, hd, rfl⟩
  · rw [Lsp.iteF hl] at ho
    simp at ho

theorem decls_word (d : List Nat) (n : List Nat) (p : Nat) (h : (n, p) ∈ decls d) : wordAtHead (d.drop p) n := by
  obtain ⟨o, k, _, hd, rfl⟩ := decls_mem d n p h
  obtain ⟨hn, hne⟩ := declAt_some _ _ _ hd
  have := word_prop ((d.drop o).drop k) n hn hne
  rw [dropdrop d o k] at this
  exact this

/-! ## 找定义 -/

def find (d n : List Nat) : Option Nat := ((decls d).find? (fun e => e.1 == n)).map (·.2)

theorem find_mem (d n : List Nat) (p : Nat) (h : find d n = some p) : (n, p) ∈ decls d := by
  unfold find at h
  cases hf : (decls d).find? (fun e => e.1 == n) with
  | none =>
    rw [hf] at h
    simp at h
  | some e =>
    obtain ⟨e1, e2⟩ := e
    rw [hf] at h
    simp at h
    have h1 := List.mem_of_find?_eq_some hf
    have h2 := List.find?_some hf
    simp at h2
    subst h h2
    exact h1

theorem find_word (d n : List Nat) (p : Nat) (h : find d n = some p) : wordAtHead (d.drop p) n :=
  decls_word d n p (find_mem d n p h)

/-- 定义在某一行开头 o 之后，o 和名字之间没有换行（声明的关键字和名字在同一行） -/
theorem find_line (d n : List Nat) (p : Nat) (h : find d n = some p) :
    ∃ o, lineStart d o = true ∧ o ≤ p ∧ declAt (d.drop o) = some (p - o, n) := by
  obtain ⟨o, k, hl, hd, rfl⟩ := decls_mem d n p (find_mem d n p h)
  refine ⟨o, hl, by omega, ?_⟩
  rw [show o + k - o = k by omega]
  exact hd

/-! ## 例子 -/

def src : List Nat := Lsp.bs
  "import \"lsp/pos\"\n\npub fn add1(x: int) -> int { x + 1 }\ntype P {\n    x: int\n}\nfn main() { print(add1(2)) }\nconst N = 3\n"

#guard decls src == [(Lsp.bs "add1", 25), (Lsp.bs "P", 60), (Lsp.bs "main", 80), (Lsp.bs "N", 112)]
#guard find src (Lsp.bs "P") == some 60
#guard find src (Lsp.bs "add") == none        -- 不会把 add1 当成 add
#guard find src (Lsp.bs "x") == none          -- 字段、参数不是声明
-- 光标在调用 add1(2) 的 d 上
#guard wordStart src 97 == 95
#guard wordEnd src 97 == 99
#guard word src 97 == Lsp.bs "add1"
#guard find src (word src 97) == some 25
-- 光标在词的结尾（紧挨着括号）也算这个词
#guard word src 99 == Lsp.bs "add1"
#guard declAt (Lsp.bs "pub enum Got {") == some (9, Lsp.bs "Got")
#guard declAt (Lsp.bs "fnx y") == none
#guard declAt (Lsp.bs "fn (") == none

end LspDef
end Lark
