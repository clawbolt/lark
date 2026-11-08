/-
apps/llsp 的证明 · 阶段 6：文档大纲（LSP 规范的 “textDocument/documentSymbol”）
先证明，再写 apps/llsp/lsp/symbols.lark。

做法：大纲就是阶段 5 扫出来的声明（LspDef.decls），每个再标上种类（按声明的关键字，LSP 的 SymbolKind）：
fn → Function（12）、type → Struct（23）、enum → Enum（10）、const → Constant（14）、interface → Interface（11）。

证明了：
- `symbols_decls`：大纲去掉种类以后正好是 decls，一个不多一个不少、顺序一样；
- `symbols_word`：大纲里每一项在它的偏移上正好是这个名字，是完整的词（来自 LspDef.decls_word）；
- `symbols_in`：每一项的范围 [偏移, 偏移 + 名字的长度) 在文档里面；
- 种类：行首（`pub ` 之后）的关键字对应的那个（下面的 #guard）。
没证：大纲只有一层（方法、枚举的变体、字段以后再加）；范围只是名字，不是整个声明。
-/
import Lark.Lsp
import Lark.LspDef

namespace Lark
namespace LspSym

open LspDef

/-- 行首（`pub ` 之后）的关键字对应的 SymbolKind；没有关键字时是 0（不会用到：没有关键字就不是声明） -/
def kindOf (l : List Nat) : Nat :=
  if (Lsp.bs "fn ").isPrefixOf (l.drop (pre l)) = true then 12
  else if (Lsp.bs "type ").isPrefixOf (l.drop (pre l)) = true then 23
  else if (Lsp.bs "enum ").isPrefixOf (l.drop (pre l)) = true then 10
  else if (Lsp.bs "const ").isPrefixOf (l.drop (pre l)) = true then 14
  else if (Lsp.bs "interface ").isPrefixOf (l.drop (pre l)) = true then 11
  else 0

/-- 大纲：(名字, 名字的偏移, 种类)，按位置排 -/
def symbols (d : List Nat) : List (List Nat × Nat × Nat) :=
  (List.range (d.length + 1)).filterMap
    (fun o => if lineStart d o = true then (declAt (d.drop o)).map (fun q => (q.2, o + q.1, kindOf (d.drop o))) else none)

theorem symbols_pt (d : List Nat) (o : Nat) :
    (if lineStart d o = true then (declAt (d.drop o)).map (fun q => (q.2, o + q.1, kindOf (d.drop o))) else none).map
      (fun s : List Nat × Nat × Nat => (s.1, s.2.1)) =
    (if lineStart d o = true then (declAt (d.drop o)).map (fun q => (q.2, o + q.1)) else none) := by
  by_cases hl : lineStart d o = true
  · rw [Lsp.iteT hl, Lsp.iteT hl]
    cases declAt (d.drop o) <;> rfl
  · rw [Lsp.iteF hl, Lsp.iteF hl]
    rfl

theorem symbols_decls (d : List Nat) : (symbols d).map (fun s => (s.1, s.2.1)) = decls d := by
  unfold symbols decls
  rw [List.map_filterMap]
  congr 1
  funext o
  exact symbols_pt d o

theorem symbols_mem (d n : List Nat) (p k : Nat) (h : (n, p, k) ∈ symbols d) : (n, p) ∈ decls d := by
  rw [← symbols_decls d]
  exact List.mem_map_of_mem (f := fun s => (s.1, s.2.1)) h

theorem symbols_word (d n : List Nat) (p k : Nat) (h : (n, p, k) ∈ symbols d) : wordAtHead (d.drop p) n :=
  decls_word d n p (symbols_mem d n p k h)

theorem take_len_le (x n : List Nat) (h : x.take n.length = n) : n.length ≤ x.length := by
  have h1 := congrArg List.length h
  rw [List.length_take] at h1
  omega

theorem symbols_in (d n : List Nat) (p k : Nat) (h : (n, p, k) ∈ symbols d) : p + n.length ≤ d.length := by
  obtain ⟨ht, hne, _, _⟩ := symbols_word d n p k h
  have h1 := take_len_le (d.drop p) n ht
  rw [List.length_drop] at h1
  have hn : n.length ≠ 0 := fun h0 => hne (List.eq_nil_of_length_eq_zero h0)
  omega

/-! ## 例子（LspDef 的 src） -/

#guard symbols src == [(Lsp.bs "add1", 25, 12), (Lsp.bs "P", 60, 23), (Lsp.bs "main", 80, 12), (Lsp.bs "N", 112, 14)]
#guard symbols (Lsp.bs "pub enum Got {\n  Msg\n}\npub interface Show {}\n") == [(Lsp.bs "Got", 9, 10), (Lsp.bs "Show", 37, 11)]
#guard kindOf (Lsp.bs "fn f()") == 12
#guard kindOf (Lsp.bs "pub fn f()") == 12
#guard kindOf (Lsp.bs "type T {") == 23
#guard kindOf (Lsp.bs "pub enum E {") == 10
#guard kindOf (Lsp.bs "const N = 1") == 14
#guard kindOf (Lsp.bs "interface I {}") == 11
#guard kindOf (Lsp.bs "x = 1") == 0

end LspSym
end Lark
