/-
apps/llsp 的证明 · 阶段 8：补全（LSP 规范的 “textDocument/completion”）
先证明，再写 apps/llsp/lsp/complete.lark。

做法：光标前面那半个词是前缀（prefixAt），候选是：
- 光标前不是 `模块.`：本文件的声明（阶段 5 的 LspDef.decls）和关键字、内置类型（kwNames）；
- 光标前是 `模块.`：import 进来的那个文件里 `pub` 的声明（pubNames；别的模块的私有名字用不了）。
留下以前缀开头的，去掉重复的（uniq）。

证明了：
- `complete_iff`：补全的每一项都是候选、都以前缀开头；反过来，每个以前缀开头的候选都在补全里（一个不漏）；
- `complete_nodup`：没有重复的；
- `local_sound`：本文件补全的每一项要么是关键字，要么是本文件真有的声明（在它的偏移上正好是这个名字，LspDef.decls_word）；
- `module_sound`：`模块.` 补全的每一项是那个文件真有的、`pub` 的声明。
没证：import 的路径怎么对应到文件（和阶段 5 一样）；方法、字段、局部变量、标准库（以后再加）。
-/
import Lark.Lsp
import Lark.LspDef

namespace Lark
namespace LspComp

open LspDef

/-! ## 去掉重复的（留最后一个） -/

def uniq : List (List Nat) → List (List Nat)
  | [] => []
  | x :: r => if x ∈ r then uniq r else x :: uniq r

theorem mem_uniq : ∀ (l : List (List Nat)) (x : List Nat), x ∈ uniq l ↔ x ∈ l
  | [], x => by simp [uniq]
  | y :: r, x => by
    by_cases h : y ∈ r
    · simp only [uniq]
      rw [Lsp.iteT h, mem_uniq r x, List.mem_cons]
      constructor
      · exact Or.inr
      · intro hx
        rcases hx with hx | hx
        · rw [hx]
          exact h
        · exact hx
    · simp only [uniq]
      rw [Lsp.iteF h]
      simp only [List.mem_cons, mem_uniq r x]

theorem nodup_uniq : ∀ l : List (List Nat), (uniq l).Nodup
  | [] => by simp [uniq]
  | y :: r => by
    by_cases h : y ∈ r
    · simp only [uniq]
      rw [Lsp.iteT h]
      exact nodup_uniq r
    · simp only [uniq]
      rw [Lsp.iteF h]
      exact List.nodup_cons.mpr ⟨fun hm => h ((mem_uniq r y).mp hm), nodup_uniq r⟩

/-! ## 补全 -/

def complete (cs : List (List Nat)) (pre : List Nat) : List (List Nat) := uniq (cs.filter (fun n => pre.isPrefixOf n))

theorem complete_iff (cs : List (List Nat)) (pre n : List Nat) :
    n ∈ complete cs pre ↔ n ∈ cs ∧ pre.isPrefixOf n = true := by
  unfold complete
  rw [mem_uniq, List.mem_filter]

theorem complete_nodup (cs : List (List Nat)) (pre : List Nat) : (complete cs pre).Nodup := nodup_uniq _

/-- 光标 o 前面那半个词 -/
def prefixAt (d : List Nat) (o : Nat) : List Nat := (d.take o).drop (wordStart d o)

/-! ## 候选 -/

def kwNames : List (List Nat) :=
  ["fn", "type", "enum", "interface", "const", "pub", "import", "if", "else", "match", "for", "in", "return",
   "break", "continue", "true", "false", "take", "inout", "scope", "select", "int", "float", "u8", "bool", "str"].map Lsp.bs

def cands (d : List Nat) : List (List Nat) := (decls d).map Prod.fst ++ kwNames

theorem local_sound (d pre n : List Nat) (h : n ∈ complete (cands d) pre) :
    pre.isPrefixOf n = true ∧ (n ∈ kwNames ∨ ∃ p, (n, p) ∈ decls d ∧ wordAtHead (d.drop p) n) := by
  rw [complete_iff] at h
  obtain ⟨hm, hp⟩ := h
  refine ⟨hp, ?_⟩
  unfold cands at hm
  rw [List.mem_append, List.mem_map] at hm
  rcases hm with ⟨⟨m, p⟩, hmp, he⟩ | hk
  · right
    subst he
    exact ⟨p, hmp, decls_word d m p hmp⟩
  · left
    exact hk

/-- 偏移 p 所在的行的开头 -/
def lineBeg (d : List Nat) : Nat → Nat
  | 0 => 0
  | p + 1 => if (d.drop p).head? = some 10 then p + 1 else lineBeg d p

def isPub (d : List Nat) (p : Nat) : Bool := (Lsp.bs "pub ").isPrefixOf (d.drop (lineBeg d p))

/-- 别的模块能用的名字：`pub` 的声明 -/
def pubNames (t : List Nat) : List (List Nat) := ((decls t).filter (fun e => isPub t e.2)).map Prod.fst

theorem module_sound (t pre n : List Nat) (h : n ∈ complete (pubNames t) pre) :
    pre.isPrefixOf n = true ∧ ∃ p, (n, p) ∈ decls t ∧ isPub t p = true ∧ wordAtHead (t.drop p) n := by
  rw [complete_iff] at h
  obtain ⟨hm, hp⟩ := h
  refine ⟨hp, ?_⟩
  unfold pubNames at hm
  rw [List.mem_map] at hm
  obtain ⟨⟨m, p⟩, hmp, he⟩ := hm
  rw [List.mem_filter] at hmp
  obtain ⟨hd, hpub⟩ := hmp
  subst he
  exact ⟨p, hd, hpub, decls_word t m p hd⟩

/-! ## 例子（LspDef 的 src） -/

#guard prefixAt src 97 == Lsp.bs "ad"
#guard complete (cands src) (prefixAt src 97) == [Lsp.bs "add1"]
#guard complete (cands src) (Lsp.bs "m") == [Lsp.bs "main", Lsp.bs "match"]
#guard complete (cands src) (Lsp.bs "P") == [Lsp.bs "P"]
#guard complete (cands src) (Lsp.bs "zz") == []
#guard pubNames src == [Lsp.bs "add1"]
#guard isPub src 25 == true
#guard isPub src 60 == false
-- 同名的声明只出现一次
#guard complete (cands (Lsp.bs "fn f()\nfn f()\n")) (Lsp.bs "f") ==
  [Lsp.bs "f", Lsp.bs "fn", Lsp.bs "for", Lsp.bs "false", Lsp.bs "float"]
-- 光标在词的开头：前缀是空的，全部候选
#guard (complete (cands src) (prefixAt src 95)).length == 4 + kwNames.length

end LspComp
end Lark
