/-
apps/llsp 的证明 · 阶段 7：格式化（LSP 规范的 “textDocument/formatting”）
先证明，再写 apps/llsp/lsp/format.lark。

做法：把文档交给现有的格式化工具（build/lark-fmt --stdout，不改它），得到格式化以后的 t。
不把整个文档换掉（编辑器里的光标会跳到末尾），只换中间不一样的那段：
- 开头一样的字节有 preLen d t 个，结尾一样的有 sufLen d t 个（两段不重叠）；
- 换的范围 [a, b)：a 往前退到最近的字符边界，b 往后进到最近的字符边界（不会切开 emoji 或者 \r\n），
  新文字是 t 里对应的那段；
- d 和 t 一样时不发修改。

证明了：
- `pre_take`、`pre_le`：开头 preLen 个（以及更少的）字节两边一样；
- `suf_ok`、`suf_le`：结尾 sufLen 个（以及更少的）字节两边一样，并且和开头那段不重叠（`pre_suf`）；
- `fmt_edit`：只要 a 不超过 preLen、d 里 b 之后的不超过 sufLen、a ≤ b，换掉 [a, b) 以后正好是 t；
- `fmt_change`：a、b 在字符边界上时，换成 LSP 的位置再按阶段 1 的 Lsp.change 作用（编辑器做的事），结果也正好是 t。
没证：格式化工具本身（它只改空白，见 tools/fmt.lark 的说明）；取字符边界的那几行（Lark 里）。
-/
import Lark.Lsp
import Lark.LspDef

namespace Lark
namespace LspFmt

/-! ## 开头一样的字节 -/

def preLen : List Nat → List Nat → Nat
  | x :: r, y :: s => if x = y then preLen r s + 1 else 0
  | _, _ => 0

theorem pre_take : ∀ d t : List Nat, d.take (preLen d t) = t.take (preLen d t)
  | [], _ => by simp [preLen]
  | _ :: _, [] => by simp [preLen]
  | x :: r, y :: s => by
    by_cases h : x = y
    · subst h
      simp [preLen, pre_take r s]
    · simp [preLen, h]

theorem pre_len : ∀ d t : List Nat, preLen d t ≤ d.length ∧ preLen d t ≤ t.length
  | [], _ => by simp [preLen]
  | _ :: _, [] => by simp [preLen]
  | x :: r, y :: s => by
    have := pre_len r s
    by_cases h : x = y <;> simp [preLen, h] <;> omega

theorem takeTake : ∀ (l : List Nat) (m n : Nat), m ≤ n → (l.take n).take m = l.take m
  | [], _, _, _ => by simp
  | _ :: _, 0, _, _ => by simp
  | _ :: _, _ + 1, 0, h => by omega
  | x :: r, m + 1, n + 1, h => by
    simp only [List.take_succ_cons]
    rw [takeTake r m n (by omega)]

theorem pre_le (d t : List Nat) (k : Nat) (h : k ≤ preLen d t) : d.take k = t.take k := by
  rw [← takeTake d k (preLen d t) h, ← takeTake t k (preLen d t) h, pre_take]

/-! ## 结尾一样的字节（不和开头那段重叠） -/

def sufOk (d t : List Nat) (k : Nat) : Prop := d.drop (d.length - k) = t.drop (t.length - k)

instance (d t : List Nat) (k : Nat) : Decidable (sufOk d t k) :=
  inferInstanceAs (Decidable (d.drop (d.length - k) = t.drop (t.length - k)))

/-- 从 n 往下找第一个结尾一样的长度 -/
def sufGo (d t : List Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => if sufOk d t (n + 1) then n + 1 else sufGo d t n

def sufLen (d t : List Nat) : Nat := sufGo d t (min d.length t.length - preLen d t)

theorem sufGo_ok (d t : List Nat) : ∀ n, sufOk d t (sufGo d t n)
  | 0 => by simp [sufGo, sufOk]
  | n + 1 => by
    by_cases h : sufOk d t (n + 1)
    · rw [sufGo, Lsp.iteT h]
      exact h
    · rw [sufGo, Lsp.iteF h]
      exact sufGo_ok d t n

theorem sufGo_le (d t : List Nat) : ∀ n, sufGo d t n ≤ n
  | 0 => by simp [sufGo]
  | n + 1 => by
    have := sufGo_le d t n
    by_cases h : sufOk d t (n + 1)
    · rw [sufGo, Lsp.iteT h]
      omega
    · rw [sufGo, Lsp.iteF h]
      omega

theorem suf_ok (d t : List Nat) : sufOk d t (sufLen d t) := sufGo_ok d t _

theorem pre_suf (d t : List Nat) : preLen d t + sufLen d t ≤ d.length ∧ preLen d t + sufLen d t ≤ t.length := by
  have h1 := sufGo_le d t (min d.length t.length - preLen d t)
  have h2 := pre_len d t
  have h3 := Nat.min_le_left d.length t.length
  have h4 := Nat.min_le_right d.length t.length
  unfold sufLen
  omega

/-- 结尾 k 个一样时，更少的也一样 -/
theorem suf_le (d t : List Nat) (k j : Nat) (hk : sufOk d t k) (hj : j ≤ k) (hd : k ≤ d.length) (ht : k ≤ t.length) :
    sufOk d t j := by
  unfold sufOk at *
  have e1 : d.drop (d.length - j) = (d.drop (d.length - k)).drop (k - j) := by
    rw [LspDef.dropdrop]
    congr 1
    omega
  have e2 : t.drop (t.length - j) = (t.drop (t.length - k)).drop (k - j) := by
    rw [LspDef.dropdrop]
    congr 1
    omega
  rw [e1, e2, hk]

/-! ## 换掉中间那段 -/

/-- 新文字：t 里去掉开头 a 个、结尾 (d 的长度 - b) 个以后的那段 -/
def mid (d t : List Nat) (a b : Nat) : List Nat := (t.drop a).take (t.length - (d.length - b) - a)

theorem fmt_edit (d t : List Nat) (a b : Nat) (ha : a ≤ preLen d t) (hb : d.length - b ≤ sufLen d t)
    (_hab : a ≤ b) (hbd : b ≤ d.length) : Lsp.edit d a b (mid d t a b) = t := by
  have hps := pre_suf d t
  have hs : sufOk d t (d.length - b) := suf_le d t _ _ (suf_ok d t) hb (by omega) (by omega)
  unfold sufOk at hs
  have hb' : d.length - (d.length - b) = b := by omega
  rw [hb'] at hs
  have hc : a + (t.length - (d.length - b) - a) = t.length - (d.length - b) := by omega
  unfold Lsp.edit mid
  rw [pre_le d t a ha, hs]
  have h3 := List.take_append_drop (t.length - (d.length - b) - a) (t.drop a)
  rw [LspDef.dropdrop, hc] at h3
  rw [List.append_assoc, h3, List.take_append_drop]

/-- 编辑器做的事：a、b 是字符边界（文档的前 i、前 j 个元素）时，换成 LSP 的位置、再按 Lsp.change 作用，结果正好是 t -/
theorem fmt_change (u : List Nat → Nat) (hu : ∀ e : List Nat, e ≠ [] → 0 < u e) (d t : List Nat) (i j : Nat)
    (ha : Lsp.blen ((Lsp.doc d).take i) ≤ preLen d t)
    (hb : d.length - Lsp.blen ((Lsp.doc d).take j) ≤ sufLen d t)
    (hab : Lsp.blen ((Lsp.doc d).take i) ≤ Lsp.blen ((Lsp.doc d).take j)) :
    Lsp.change u d (Lsp.posOf u (Lsp.doc d) (Lsp.blen ((Lsp.doc d).take i)))
      (Lsp.posOf u (Lsp.doc d) (Lsp.blen ((Lsp.doc d).take j)))
      (mid d t (Lsp.blen ((Lsp.doc d).take i)) (Lsp.blen ((Lsp.doc d).take j))) = t := by
  have hbd : Lsp.blen ((Lsp.doc d).take j) ≤ d.length := by
    have := Lsp.blen_take_le (Lsp.doc d) j
    rw [Lsp.blen_doc] at this
    exact this
  unfold Lsp.change
  rw [Lsp.pos_off u hu (Lsp.doc d) (Lsp.doc_ne d) i, Lsp.pos_off u hu (Lsp.doc d) (Lsp.doc_ne d) j,
    Nat.min_eq_left hab, Nat.max_eq_right hab]
  exact fmt_edit d t _ _ ha hb hab hbd

/-! ## 例子 -/

def d1 : List Nat := Lsp.bs "fn  main( ) {}\n"
def t1 : List Nat := Lsp.bs "fn main() {}\n"
#guard preLen d1 t1 == 3
#guard sufLen d1 t1 == 5
#guard Lsp.edit d1 3 10 (mid d1 t1 3 10) == t1
#guard mid d1 t1 3 10 == Lsp.bs "main("

-- 不一样的地方在 emoji 中间（😀 F0 9F 98 80 → 😁 F0 9F 98 81）：a 从 4 退到字符边界 1
def d2 : List Nat := [97, 0xF0, 0x9F, 0x98, 0x80, 120]
def t2 : List Nat := [97, 0xF0, 0x9F, 0x98, 0x81, 120]
#guard preLen d2 t2 == 4
#guard sufLen d2 t2 == 1
#guard Lsp.posOf Lsp.u16 (Lsp.doc d2) 1 == (0, 1)
#guard Lsp.posOf Lsp.u16 (Lsp.doc d2) 5 == (0, 3)
#guard Lsp.change Lsp.u16 d2 (0, 1) (0, 3) (mid d2 t2 1 5) == t2

-- 一样的时候：开头一样的就是整个文档
#guard preLen t1 t1 == t1.length
#guard sufLen t1 t1 == 0

end LspFmt
end Lark
