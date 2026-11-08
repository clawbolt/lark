/-
apps/llsp 的证明 · 阶段 4：诊断（LSP 规范的 “textDocument/publishDiagnostics”）
先证明，再写 apps/llsp/lsp/diag.lark。

做法：文档打开或者改了以后，把内容交给编译器（lark1），把它的错误（标准错误里的 “文件:行:列: 类别：信息”）
换成 LSP 的诊断发给编辑器。两边的位置不一样：
- 编译器：行、列都从 1 数，列是字节数，只有 \n 换行；
- LSP：行、列从 0 数，列按商量好的单位（UTF-16 或字节）数，\r、\n、\r\n 都换行。
所以先按编译器的规则换成字节偏移（cOff），再用阶段 1 证明过的 posOf 换成 LSP 的位置。

证明了：
- `c_round`：字节偏移 → 编译器的行列（cPos）→ 字节偏移，不变；`cOff_le`：任何行列换成的偏移都不超过文档的长度；
- `dpos_exact`、`diag_round`：编译器指着某个字符的开头时，编辑器里标在同一个字节上（不管 \r、emoji、UTF-16）；
- `parse_fmt`：编译器写出的那一行能读回行、列和信息；
- `pubs_latest`：发诊断的一定是这次通知的文档，带的是它最新的版本，关掉时发空的（清掉）；
- `pubs_quiet`：不发诊断的通知（旧版本、没打开）什么都没改；`pubs_len`：每条通知最多发一次。
没证：编译器本身报的错对不对；运行编译器（std/proc）。
-/
import Lark.Lsp
import Lark.LspDoc

namespace Lark
namespace LspDiag

/-! ## 编译器的行列 ↔ 字节偏移（行、列从 0 数；cOff 换成从 1 数的） -/

/-- 第 l 行第 c 列的偏移。列超过行尾时停在 \n 上，行超过最后一行时是末尾 -/
def cGo : List Nat → Nat → Nat → Nat
  | [], _, _ => 0
  | _ :: _, 0, 0 => 0
  | x :: r, 0, c + 1 => if x = 10 then 0 else cGo r 0 c + 1
  | x :: r, l + 1, c => if x = 10 then cGo r l c + 1 else cGo r (l + 1) c + 1

/-- 偏移 o 在编译器里的行列 -/
def cPos : List Nat → Nat → Nat × Nat
  | [], _ => (0, 0)
  | _ :: _, 0 => (0, 0)
  | x :: r, o + 1 =>
    if x = 10 then ((cPos r o).1 + 1, (cPos r o).2)
    else if (cPos r o).1 = 0 then (0, (cPos r o).2 + 1) else cPos r o

/-- 编译器报的（从 1 数的）行列 -/
def cOff (d : List Nat) (l c : Nat) : Nat := cGo d (l - 1) (c - 1)

theorem cGo_le : ∀ (d : List Nat) (l c : Nat), cGo d l c ≤ d.length
  | [], _, _ => by simp [cGo]
  | _ :: _, 0, 0 => by simp [cGo]
  | x :: r, 0, c + 1 => by
    have := cGo_le r 0 c
    by_cases hx : x = 10 <;> simp [cGo, hx] <;> omega
  | x :: r, l + 1, c => by
    have h1 := cGo_le r l c
    have h2 := cGo_le r (l + 1) c
    by_cases hx : x = 10 <;> simp [cGo, hx] <;> omega

theorem cOff_le (d : List Nat) (l c : Nat) : cOff d l c ≤ d.length := cGo_le d (l - 1) (c - 1)

theorem c_round : ∀ (d : List Nat) (o : Nat), o ≤ d.length → cGo d (cPos d o).1 (cPos d o).2 = o
  | [], o, h => by
    have h0 : o = 0 := by simp at h; omega
    subst h0
    simp [cGo]
  | _ :: _, 0, _ => by simp [cPos, cGo]
  | x :: r, o + 1, h => by
    have ih := c_round r o (by simp at h; omega)
    by_cases hx : x = 10
    · subst hx
      simp only [cPos, ↓reduceIte, cGo, ih]
    · by_cases hp : (cPos r o).1 = 0
      · simp only [cPos, hx, hp, ↓reduceIte, cGo]
        rw [hp] at ih
        omega
      · obtain ⟨k, hk⟩ : ∃ k, (cPos r o).1 = k + 1 := ⟨(cPos r o).1 - 1, by omega⟩
        simp only [cPos, hx, hp, ↓reduceIte]
        rw [hk]
        simp only [cGo, hx, ↓reduceIte]
        rw [hk] at ih
        omega

/-! ## 诊断的位置：编译器的行列 → 字节偏移 → LSP 的位置 -/

def dpos (u : List Nat → Nat) (d : List Nat) (l c : Nat) : Nat × Nat := Lsp.posOf u (Lsp.doc d) (cOff d l c)

/-- 编译器指着字符的开头时，LSP 的位置换回来就是同一个字节 -/
theorem dpos_exact (u : List Nat → Nat) (hu : ∀ e : List Nat, e ≠ [] → 0 < u e) (d : List Nat) (l c k : Nat)
    (hk : cOff d l c = Lsp.blen ((Lsp.doc d).take k)) :
    Lsp.offOf u (Lsp.doc d) (dpos u d l c) = cOff d l c := by
  unfold dpos
  rw [hk]
  exact Lsp.pos_off u hu (Lsp.doc d) (Lsp.doc_ne d) k

/-- 从头到尾：编译器给字符开头 o 报的行列（从 1 数），在编辑器里标在 o 上 -/
theorem diag_round (u : List Nat → Nat) (hu : ∀ e : List Nat, e ≠ [] → 0 < u e) (d : List Nat) (k o : Nat)
    (ho : o = Lsp.blen ((Lsp.doc d).take k)) :
    Lsp.offOf u (Lsp.doc d) (dpos u d ((cPos d o).1 + 1) ((cPos d o).2 + 1)) = o := by
  have hle : o ≤ d.length := by
    have := Lsp.blen_take_le (Lsp.doc d) k
    rw [Lsp.blen_doc] at this
    omega
  have hc : cOff d ((cPos d o).1 + 1) ((cPos d o).2 + 1) = o := by
    unfold cOff
    simp only [Nat.add_sub_cancel]
    exact c_round d o hle
  rw [dpos_exact u hu d _ _ k (by rw [hc]; exact ho), hc]

/-! ## 编译器的一行错误：文件:行:列: 信息 -/

/-- 到第一个冒号（58）为止 -/
def spl : List Nat → Option (List Nat × List Nat)
  | [] => none
  | a :: r => if a = 58 then some ([], r) else (spl r).map (fun p => (a :: p.1, p.2))

theorem spl_app (l r : List Nat) (h : 58 ∉ l) : spl (l ++ 58 :: r) = some (l, r) := by
  induction l with
  | nil => simp [spl]
  | cons a l ih =>
    have ha : a ≠ 58 := by intro e; exact h (by simp [e])
    have hl : 58 ∉ l := by intro e; exact h (by simp [e])
    simp [spl, ha, ih hl]

theorem no_colon (n : Nat) : 58 ∉ Lsp.asc (Lsp.digs n) := by
  intro h
  simp only [Lsp.asc, List.mem_map] at h
  obtain ⟨d, hd, he⟩ := h
  have := Lsp.digs_lt n d hd
  omega

def fmtLine (name : List Nat) (l c : Nat) (rest : List Nat) : List Nat :=
  name ++ 58 :: (Lsp.asc (Lsp.digs l) ++ 58 :: (Lsp.asc (Lsp.digs c) ++ 58 :: 32 :: rest))

/-- 只认文件名是 name 的行（别的文件里的错误、指着列的 ^ 那两行都是 none） -/
def parseLine (name s : List Nat) : Option (Nat × Nat × List Nat) :=
  if (name ++ [58]).isPrefixOf s = true then
    match spl (s.drop (name.length + 1)) with
    | some (a, t) =>
      match spl t with
      | some (b, t2) =>
        match Lsp.num a, Lsp.num b, t2 with
        | some l, some c, x :: rest => if x = 32 then some (l, c, rest) else none
        | _, _, _ => none
      | none => none
    | none => none
  else none

theorem parse_fmt (name rest : List Nat) (l c : Nat) : parseLine name (fmtLine name l c rest) = some (l, c, rest) := by
  have he : fmtLine name l c rest =
      (name ++ [58]) ++ (Lsp.asc (Lsp.digs l) ++ 58 :: (Lsp.asc (Lsp.digs c) ++ 58 :: 32 :: rest)) := by
    simp [fmtLine]
  have h1 : (name ++ [58]).isPrefixOf (fmtLine name l c rest) = true := by
    rw [he]
    exact Lsp.isPrefix_app _ _
  have h2 : (fmtLine name l c rest).drop (name.length + 1) =
      Lsp.asc (Lsp.digs l) ++ 58 :: (Lsp.asc (Lsp.digs c) ++ 58 :: 32 :: rest) := by
    have hl : name.length + 1 = (name ++ [58]).length := by simp
    rw [he, hl]
    exact Lsp.dropApp _ _
  unfold parseLine
  rw [Lsp.iteT h1, h2, spl_app _ _ (no_colon l)]
  simp only [spl_app _ _ (no_colon c), Lsp.num_asc, ↓reduceIte]

/-! ## 什么时候发诊断 -/

/-- 一条通知以后要发的诊断：(uri, 版本)；版本是 none 时发空的诊断（清掉） -/
def pubs (s : LspDoc.Store) : LspDoc.Ev → List (String × Option Nat)
  | .opn uri v _ => [(uri, some v)]
  | .chg uri v _ =>
    match LspDoc.get s uri with
    | some (v0, _) => if v0 < v then [(uri, some v)] else []
    | none => []
  | .cls uri => [(uri, none)]

theorem pubs_latest (un : List Nat → Nat) (s : LspDoc.Store) (e : LspDoc.Ev) :
    ∀ p ∈ pubs s e, p.1 = e.uri ∧ p.2 = (LspDoc.get (LspDoc.step un s e) e.uri).map Prod.fst := by
  cases e with
  | opn uri v t =>
    intro p hp
    simp [pubs] at hp
    subst hp
    simp [LspDoc.Ev.uri, LspDoc.open_get]
  | cls uri =>
    intro p hp
    simp [pubs] at hp
    subst hp
    simp [LspDoc.Ev.uri, LspDoc.close_get]
  | chg uri v cs =>
    intro p hp
    cases hg : LspDoc.get s uri with
    | none => simp [pubs, hg] at hp
    | some q =>
      obtain ⟨v0, d⟩ := q
      by_cases hv : v0 < v
      · simp [pubs, hg, hv] at hp
        subst hp
        simp [LspDoc.Ev.uri, LspDoc.change_get un s uri v v0 d cs hg hv]
      · simp [pubs, hg, hv] at hp

theorem pubs_quiet (un : List Nat → Nat) (s : LspDoc.Store) (e : LspDoc.Ev) (h : pubs s e = []) :
    LspDoc.step un s e = s := by
  cases e with
  | opn uri v t => simp [pubs] at h
  | cls uri => simp [pubs] at h
  | chg uri v cs =>
    cases hg : LspDoc.get s uri with
    | none => exact LspDoc.change_unknown un s uri v cs hg
    | some q =>
      obtain ⟨v0, d⟩ := q
      by_cases hv : v0 < v
      · simp [pubs, hg, hv] at h
      · exact LspDoc.change_stale un s uri v v0 d cs hg hv

theorem pubs_len (s : LspDoc.Store) (e : LspDoc.Ev) : (pubs s e).length ≤ 1 := by
  cases e with
  | opn uri v t => simp [pubs]
  | cls uri => simp [pubs]
  | chg uri v cs =>
    cases hg : LspDoc.get s uri with
    | none => simp [pubs, hg]
    | some q =>
      obtain ⟨v0, d⟩ := q
      by_cases hv : v0 < v <;> simp [pubs, hg, hv]

def runPubs (un : List Nat → Nat) : LspDoc.Store → List LspDoc.Ev → List (String × Option Nat)
  | _, [] => []
  | s, e :: es => pubs s e ++ runPubs un (LspDoc.step un s e) es

/-! ## 例子 -/

-- a😀b\nc：编译器的第 1 行第 6 列是 b（字节 5），UTF-16 里是第 0 行第 3 列
def ex : List Nat := [97, 0xF0, 0x9F, 0x98, 0x80, 98, 10, 99]
#guard cOff ex 1 6 == 5
#guard dpos Lsp.u16 ex 1 6 == (0, 3)
#guard dpos Lsp.u8 ex 1 6 == (0, 5)
#guard dpos Lsp.u16 ex 2 1 == (1, 0)
#guard dpos Lsp.u16 ex 1 99 == (0, 4)    -- 列超过行尾：停在 \n 上
#guard dpos Lsp.u16 ex 9 1 == (1, 1)     -- 行超过最后一行：文档末尾
#guard cPos ex 7 == (1, 0)
-- 单独的 \r：编译器不当它换行（第 1 行第 3 列是 b），LSP 当它换行
#guard dpos Lsp.u16 (Lsp.bs "a\rb") 1 3 == (1, 0)
#guard dpos Lsp.u16 (Lsp.bs "a\r\nb") 2 1 == (1, 0)
#guard parseLine (Lsp.bs "f.lark") (Lsp.bs "f.lark:12:5: E: x") == some (12, 5, Lsp.bs "E: x")
#guard parseLine (Lsp.bs "f.lark") (Lsp.bs "g.lark:12:5: E: x") == none
#guard parseLine (Lsp.bs "f.lark") (Lsp.bs " 12 | let x") == none
#guard parseLine (Lsp.bs "f.lark") (Lsp.bs "f.lark:x:5: E") == none
#guard runPubs Lsp.u16 [] LspDoc.evs ==
  [("file:///a", some 1), ("file:///a", some 2), ("file:///a", some 3), ("file:///b", some 1), ("file:///b", none)]

end LspDiag
end Lark
