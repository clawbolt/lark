/-
apps/lterm 的证明 · 阶段 6：滚动缓冲（scrollback）、改大小（resize）
先证明，再写 apps/lterm 里的这一部分。

滚动缓冲：整个屏幕往上滚（滚动区域是整个屏幕、在主屏幕上）时，滚出屏幕顶上的行不丢，按顺序放进滚动缓冲；
缓冲最多存 cap 行，多了丢掉最旧的（keep）。
改大小：每一行补齐或截断成新的列数（rowFix，宽字符被切开时剩下的一半变成空格）；
行数变少时，如果光标会落到屏幕外面，就把顶上的几行（cut 行）挪进滚动缓冲，让光标那一行留在屏幕的最后一行；
光标限制在屏幕里，滚动区域变回整个屏幕。备用屏幕上时，存着的主屏幕一起改大小。

证明了：
- `up_keep`、`hist_up`：整个屏幕往上滚 n 行时，滚出去的 n 行接上滚动以后的屏幕，正好是滚动以前的屏幕接上 n 个空行：
  滚动缓冲 ++ 屏幕 这一整段历史，除了在最后添了空行，一行都没丢、顺序也没变；
- `keep_len`、`keep_suffix`、`keep_all`：缓冲不超过 cap 行；留下的总是最新的那一段；没满时一行都不丢；
- `resize_ok`、`resizeT_ok`：改成任何大小（行数、列数大于 0）以后屏幕都是好的（VtScreen.Ok / VtMode.Ok）；
- `resize_cur`：光标所在的那一行还在光标所在的地方（只是补齐或截断了列）；
- `resize_lost`：挪进滚动缓冲的就是顶上的那 cut 行。
例子（#guard）里检查了：滚出去的行、缓冲满了丢最旧的、改小改大、行数变少时顶上的行挪走。
没做：改列数时把长行重新折行（reflow）；滚动区域不是整个屏幕时滚出去的行不存（和 xterm 一样）。
-/
import Lark.Lsp
import Lark.VtScreen
import Lark.VtMode

namespace Lark
namespace VtSb

open VtScreen

/-! ## 行的列表的几个性质 -/

theorem getAt_append : ∀ (A B : List (List Cell)) (i : Nat),
    getAt (A ++ B) i = if i < A.length then getAt A i else getAt B (i - A.length)
  | [], B, i => by simp
  | a :: A, B, 0 => by simp [getAt]
  | a :: A, B, n + 1 => by
    have e : getAt ((a :: A) ++ B) (n + 1) = getAt (A ++ B) n := rfl
    have e2 : getAt (a :: A) (n + 1) = getAt A n := rfl
    rw [e, getAt_append A B n]
    by_cases hn : n < A.length
    · have h2 : n + 1 < (a :: A).length := by simp only [List.length_cons]; omega
      rw [Lsp.iteT hn, Lsp.iteT h2, e2]
    · have h2 : ¬(n + 1 < (a :: A).length) := by simp only [List.length_cons]; omega
      have h3 : n + 1 - (a :: A).length = n - A.length := by simp only [List.length_cons]; omega
      rw [Lsp.iteF hn, Lsp.iteF h2, h3]

theorem getAt_rep : ∀ (n i : Nat) (x : List Cell), i < n → getAt (List.replicate n x) i = x
  | 0, _, _, h => absurd h (Nat.not_lt_zero _)
  | _ + 1, 0, _, _ => rfl
  | n + 1, i + 1, x, h => getAt_rep n i x (by omega)

theorem getAt_ext : ∀ (A B : List (List Cell)), A.length = B.length →
    (∀ i, i < A.length → getAt A i = getAt B i) → A = B
  | [], [], _, _ => rfl
  | [], _ :: _, h, _ => by simp at h
  | _ :: _, [], h, _ => by simp at h
  | a :: A, b :: B, hl, hg => by
    have h0 : a = b := hg 0 (by simp only [List.length_cons]; omega)
    have hl' : A.length = B.length := by simp only [List.length_cons] at hl; omega
    have hr : A = B := getAt_ext A B hl' (fun i hi => hg (i + 1) (by simp only [List.length_cons]; omega))
    rw [h0, hr]

/-! ## 滚出去的行不丢 -/

/-- 屏幕顶上的 n 行（往上滚 n 行时滚出去的） -/
def topRows (s : S) (n : Nat) : List (List Cell) := buildF (getAt s.rows) n 0

theorem up_keep {s : S} (h : Ok s) {n : Nat} (hn : n ≤ s.R) :
    topRows s n ++ (scrollUp s 0 (s.R - 1) n).rows = s.rows ++ List.replicate n (blankRow s.C) := by
  obtain ⟨hR, _, hl, _⟩ := h
  have e : (scrollUp s 0 (s.R - 1) n).rows = buildF (upRows s 0 (s.R - 1) n) s.R 0 := rfl
  unfold topRows
  rw [e]
  apply getAt_ext
  · rw [List.length_append, List.length_append, buildF_len, buildF_len, hl, List.length_replicate]
    omega
  · intro i hi
    rw [List.length_append, buildF_len, buildF_len] at hi
    rw [getAt_append, getAt_append, buildF_len, hl]
    by_cases h1 : i < n
    · have h2 : i < s.R := by omega
      rw [Lsp.iteT h1, Lsp.iteT h2, buildF_get n 0 i h1, Nat.zero_add]
    · rw [Lsp.iteF h1, buildF_get s.R 0 (i - n) (by omega), Nat.zero_add]
      unfold upRows
      have h3 : 0 ≤ i - n ∧ i - n ≤ s.R - 1 := by omega
      rw [Lsp.iteT h3]
      by_cases h4 : i < s.R
      · have h5 : i - n + n ≤ s.R - 1 := by omega
        rw [Lsp.iteT h5, Lsp.iteT h4, Nat.sub_add_cancel (by omega : n ≤ i)]
      · have h5 : ¬(i - n + n ≤ s.R - 1) := by omega
        rw [Lsp.iteF h5, Lsp.iteF h4, getAt_rep n (i - s.R) _ (by omega)]

/-- 滚动缓冲 ++ 屏幕：滚动以后只在最后多了 n 个空行 -/
theorem hist_up {s : S} (h : Ok s) {n : Nat} (hn : n ≤ s.R) (sb : List (List Cell)) :
    (sb ++ topRows s n) ++ (scrollUp s 0 (s.R - 1) n).rows = sb ++ (s.rows ++ List.replicate n (blankRow s.C)) := by
  rw [List.append_assoc, up_keep h hn]

/-! ## 缓冲最多存 cap 行 -/

def keep {α : Type} (cap : Nat) (l : List α) : List α := l.drop (l.length - cap)

theorem keep_len {α : Type} (cap : Nat) (l : List α) : (keep cap l).length ≤ cap := by
  unfold keep
  rw [List.length_drop]
  omega

theorem keep_suffix {α : Type} (cap : Nat) (l : List α) : ∃ p, p ++ keep cap l = l :=
  ⟨l.take (l.length - cap), List.take_append_drop _ _⟩

theorem keep_all {α : Type} {cap : Nat} {l : List α} (h : l.length ≤ cap) : keep cap l = l := by
  unfold keep
  rw [Nat.sub_eq_zero_of_le h, List.drop_zero]

/-! ## 改大小 -/

/-- 行数改成 R 时顶上要挪走几行：让光标那一行留在屏幕里 -/
def cut (s : S) (R : Nat) : Nat := s.y + 1 - R

/-- 改成 R 行 × C 列；第二个是挪进滚动缓冲的行 -/
def resize (s : S) (R C : Nat) : S × List (List Cell) :=
  let s2 : S :=
    { rows := buildF (fun i => rowFix C (getAt s.rows (i + cut s R))) R 0
      R := R
      C := C
      x := lim C s.x
      y := s.y - cut s R
      pend := false
      top := 0
      bot := R - 1 }
  (s2, topRows s (cut s R))

theorem resize_ok {s : S} {R C : Nat} (hR : 0 < R) (hC : 0 < C) : Ok (resize s R C).1 := by
  refine ⟨hR, hC, buildF_len R 0, ?_, lim_lt hC, ?_, Nat.zero_le _, by show R - 1 < R; omega⟩
  · intro r hm
    have hm' : r ∈ buildF (fun i => rowFix C (getAt s.rows (i + cut s R))) R 0 := hm
    obtain ⟨i, _, _, rfl⟩ := buildF_mem R 0 r hm'
    show RowOk C (rowFix C (getAt s.rows (i + cut s R)))
    exact rowFix_ok
  · show s.y - cut s R < R
    unfold cut
    omega

theorem resize_cur (s : S) {R : Nat} (C : Nat) (hR : 0 < R) :
    getAt (resize s R C).1.rows (resize s R C).1.y = rowFix C (getAt s.rows s.y) := by
  show getAt (buildF (fun i => rowFix C (getAt s.rows (i + cut s R))) R 0) (s.y - cut s R) = _
  rw [buildF_get R 0 (s.y - cut s R) (by unfold cut; omega)]
  have e : 0 + (s.y - cut s R) + cut s R = s.y := by unfold cut; omega
  show rowFix C (getAt s.rows (0 + (s.y - cut s R) + cut s R)) = _
  rw [e]

theorem resize_lost (s : S) (R C : Nat) :
    (resize s R C).2.length = cut s R ∧ ∀ i, i < cut s R → getAt (resize s R C).2 i = getAt s.rows i := by
  refine ⟨buildF_len (cut s R) 0, ?_⟩
  intro i hi
  show getAt (buildF (getAt s.rows) (cut s R) 0) i = _
  rw [buildF_get _ 0 i hi, Nat.zero_add]

/-- 终端改大小：现在的屏幕和存着的主屏幕都改 -/
def resizeT (t : VtMode.T) (R C : Nat) : VtMode.T :=
  { t with scr := (resize t.scr R C).1, other := t.other.map (fun m => (resize m R C).1) }

theorem resizeT_ok (t : VtMode.T) {R C : Nat} (hR : 0 < R) (hC : 0 < C) : VtMode.Ok (resizeT t R C) := by
  refine ⟨resize_ok (s := t.scr) hR hC, ?_⟩
  intro m hm
  cases ho : t.other with
  | none => simp [resizeT, ho] at hm
  | some a =>
    simp [resizeT, ho] at hm
    subst hm
    exact resize_ok hR hC

/-! ## 例子 -/

def rowsOf (l : List (List Cell)) : List (List Nat) := l.map (fun r => r.map cellCh)

-- 两行的屏幕写了两行：往上滚 1 行时滚出去的是 "a"
#guard (fun s => rowsOf (topRows s 1) == [bs "a "] && line s 1 == bs "b ")
  (run (init 2 2) (texts (bs "a") ++ [.cr, .lf] ++ texts (bs "b")))
#guard (fun s => rowsOf (topRows s 1 ++ (scrollUp s 0 (s.R - 1) 1).rows) == [bs "a ", bs "b ", bs "  "])
  (run (init 2 2) (texts (bs "a") ++ [.cr, .lf] ++ texts (bs "b")))
-- 缓冲满了丢最旧的
#guard keep 2 [1, 2, 3, 4] == [3, 4]
#guard keep 5 [1, 2, 3] == [1, 2, 3]
-- 改窄：截断；宽字符被切开，剩下的一半变成空格；改宽：补空格
#guard (fun s => line (resize s 1 2).1 0 == bs "ab" && (resize s 1 2).1.x == 1) (run (init 1 4) (texts (bs "abcd")))
#guard (fun s => line (resize s 1 2).1 0 == bs "a ") (run (init 1 4) (texts (bs "a") ++ [.print 20013 2]))
#guard (fun s => line (resize s 2 4).1 0 == bs "ab  " && line (resize s 2 4).1 1 == bs "    ") (run (init 1 2) (texts (bs "ab")))
-- 行数变少、光标在最后一行：顶上的行挪进滚动缓冲，光标那一行留在屏幕上
#guard (fun s => rowsOf (resize s 1 2).2 == [bs "a "] && line (resize s 1 2).1 0 == bs "b " && (resize s 1 2).1.y == 0)
  (run (init 2 2) (texts (bs "a") ++ [.cr, .lf] ++ texts (bs "b")))
-- 光标在第一行：不挪，只截掉下面的行
#guard (fun s => (resize s 1 2).2 == [] && line (resize s 1 2).1 0 == bs "a ")
  (run (init 2 2) (texts (bs "a") ++ [.cr, .lf] ++ texts (bs "b") ++ [.cup 1 1]))

end VtSb
end Lark
