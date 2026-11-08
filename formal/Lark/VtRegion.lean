/-
apps/lterm 的证明 · 阶段 11：滚动区域从屏幕顶上开始时，滚出去的行也进滚动缓冲
先证明，再写 apps/lterm 里的这一部分。

阶段 6（VtSb.lean）只在滚动区域是整个屏幕时才把滚出去的行存起来。
codex 这类不用备用屏幕的全屏程序：下面留一块自己画的界面，上面设成滚动区域 [0, b]（CSI 1 ; b+1 r），
在区域的最后一行换行，把新的输出一行一行推上去。滚出区域顶上的行就是屏幕顶上的行，
不存的话这些内容直接没了（翻滚动缓冲也看不到）。xterm、VTE、Ghostty 也是区域从第一行开始就存。

证明了：
- `region_keep`：区域 [0, b] 往上滚 n 行（n ≤ b + 1）时，滚出去的 n 行（屏幕顶上的 n 行）接上滚动以后区域里的 b + 1 行，
  正好是滚动以前区域里的 b + 1 行接上 n 个空行：一行都没丢、顺序也没变（b = R - 1 时就是 VtSb.up_keep）；
- `region_hist`：滚动缓冲 ++ 区域 这一整段也一样；
- `region_below`：区域下面的行（程序自己画的界面）不动（就是 VtScreen.up_outside）；
- `up_clamp`：往上滚超过 b + 1 行和滚 b + 1 行一样（整个区域都空了），所以最多存 b + 1 行。
例子（#guard）里检查了：三行的屏幕、区域是前两行时，换行滚出去的是第一行，第三行不动。
-/
import Lark.Lsp
import Lark.VtScreen
import Lark.VtSb

namespace Lark
namespace VtRegion

open VtScreen

theorem region_keep {s : S} {b n : Nat} (hb : b < s.R) (hn : n ≤ b + 1) :
    VtSb.topRows s n ++ VtSb.topRows (scrollUp s 0 b n) (b + 1)
      = VtSb.topRows s (b + 1) ++ List.replicate n (blankRow s.C) := by
  have e : (scrollUp s 0 b n).rows = buildF (upRows s 0 b n) s.R 0 := rfl
  unfold VtSb.topRows
  rw [e]
  apply VtSb.getAt_ext
  · simp only [List.length_append, buildF_len, List.length_replicate]
    omega
  · intro i hi
    simp only [List.length_append, buildF_len] at hi
    rw [VtSb.getAt_append, VtSb.getAt_append]
    simp only [buildF_len]
    by_cases h1 : i < n
    · have h2 : i < b + 1 := by omega
      rw [Lsp.iteT h1, Lsp.iteT h2, buildF_get n 0 i h1, buildF_get (b + 1) 0 i h2]
    · rw [Lsp.iteF h1, buildF_get (b + 1) 0 (i - n) (by omega), Nat.zero_add,
        buildF_get s.R 0 (i - n) (by omega), Nat.zero_add]
      unfold upRows
      have h3 : 0 ≤ i - n ∧ i - n ≤ b := by omega
      rw [Lsp.iteT h3]
      by_cases h4 : i < b + 1
      · have h5 : i - n + n ≤ b := by omega
        rw [Lsp.iteT h5, Lsp.iteT h4, buildF_get (b + 1) 0 i h4, Nat.zero_add,
          Nat.sub_add_cancel (by omega : n ≤ i)]
      · have h5 : ¬(i - n + n ≤ b) := by omega
        rw [Lsp.iteF h5, Lsp.iteF h4, VtSb.getAt_rep n (i - (b + 1)) _ (by omega)]

theorem region_hist {s : S} {b n : Nat} (hb : b < s.R) (hn : n ≤ b + 1) (sb : List (List Cell)) :
    (sb ++ VtSb.topRows s n) ++ VtSb.topRows (scrollUp s 0 b n) (b + 1)
      = sb ++ (VtSb.topRows s (b + 1) ++ List.replicate n (blankRow s.C)) := by
  rw [List.append_assoc, region_keep hb hn]

theorem region_below {s : S} {b n i : Nat} (hi : i < s.R) (hb : b < i) :
    getAt (scrollUp s 0 b n).rows i = getAt s.rows i :=
  up_outside hi (by omega)

theorem up_clamp {s : S} {b n : Nat} (hn : b + 1 ≤ n) :
    (scrollUp s 0 b n).rows = (scrollUp s 0 b (b + 1)).rows := by
  show buildF (upRows s 0 b n) s.R 0 = buildF (upRows s 0 b (b + 1)) s.R 0
  have e : upRows s 0 b n = upRows s 0 b (b + 1) := by
    funext i
    unfold upRows
    by_cases h : 0 ≤ i ∧ i ≤ b
    · rw [Lsp.iteT h, Lsp.iteT h, Lsp.iteF (by omega : ¬(i + n ≤ b)), Lsp.iteF (by omega : ¬(i + (b + 1) ≤ b))]
    · rw [Lsp.iteF h, Lsp.iteF h]
  rw [e]

/-! ## 例子 -/

-- 三行的屏幕，区域是前两行（CSI 1 ; 2 r）：写 a、b、c，再在区域的最后一行换行
def ex : S := run (init 3 2) (texts (bs "a") ++ [.cr, .lf] ++ texts (bs "b") ++ [.cr, .lf] ++ texts (bs "c") ++ [.stbm 1 2, .cup 2 1])

-- 滚出去的是 "a"；区域里接着是 "b"、空行；第三行（区域下面）还是 "c"
#guard VtSb.rowsOf (VtSb.topRows ex 1) == [bs "a "]
#guard VtSb.rowsOf (VtSb.topRows ex 1 ++ VtSb.topRows (scrollUp ex 0 1 1) 2) == [bs "a ", bs "b ", bs "  "]
#guard line (step ex .lf) 2 == bs "c "
#guard line (step ex .lf) 0 == bs "b "

end VtRegion
end Lark
