/-
apps/lterm 的证明 · 阶段 8：翻看滚动缓冲
先证明，再写 apps/lterm/vt/view.lark。

lterm run 里按 Ctrl-] 再按 [ 进入翻看：屏幕上显示的不再是现在的屏幕，而是 滚动缓冲 ++ 屏幕 这一整段历史里的一个窗口。
窗口和屏幕一样高（R 行）；off 是往上翻了几行（0 就是现在的屏幕），最多翻到滚动缓冲的第一行（off ≤ 缓冲的行数）。
上翻 n 行（up）、下翻 n 行（down）、到最上面（top）、回到最下面（0）。

证明了：
- `view_len`：不管 off 是多少，窗口总是正好 R 行；
- `view_zero`：off = 0 时窗口就是现在的屏幕（翻看没动时和平常一样）；
- `view_sub`：窗口是历史里连续的一段（没有跳行，也没有编出来的行）；
- `view_top`：翻到最上面时窗口从缓冲的第一行开始；
- `up_le`：上翻不会超过缓冲的第一行；`up_down`：没碰到顶时上翻 n 行再下翻 n 行回到原来的地方；`down_zero`：下翻够了回到现在的屏幕。
格子、行是任何东西（Lark 里一行是格子和样式）。
例子（#guard）里检查了：不翻、翻一行、翻过头、翻到最上面、缓冲是空的。
没做：翻看时有新的输出，窗口跟着内容走（现在 off 不变，看到的内容会往上移）；在历史里搜索。
-/
import Lark.Lsp

namespace Lark
namespace VtView

variable {α : Type}

/-- 限制在 [0, 缓冲的行数] 里 -/
def clamp (sb : List α) (o : Nat) : Nat := min o sb.length

/-- 往上翻了 o 行时看到的窗口 -/
def view (sb scr : List α) (o : Nat) : List α :=
  ((sb ++ scr).drop (sb.length - clamp sb o)).take scr.length

def up (sb : List α) (n o : Nat) : Nat := clamp sb (o + n)

def down (n o : Nat) : Nat := o - n

theorem view_len (sb scr : List α) (o : Nat) : (view sb scr o).length = scr.length := by
  unfold view clamp
  rw [List.length_take, List.length_drop, List.length_append]
  omega

theorem view_zero (sb scr : List α) : view sb scr 0 = scr := by
  unfold view clamp
  simp

theorem view_sub (sb scr : List α) (o : Nat) : ∃ p q, p ++ view sb scr o ++ q = sb ++ scr := by
  refine ⟨(sb ++ scr).take (sb.length - clamp sb o), ((sb ++ scr).drop (sb.length - clamp sb o)).drop scr.length, ?_⟩
  unfold view
  rw [List.append_assoc, List.take_append_drop, List.take_append_drop]

theorem view_top (sb scr : List α) : view sb scr sb.length = (sb ++ scr).take scr.length := by
  unfold view clamp
  simp

theorem up_le (sb : List α) (n o : Nat) : up sb n o ≤ sb.length := by
  unfold up clamp
  exact Nat.min_le_right _ _

theorem up_down (sb : List α) {n o : Nat} (h : o + n ≤ sb.length) : down n (up sb n o) = o := by
  unfold down up clamp
  rw [Nat.min_eq_left h]
  omega

theorem down_zero {n o : Nat} (h : o ≤ n) : down n o = 0 := by
  unfold down
  omega

/-! ## 例子 -/

-- 缓冲 [1, 2, 3]，屏幕 [4, 5]
#guard view [1, 2, 3] [4, 5] 0 == [4, 5]
#guard view [1, 2, 3] [4, 5] 1 == [3, 4]
#guard view [1, 2, 3] [4, 5] 3 == [1, 2]
-- 翻过头：停在最上面
#guard view [1, 2, 3] [4, 5] 9 == [1, 2]
#guard up [1, 2, 3] 5 1 == 3
#guard down 2 (up [1, 2, 3] 2 1) == 1
-- 缓冲是空的：怎么翻都是现在的屏幕
#guard view ([] : List Nat) [4, 5] 7 == [4, 5]
-- 缓冲比屏幕短：翻到最上面时下面接着屏幕的开头
#guard view [1] [4, 5, 6] 1 == [1, 4, 5]

end VtView
end Lark
