/-
apps/lterm 的证明 · 阶段 7：把屏幕画到真的终端上（只画变了的地方）
先证明，再写 apps/lterm/vt/draw.lark。

lterm run 在一个伪终端（pty）里跑 shell，shell 的输出喂给我们自己的终端仿真（阶段 1–6），
再把仿真出来的屏幕画到外面真的终端上。每次不重画整个屏幕，只画变了的地方：
上一次画出去的画面（帧）记着，新画面的每一行和旧的比，一样的行不画；不一样的行，
从第一个不一样的格子（pre：一样的前缀有多长）开始，把这一行剩下的部分画出去（rowCmd）。
真的终端执行这些命令（applyRow / applyF）以后，屏幕上就是新画面。

证明了：
- `pre_take`：一样的前缀确实一样；
- `applyRow_ok`、`draw_ok`：旧画面执行 diff 出来的命令，正好得到新画面（行数一样时）；
- `applyRow_le`：从前缀里更早的地方开始画也对（Lark 里遇到宽字符的右半要退回到左半再画，靠它）；
- `diff_same`：画面没变时一个格子也不画；
- `cost_le`：一行画出去的格子不比这一行多。
格子是任何能比较相等的东西（Lark 里是字符和样式）。
例子（#guard）里检查了：改一个格子、改一行的末尾、整行一样、整个画面一样。
没做：行数、列数变了时（改大小）整个重画，不用 diff；光标位置和样式的转义序列在 Lark 里写，模型里只有格子。
-/
import Lark.Lsp

namespace Lark
namespace VtDraw

variable {α : Type} [DecidableEq α]

/-- 两行一样的前缀有多长 -/
def pre : List α → List α → Nat
  | a :: r, b :: s => if a = b then pre r s + 1 else 0
  | _, _ => 0

theorem pre_take : ∀ (o n : List α), o.take (pre o n) = n.take (pre o n)
  | [], _ => by simp [pre]
  | _ :: _, [] => by simp [pre]
  | a :: r, b :: s => by
    by_cases h : a = b
    · subst h
      simp [pre, pre_take r s]
    · simp [pre, h]

omit [DecidableEq α] in
theorem take_le (l : List α) {a p : Nat} (h : a ≤ p) : (l.take p).take a = l.take a := by
  simp only [List.take_take]
  congr 1
  omega

/-- 一行要画什么：一样就不画；不一样就从第一个不一样的格子开始画剩下的 -/
def rowCmd (o n : List α) : Option (Nat × List α) :=
  if o = n then none else some (pre o n, n.drop (pre o n))

/-- 真的终端执行一行的命令：光标移到第 a 列，写 cs（后面原来的格子被盖掉） -/
def applyRow (o : List α) : Option (Nat × List α) → List α
  | none => o
  | some (a, cs) => o.take a ++ cs

theorem applyRow_ok (o n : List α) : applyRow o (rowCmd o n) = n := by
  unfold rowCmd
  by_cases h : o = n
  · rw [Lsp.iteT h]
    exact h
  · rw [Lsp.iteF h]
    show o.take (pre o n) ++ n.drop (pre o n) = n
    rw [pre_take]
    exact List.take_append_drop _ _

theorem applyRow_le (o n : List α) {a : Nat} (ha : a ≤ pre o n) : applyRow o (some (a, n.drop a)) = n := by
  show o.take a ++ n.drop a = n
  have e : o.take a = n.take a := by
    rw [← take_le o ha, pre_take, take_le n ha]
  rw [e]
  exact List.take_append_drop _ _

theorem cost_le (o n : List α) : ∀ a cs, rowCmd o n = some (a, cs) → cs.length ≤ n.length := by
  intro a cs h
  unfold rowCmd at h
  by_cases ho : o = n
  · rw [Lsp.iteT ho] at h
    cases h
  · rw [Lsp.iteF ho] at h
    cases h
    simp

/-! ## 整个画面 -/

def diff : List (List α) → List (List α) → List (Option (Nat × List α))
  | o :: os, n :: ns => rowCmd o n :: diff os ns
  | _, _ => []

def applyF : List (List α) → List (Option (Nat × List α)) → List (List α)
  | o :: os, c :: cs => applyRow o c :: applyF os cs
  | os, [] => os
  | [], _ :: _ => []

theorem draw_ok : ∀ (os ns : List (List α)), os.length = ns.length → applyF os (diff os ns) = ns
  | [], [], _ => rfl
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | o :: os, n :: ns, h => by
    simp only [diff, applyF]
    rw [applyRow_ok, draw_ok os ns (by simp at h; omega)]

theorem diff_same : ∀ (f : List (List α)), ∀ c ∈ diff f f, c = none
  | [] => by simp [diff]
  | r :: f => by
    intro c hc
    simp only [diff, List.mem_cons] at hc
    rcases hc with hc | hc
    · rw [hc]
      simp [rowCmd]
    · exact diff_same f c hc

/-! ## 例子 -/

#guard pre [1, 2, 3] [1, 2, 4] == 2
#guard diff [[1, 2, 3], [4, 5]] [[1, 9, 3], [4, 5]] == [some (1, [9, 3]), none]
#guard applyF [[1, 2, 3], [4, 5]] (diff [[1, 2, 3], [4, 5]] [[1, 9, 3], [4, 5]]) == [[1, 9, 3], [4, 5]]
#guard diff [[1, 2, 3]] [[1, 2, 7]] == [some (2, [7])]
#guard diff [[1, 2], [3]] [[1, 2], [3]] == [none, none]
-- 从更早的地方开始画也对
#guard applyRow [1, 2, 3] (some (0, [1, 9, 3])) == [1, 9, 3]

end VtDraw
end Lark
