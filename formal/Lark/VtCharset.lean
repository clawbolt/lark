/-
apps/lterm 的证明 · 阶段 10：画框线的字符集（DEC Special Graphics）
先证明，再写 apps/lterm/vt/charset.lark。

用 ncurses 画框的程序（dialog、mc、一些 TUI）不直接写 ─ │ ┌，而是先切换字符集，再写普通的字母：
- ESC ( 0：G0 换成画线字符集；ESC ( B：G0 换回 ASCII（ESC ) 0 / ESC ) B 是 G1）；
- SO（0x0E）：之后用 G1；SI（0x0F）：之后用 G0。
画线字符集里 0x5F–0x7E 这 32 个字母换成别的字符（q → ─、x → │、l → ┌ ……），别的字符不变。

证明了：
- `map_out`：0x5F–0x7E 以外的字符不变；`map_ascii`：现在用的是 ASCII 时什么都不变；
- `gfx_width`：换出来的字符都占一格（和原来的字母一样宽，屏幕上不会错位；用的是阶段 2 的 width）；
- `gfx_inj`：不同的字母换成不同的字符；
- `reset_ascii`：ESC ( B 再 SI 以后（或者 ESC c 复位以后），一定回到 ASCII；
- `designate_other`：设置 G0 不影响 G1，反过来也一样。
例子（#guard）里检查了：q x l k j m 换成框线，SO / SI 切换，画线字符集之外的字母不变。
没做：别的字符集（英国 ESC ( A 等）、单次切换（SS2 / SS3）、G2 / G3。
-/
import Lark.Lsp
import Lark.VtUtf8

namespace Lark
namespace VtCharset

/-- 画线字符集：从 0x5F 开始的 32 个字符 -/
def gfx : List Nat :=
  [0x00A0, 0x25C6, 0x2592, 0x2409, 0x240C, 0x240D, 0x240A, 0x00B0,
   0x00B1, 0x2424, 0x240B, 0x2518, 0x2510, 0x250C, 0x2514, 0x253C,
   0x23BA, 0x23BB, 0x2500, 0x23BC, 0x23BD, 0x251C, 0x2524, 0x2534,
   0x252C, 0x2502, 0x2264, 0x2265, 0x03C0, 0x2260, 0x00A3, 0x00B7]

structure Cs where
  g0 : Bool := false   -- true：画线字符集
  g1 : Bool := false
  shift : Bool := false -- true：用 G1（SO）
deriving DecidableEq, Repr

def init : Cs := {}

def active (s : Cs) : Bool := if s.shift then s.g1 else s.g0

/-- 一个字符经过现在的字符集 -/
def map (s : Cs) (c : Nat) : Nat :=
  if active s = true ∧ 0x5F ≤ c ∧ c ≤ 0x7E then gfx.getD (c - 0x5F) 0 else c

inductive Op
  | designate (g : Nat) (lines : Bool)  -- ESC ( F（g = 0）、ESC ) F（g = 1）
  | so
  | si
  | reset

def step (s : Cs) : Op → Cs
  | .designate 0 b => { s with g0 := b }
  | .designate _ b => { s with g1 := b }
  | .so => { s with shift := true }
  | .si => { s with shift := false }
  | .reset => init

theorem map_out (s : Cs) {c : Nat} (h : c < 0x5F ∨ 0x7E < c) : map s c = c := by
  unfold map
  have hn : ¬(active s = true ∧ 0x5F ≤ c ∧ c ≤ 0x7E) := by omega
  rw [Lsp.iteF hn]

theorem map_ascii (s : Cs) (c : Nat) (h : active s = false) : map s c = c := by
  unfold map
  have hn : ¬(active s = true ∧ 0x5F ≤ c ∧ c ≤ 0x7E) := by
    intro h2
    rw [h] at h2
    exact absurd h2.1 (by decide)
  rw [Lsp.iteF hn]

theorem gfx_len : gfx.length = 32 := rfl

theorem gfx_width : ∀ c ∈ gfx, VtUtf8.width c = 1 := by decide

/-- 32 个字符一个一个算：都在表里、都占一格、两两不同 -/
theorem gfx_get : ∀ i, i < 32 → gfx.getD i 0 ∈ gfx := by decide

theorem width_get : ∀ i, i < 32 → VtUtf8.width (gfx.getD i 0) = 1 := by decide

theorem map_width (s : Cs) (c : Nat) (h : 0x5F ≤ c ∧ c ≤ 0x7E) (ha : active s = true) :
    VtUtf8.width (map s c) = 1 := by
  unfold map
  rw [Lsp.iteT ⟨ha, h⟩]
  exact width_get (c - 0x5F) (by omega)

theorem gfx_inj : ∀ a, a < 32 → ∀ b, b < 32 → gfx.getD a 0 = gfx.getD b 0 → a = b := by decide

theorem reset_ascii (s : Cs) (c : Nat) :
    map (step (step s (.designate 0 false)) .si) c = c ∧ map (step s .reset) c = c := by
  constructor
  · exact map_ascii _ c rfl
  · exact map_ascii _ c rfl

theorem designate_other (s : Cs) (b : Bool) :
    (step s (.designate 0 b)).g1 = s.g1 ∧ (step s (.designate 1 b)).g0 = s.g0 := ⟨rfl, rfl⟩

/-! ## 例子 -/

def runOps (l : List Op) : Cs := l.foldl step init

def mapStr (s : Cs) (l : List Nat) : List Nat := l.map (map s)

-- ESC ( 0 以后 lqqk / x  x / mqqj 是一个框
#guard mapStr (runOps [.designate 0 true]) [0x6C, 0x71, 0x6B, 0x78, 0x6D, 0x6A] == [0x250C, 0x2500, 0x2510, 0x2502, 0x2514, 0x2518]
-- 大写字母、数字不变
#guard mapStr (runOps [.designate 0 true]) [0x41, 0x30, 0x5E] == [0x41, 0x30, 0x5E]
-- G1 是画线字符集：SO 以后才用，SI 回来
#guard mapStr (runOps [.designate 1 true]) [0x71] == [0x71]
#guard mapStr (runOps [.designate 1 true, .so]) [0x71] == [0x2500]
#guard mapStr (runOps [.designate 1 true, .so, .si]) [0x71] == [0x71]
-- ESC ( B 换回来；复位
#guard mapStr (runOps [.designate 0 true, .designate 0 false]) [0x71] == [0x71]
#guard mapStr (runOps [.designate 0 true, .reset]) [0x71] == [0x71]

end VtCharset
end Lark
