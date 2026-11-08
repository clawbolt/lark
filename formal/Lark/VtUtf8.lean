/-
apps/lterm 的证明 · 阶段 2：UTF-8 的流式解码和字符宽度
先证明，再写 apps/lterm/vt/utf8.lark 和 apps/lterm/vt/width.lark。

解析器（VtParse）给出的 print 是一个字节一个字节的；屏幕要的是字符。程序的输出是一段一段读到的，
一个多字节字符可能被切在两段之间，所以解码是流式的：字节一个一个喂进去，没凑齐的字符先存着（pend）。
坏的字节照标准库（std/utf8.lark，Utf8.lean）的规矩：不合法的地方每次一个字节，码点 U+FFFD。

一步（settle）：把存着的字节加上新来的字节，
- 正好是一个完整的合法字符：交出去；
- 还可能凑成合法字符（是某个合法字符的真前缀，prefixOk）：接着存；
- 都不是：第一个字节交出去（U+FFFD），剩下的再走一遍。

证明了：
- `settle_join`、`feed_join`：交出去的字节拼起来、再接上存着的，正好是喂进去的全部字节：一个字节也不丢、不重复；
- `settle_pend`、`feed_pend`：存着的要么是空的，要么是某个合法字符的真前缀，所以最多 3 个字节（`pend_short`）；
- `settle_ne`：交出去的每一段都不是空的，最多 4 个字节；
- 每一段的码点是 Utf8.codeAt，都合法（Utf8.codeAt_valid），交给屏幕不会出错；
- `width_le`：宽度只有 0、1、2；`width_ascii`：可显示的 ASCII 宽度都是 1；
  两张表按区间从小到大排好、互不重叠（#guard）。
例子（#guard）里检查了：和 Utf8.codePoints（标准库）的结果一样，包括坏字节、截断、过长编码、代理区；
一个字符切在两段之间、切在哪里都一样。
没证：流式解码和 Utf8.codePoints 对所有输入都一样（只在例子和 Lark 的随机测试里对照）；
宽度表只收了常用的区间（组合附加符号、零宽字符、变体选择符；中日韩、全角、谚文、常见的 emoji），
不是完整的 Unicode East Asian Width 表。
-/
import Lark.Utf8
import Lark.Lsp

namespace Lark
namespace VtUtf8

open Utf8

/-! ## 流式解码 -/

def cont (b : Nat) : Bool := 0x80 ≤ b && b ≤ 0xBF

/-- 多字节字符的第二个字节：E0、ED、F0、F4 的范围更窄（和 Utf8.validLen 一样） -/
def second (b0 b1 : Nat) : Bool :=
  cont b1 && (b0 != 0xE0 || 0xA0 ≤ b1) && (b0 != 0xED || b1 ≤ 0x9F) &&
    (b0 != 0xF0 || 0x90 ≤ b1) && (b0 != 0xF4 || b1 ≤ 0x8F)

/-- 是某个合法字符的真前缀：再来几个字节还可能凑成合法字符 -/
def prefixOk : List Nat → Bool
  | [b0] => 0xC2 ≤ b0 && b0 ≤ 0xF4
  | [b0, b1] => 0xE0 ≤ b0 && b0 ≤ 0xF4 && second b0 b1
  | [b0, b1, b2] => 0xF0 ≤ b0 && b0 ≤ 0xF4 && second b0 b1 && cont b2
  | _ => false

/-- (交出去的字符，每个是它的字节；接着存的字节) -/
def settle : List Nat → List (List Nat) × List Nat
  | [] => ([], [])
  | a :: t =>
    if validLen (a :: t) = (a :: t).length then ([a :: t], [])
    else if prefixOk (a :: t) then ([], a :: t)
    else ([a] :: (settle t).1, (settle t).2)

/-- 喂一串字节：从存着的 p 开始 -/
def feed : List Nat → List Nat → List (List Nat) × List Nat
  | p, [] => ([], p)
  | p, b :: r =>
    let x := settle (p ++ [b])
    (x.1 ++ (feed x.2 r).1, (feed x.2 r).2)

/-- 不会再有字节了（或者被转义序列打断）：存着的每个字节各算一个 U+FFFD -/
def flush (p : List Nat) : List (List Nat) := p.map (fun b => [b])

/-- 一次喂完再 flush，交出去的码点 -/
def decode (l : List Nat) : List Nat :=
  let x := feed [] l
  (x.1 ++ flush x.2).map codeAt

theorem joinAll_append : ∀ (a b : List (List Nat)), joinAll (a ++ b) = joinAll a ++ joinAll b
  | [], b => by simp [joinAll]
  | c :: cs, b => by
    simp only [List.cons_append, joinAll]
    rw [joinAll_append cs b, List.append_assoc]

theorem settle_join : ∀ (s : List Nat), joinAll (settle s).1 ++ (settle s).2 = s
  | [] => by simp [settle, joinAll]
  | a :: t => by
    simp only [settle]
    by_cases h1 : validLen (a :: t) = (a :: t).length
    · rw [Lsp.iteT h1]
      simp [joinAll]
    · rw [Lsp.iteF h1]
      by_cases h2 : prefixOk (a :: t) = true
      · rw [Lsp.iteT h2]
        simp [joinAll]
      · rw [Lsp.iteF h2]
        have ih := settle_join t
        simp only [joinAll]
        rw [List.append_assoc, ih]
        rfl

theorem feed_join : ∀ (l p : List Nat), joinAll (feed p l).1 ++ (feed p l).2 = p ++ l
  | [], p => by simp [feed, joinAll]
  | b :: r, p => by
    have h1 := settle_join (p ++ [b])
    have h2 := feed_join r (settle (p ++ [b])).2
    simp only [feed]
    rw [joinAll_append, List.append_assoc, h2, ← List.append_assoc, h1]
    simp

theorem settle_pend : ∀ (s : List Nat), (settle s).2 = [] ∨ prefixOk (settle s).2 = true
  | [] => by simp [settle]
  | a :: t => by
    simp only [settle]
    by_cases h1 : validLen (a :: t) = (a :: t).length
    · rw [Lsp.iteT h1]
      simp
    · rw [Lsp.iteF h1]
      by_cases h2 : prefixOk (a :: t) = true
      · rw [Lsp.iteT h2]
        simp [h2]
      · rw [Lsp.iteF h2]
        exact settle_pend t

theorem feed_pend : ∀ (l p : List Nat), (p = [] ∨ prefixOk p = true) →
    (feed p l).2 = [] ∨ prefixOk (feed p l).2 = true
  | [], p, h => by simpa [feed] using h
  | b :: r, p, _ => by
    simp only [feed]
    exact feed_pend r _ (settle_pend (p ++ [b]))

theorem pend_short (p : List Nat) (h : prefixOk p = true) : p.length ≤ 3 := by
  rcases p with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, r⟩⟩⟩⟩
  · have e : prefixOk [] = false := rfl
    rw [e] at h
    exact absurd h (by decide)
  · simp
  · simp
  · simp
  · have e : prefixOk (a :: b :: c :: d :: r) = false := rfl
    rw [e] at h
    exact absurd h (by decide)

theorem settle_ne : ∀ (s : List Nat), s.length ≤ 4 → ∀ c ∈ (settle s).1, c ≠ [] ∧ c.length ≤ 4
  | [], _ => by simp [settle]
  | a :: t, hl => by
    intro c hc
    simp only [settle] at hc
    by_cases h1 : validLen (a :: t) = (a :: t).length
    · rw [Lsp.iteT h1] at hc
      simp at hc
      rw [hc]
      exact ⟨by simp, hl⟩
    · rw [Lsp.iteF h1] at hc
      by_cases h2 : prefixOk (a :: t) = true
      · rw [Lsp.iteT h2] at hc
        simp at hc
      · rw [Lsp.iteF h2] at hc
        have hc' : c ∈ [a] :: (settle t).1 := hc
        rcases List.mem_cons.mp hc' with e | e
        · rw [e]
          exact ⟨by simp, by simp⟩
        · have : t.length ≤ 4 := by simp at hl; omega
          exact settle_ne t this c e

/-- 喂进去的时候，存着的最多 3 个字节，加上新来的最多 4 个，所以交出去的每一段都不空、最多 4 个字节 -/
theorem feed_ne : ∀ (l p : List Nat), (p = [] ∨ prefixOk p = true) → ∀ c ∈ (feed p l).1, c ≠ [] ∧ c.length ≤ 4
  | [], _, _ => by simp [feed]
  | b :: r, p, hp => by
    intro c hc
    simp only [feed] at hc
    rcases List.mem_append.mp hc with e | e
    · have hl : (p ++ [b]).length ≤ 4 := by
        rcases hp with h | h
        · simp [h]
        · have := pend_short p h
          simp only [List.length_append, List.length_singleton]
          omega
      exact settle_ne (p ++ [b]) hl c e
    · exact feed_ne r _ (settle_pend (p ++ [b])) c e

/-- 交给屏幕的码点都合法 -/
theorem decode_valid (l : List Nat) : ∀ cp ∈ decode l, ValidCP cp := by
  intro cp h
  simp only [decode, List.mem_map] at h
  obtain ⟨c, _, rfl⟩ := h
  exact codeAt_valid c

/-! ## 字符宽度 -/

/-- 在不在这些区间里（闭区间） -/
def inR : List (Nat × Nat) → Nat → Bool
  | [], _ => false
  | (lo, hi) :: rs, c => (lo ≤ c && c ≤ hi) || inR rs c

/-- 宽度 0：组合附加符号、零宽字符、变体选择符（跟在前一个字符后面，不占格子） -/
def zeroTab : List (Nat × Nat) :=
  [(0x0300, 0x036F), (0x0483, 0x0489), (0x0591, 0x05BD), (0x0610, 0x061A), (0x064B, 0x065F),
   (0x0E31, 0x0E31), (0x0E34, 0x0E3A), (0x0E47, 0x0E4E), (0x1AB0, 0x1AFF), (0x1DC0, 0x1DFF),
   (0x200B, 0x200F), (0x202A, 0x202E), (0x2060, 0x2064), (0x20D0, 0x20FF), (0xFE00, 0xFE0F),
   (0xFE20, 0xFE2F), (0xFEFF, 0xFEFF), (0xE0100, 0xE01EF)]

/-- 宽度 2：中日韩、谚文、全角、常见的 emoji -/
def wideTab : List (Nat × Nat) :=
  [(0x1100, 0x115F), (0x231A, 0x231B), (0x2329, 0x232A), (0x23E9, 0x23EC), (0x23F0, 0x23F0),
   (0x23F3, 0x23F3), (0x25FD, 0x25FE), (0x2614, 0x2615), (0x2648, 0x2653), (0x267F, 0x267F),
   (0x2693, 0x2693), (0x26A1, 0x26A1), (0x26AA, 0x26AB), (0x26BD, 0x26BE), (0x26C4, 0x26C5),
   (0x26CE, 0x26CE), (0x26D4, 0x26D4), (0x26EA, 0x26EA), (0x26F2, 0x26F3), (0x26F5, 0x26F5),
   (0x26FA, 0x26FA), (0x26FD, 0x26FD), (0x2705, 0x2705), (0x270A, 0x270B), (0x2728, 0x2728),
   (0x274C, 0x274C), (0x274E, 0x274E), (0x2753, 0x2755), (0x2757, 0x2757), (0x2795, 0x2797),
   (0x27B0, 0x27B0), (0x27BF, 0x27BF), (0x2B1B, 0x2B1C), (0x2B50, 0x2B50), (0x2B55, 0x2B55),
   (0x2E80, 0x303E), (0x3041, 0x33FF), (0x3400, 0x4DBF), (0x4E00, 0x9FFF), (0xA000, 0xA4CF),
   (0xA960, 0xA97F), (0xAC00, 0xD7A3), (0xF900, 0xFAFF), (0xFE10, 0xFE19), (0xFE30, 0xFE6F),
   (0xFF00, 0xFF60), (0xFFE0, 0xFFE6), (0x1F004, 0x1F004), (0x1F0CF, 0x1F0CF), (0x1F18E, 0x1F18E),
   (0x1F191, 0x1F19A), (0x1F200, 0x1F202), (0x1F210, 0x1F23B), (0x1F240, 0x1F248), (0x1F250, 0x1F251),
   (0x1F300, 0x1F64F), (0x1F680, 0x1F6FF), (0x1F7E0, 0x1F7EB), (0x1F900, 0x1F9FF), (0x1FA70, 0x1FAFF),
   (0x20000, 0x2FFFD), (0x30000, 0x3FFFD)]

def width (c : Nat) : Nat :=
  if inR zeroTab c then 0 else if inR wideTab c then 2 else 1

theorem width_le (c : Nat) : width c ≤ 2 := by
  unfold width
  split
  · omega
  · split <;> omega

theorem inR_below : ∀ (rs : List (Nat × Nat)) (c : Nat), (∀ r ∈ rs, c < r.1) → inR rs c = false
  | [], _, _ => by simp [inR]
  | (lo, hi) :: rs, c, h => by
    have h1 : c < lo := h (lo, hi) (by simp)
    have h2 := inR_below rs c (fun r hr => h r (by simp [hr]))
    simp only [inR, h2, Bool.or_false]
    have : ¬ lo ≤ c := by omega
    simp [this]

theorem zero_above : ∀ r ∈ zeroTab, 0x7F ≤ r.1 := by decide
theorem wide_above : ∀ r ∈ wideTab, 0x7F ≤ r.1 := by decide

theorem width_ascii (c : Nat) (h : c ≤ 0x7E) : width c = 1 := by
  have h1 := inR_below zeroTab c (fun r hr => by have := zero_above r hr; omega)
  have h2 := inR_below wideTab c (fun r hr => by have := wide_above r hr; omega)
  simp [width, h1, h2]

/-- 区间都是 lo ≤ hi，按从小到大排好、互不重叠 -/
def sortedR : List (Nat × Nat) → Bool
  | [] => true
  | [(lo, hi)] => lo ≤ hi
  | (lo, hi) :: (lo2, hi2) :: rs => lo ≤ hi && hi < lo2 && sortedR ((lo2, hi2) :: rs)

/-! ## 例子 -/

#guard sortedR zeroTab
#guard sortedR wideTab
-- 和标准库的 code_points（Utf8.codePoints）一样：中文、坏字节、过长编码、代理区、超过 U+10FFFF、截断
#guard decode [0xE4, 0xB8, 0xAD, 0x61] == codePoints [0xE4, 0xB8, 0xAD, 0x61]
#guard decode [0xC3, 0x41] == codePoints [0xC3, 0x41]
#guard decode [0xC0, 0x80] == codePoints [0xC0, 0x80]
#guard decode [0xED, 0xA0, 0x80] == codePoints [0xED, 0xA0, 0x80]
#guard decode [0xF7, 0xBF, 0xBF, 0xBF] == codePoints [0xF7, 0xBF, 0xBF, 0xBF]
#guard decode [0xF0, 0x9F, 0x98, 0x80, 0xE4, 0xB8] == codePoints [0xF0, 0x9F, 0x98, 0x80, 0xE4, 0xB8]
#guard decode [0xF0, 0x9F, 0x41, 0x80] == codePoints [0xF0, 0x9F, 0x41, 0x80]
#guard decode [0xE4, 0xB8, 0xAD, 0x61] == [20013, 97]
-- 一个字符切在两段之间：先喂两个字节、存着；再喂一个字节、交出 “中”
#guard feed [] [0xE4, 0xB8] == ([], [0xE4, 0xB8])
#guard feed [0xE4, 0xB8] [0xAD, 0x61] == ([[0xE4, 0xB8, 0xAD], [0x61]], [])
-- 宽度：ASCII 1、“中” 2、组合重音 0、零宽连接符 0、😀 2
#guard width 0x41 == 1 && width 20013 == 2 && width 0x0301 == 0 && width 0x200D == 0 && width 0x1F600 == 2

end VtUtf8
end Lark
