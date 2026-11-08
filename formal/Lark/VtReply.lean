/-
apps/lterm 的证明 · 阶段 9：回答终端查询
先证明，再写 apps/lterm/vt/term.lark 里回答查询的部分。

程序会问终端一些事，等终端从输入那边回答：
- CSI 6 n（DSR，光标在哪）：回答 ESC [ 行 ; 列 R（从 1 开始）；
- CSI 5 n（状态）：回答 ESC [ 0 n；CSI c（DA1，你是什么终端）：回答 ESC [ ? 1 ; 2 c；CSI > c（DA2）：回答 ESC [ > 0 ; 10 ; 1 c。
不回答时，等回答的程序（新版 fish、一些 shell 插件、vim 查背景色）会卡一下或者超时。

证明了：
- `dec_acc`：数字写成十进制（dec）再按解析器的办法读回来（acc），还是原来的数（不超过 65535 时）；
- `dsr_parse`：回答光标位置的那串字节，交给阶段 1 的解析器（VtParse），正好解析成一个动作 CSI [行, 列] R，
  不多也不少——所以程序（它也用同样的标准解析）读到的正是光标的位置；
- `run_digs`、`run_sep`、`run_fin`：解析器读一串数字、分号、结尾字节时的样子（证明 dsr_parse 用）。
例子（#guard）里检查了：十进制、几个位置的回答、回答解析回来。
别的回答是固定的字节串，Lark 里直接写；DECCKM（?1，方向键发 ESC O A）只是记着交给外面的终端，不动屏幕。
-/
import Lark.Lsp
import Lark.VtParse

namespace Lark
namespace VtReply

open VtParse

/-- 十进制，高位在前（字节） -/
def dec (n : Nat) : List Nat :=
  if h : n < 10 then [n + 0x30] else dec (n / 10) ++ [n % 10 + 0x30]
termination_by n
decreasing_by omega

/-- 解析器读数字的办法：cur * 10 + 这一位，最多 maxParam -/
def acc (k : Nat) : List Nat → Nat
  | [] => k
  | d :: r => acc (min maxParam (k * 10 + (d - 0x30))) r

theorem acc_append : ∀ (a b : List Nat) (k : Nat), acc k (a ++ b) = acc (acc k a) b
  | [], _, _ => rfl
  | _ :: r, b, _ => acc_append r b _

theorem acc_one (k d : Nat) : acc k [d] = min maxParam (k * 10 + (d - 0x30)) := rfl

theorem dec_dig (n : Nat) : ∀ c ∈ dec n, 0x30 ≤ c ∧ c ≤ 0x39 := by
  intro c hc
  rw [dec] at hc
  split at hc
  · simp at hc
    omega
  · simp only [List.mem_append, List.mem_singleton] at hc
    rcases hc with hc | hc
    · exact dec_dig (n / 10) c hc
    · omega
termination_by n
decreasing_by all_goals omega

theorem dec_ne (n : Nat) : dec n ≠ [] := by
  rw [dec]
  split <;> simp

theorem dec_acc (n : Nat) (hn : n ≤ maxParam) : acc 0 (dec n) = n := by
  unfold dec
  split
  · rw [acc_one]
    unfold maxParam at hn ⊢
    omega
  · rw [acc_append, dec_acc (n / 10) (by unfold maxParam at hn ⊢; omega), acc_one]
    unfold maxParam at hn ⊢
    omega
termination_by n
decreasing_by all_goals omega

/-! ## 解析器读回答 -/

theorem step_dig (p : P) (c : Nat) (hs : p.st = .csiEntry ∨ p.st = .csiParam) (hc : 0x30 ≤ c ∧ c ≤ 0x39) :
    step p c = (goto (digit p c) .csiParam, none) := by
  have h1 : ¬(c = 0x18 ∨ c = 0x1A) := by omega
  have h2 : ¬c = 0x1B := by omega
  have h3 : ¬c < 0x20 := by omega
  have h4 : isPriv c = false := by
    unfold isPriv
    simp
    omega
  have h5 : isDig c = true := by
    unfold isDig
    simp
    omega
  rcases hs with h | h
  · simp [step, body, params, h, h1, h2, h3, h4, h5]
  · simp [step, body, params, h, h1, h2, h3, h4, h5]

theorem run_digs (ds : List Nat) {p : P} {rest : List Nat} (hs : p.st = .csiEntry ∨ p.st = .csiParam)
    (hd : ∀ c ∈ ds, 0x30 ≤ c ∧ c ≤ 0x39) (hne : ds ≠ []) :
    run p (ds ++ rest) = run { p with st := .csiParam, cur := acc p.cur ds, any := true } rest := by
  induction ds generalizing p with
  | nil => exact absurd rfl hne
  | cons d r ih =>
    have e := step_dig p d hs (hd d (by simp))
    cases r with
    | nil =>
      show (step p d).2.toList ++ run (step p d).1 rest = _
      rw [e]
      rfl
    | cons d2 r2 =>
      have ih2 := ih (p := goto (digit p d) .csiParam) (Or.inr rfl)
        (fun c hc => hd c (List.mem_cons_of_mem d hc)) (by simp)
      show (step p d).2.toList ++ run (step p d).1 ((d2 :: r2) ++ rest) = _
      rw [e]
      exact ih2

theorem run_sep {p : P} {rest : List Nat} (h : p.st = .csiParam) :
    run p (0x3B :: rest) = run (goto (sep p) .csiParam) rest := by
  have e : step p 0x3B = (goto (sep p) .csiParam, none) := by
    simp [step, body, params, h, isDig, isSep, isPriv]
  show (step p 0x3B).2.toList ++ run (step p 0x3B).1 rest = _
  rw [e]
  rfl

theorem run_fin {p : P} (h : p.st = .csiParam) :
    run p [0x52] = [.csi (allParams p) p.inter 0x52] := by
  have e : step p 0x52 = (clear .ground, some (.csi (allParams p) p.inter 0x52)) := by
    simp [step, body, params, h, isDig, isSep, isPriv, isInter, isFinal]
  show (step p 0x52).2.toList ++ run (step p 0x52).1 [] = _
  rw [e]
  rfl

/-- 回答光标位置：ESC [ 行 ; 列 R（y、x 从 0 开始，回答里从 1 开始） -/
def dsr (y x : Nat) : List Nat := 0x1B :: 0x5B :: (dec (y + 1) ++ (0x3B :: (dec (x + 1) ++ [0x52])))

theorem dsr_parse {y x : Nat} (hy : y + 1 ≤ maxParam) (hx : x + 1 ≤ maxParam) :
    run init (dsr y x) = [.csi [y + 1, x + 1] [] 0x52] := by
  have e0 : run init (dsr y x) = run (clear .csiEntry) (dec (y + 1) ++ (0x3B :: (dec (x + 1) ++ [0x52]))) := rfl
  rw [e0, run_digs (dec (y + 1)) _ (dec_dig _) (dec_ne _), run_sep _,
    run_digs (dec (x + 1)) _ (dec_dig _) (dec_ne _), run_fin _]
  show [Act.csi [acc 0 (dec (y + 1)), acc 0 (dec (x + 1))] [] 0x52] = _
  rw [dec_acc _ hy, dec_acc _ hx]
  all_goals first | rfl | exact Or.inl rfl | exact Or.inr rfl

/-! ## 例子 -/

#guard dec 0 == [0x30]
#guard dec 7 == [0x37]
#guard dec 120 == [0x31, 0x32, 0x30]
#guard acc 0 (dec 65535) == 65535
#guard dsr 0 0 == [0x1B, 0x5B, 0x31, 0x3B, 0x31, 0x52]
#guard dsr 23 79 == [0x1B, 0x5B, 0x32, 0x34, 0x3B, 0x38, 0x30, 0x52]
#guard run init (dsr 4 11) == [.csi [5, 12] [] 0x52]

end VtReply
end Lark
