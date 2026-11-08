/-
apps/lvm 的证明 · 阶段 1：虚拟机的指令和一个线程怎么跑（可以随时被抢占）
先证明，再写 apps/lvm/vm/core.lark。

apps/lvm 是从零写的轻量线程：线程跑在一个小的栈式虚拟机里（不是系统线程，也不是 Lark 运行时的任务），
由 lvm 自己的调度器放到好几个工作线程上（M:N，阶段 2 证明调度）。像 Erlang 一样按"跑了几条指令"抢占：
一个线程每次最多跑 budget 条指令（一个时间片，slice），用完了就换下一个，线程自己不用让出。

一个线程（Th）：pc、操作数栈 st、局部变量 loc。指令（Ins）：
- 栈和算术：push n、pop、dup、swap、add、sub、mul、lt、eq（比较的结果是 1 / 0）；
- 局部变量：load i、store i；跳转：jmp a、jz a（栈顶是 0 时跳）；结束：halt（结果是栈顶）；
- sys k：要调度器做的事（spawn、yield、通道的 send / recv、sleep、join……），线程停在下一条指令，参数留在栈上。
出错（栈不够、局部变量越界、pc 跑出程序）时线程 fault，不会弄坏别的线程。

证明了：
- `slice_le`：一个时间片最多跑 budget 条指令（抢占是有界的：别的线程等的时间有上限）；
- `slice_budget`：时间片因为用完而停下时，正好跑了 budget 条；
- `slice_split`：先跑 n 条（被抢占）、换回来再跑 m 条，和一口气跑 n + m 条结果完全一样——
  抢占对线程是看不见的，什么时候被换下去都不改变它算出来的东西；
- `slice_one`：时间片只有 1 时就是走一步（step）。
例子（#guard）里检查了：1 加到 10、在不同的地方被抢占结果都一样、出错、sys 停下。
-/
import Lark.Lsp

namespace Lark
namespace VmCore

inductive Sys where
  | yield | spawn (a : Nat) | newch | send | recv | sleep | join | self | print
  deriving DecidableEq, Repr

inductive Ins where
  | push (n : Int) | pop | dup | swap | add | sub | mul | lt | eq
  | load (i : Nat) | store (i : Nat) | jmp (a : Nat) | jz (a : Nat) | halt
  | sys (k : Sys)
  deriving DecidableEq, Repr

structure Th where
  pc : Nat
  st : List Int
  loc : List Int
  deriving DecidableEq, Repr

/-- 走一步的结果：接着跑、结束（栈顶）、出错、要调度器做事（线程已经停在下一条指令） -/
inductive Out where
  | next (t : Th) | halt (v : Option Int) | fault | sys (k : Sys) (t : Th)
  deriving DecidableEq, Repr

def bin (f : Int → Int → Int) (t : Th) : Out :=
  match t.st with
  | b :: a :: r => .next { t with pc := t.pc + 1, st := f a b :: r }
  | _ => .fault

def step (c : List Ins) (t : Th) : Out :=
  match c[t.pc]? with
  | none => .fault
  | some i =>
    match i with
    | .push n => .next { t with pc := t.pc + 1, st := n :: t.st }
    | .pop =>
      match t.st with
      | _ :: r => .next { t with pc := t.pc + 1, st := r }
      | [] => .fault
    | .dup =>
      match t.st with
      | a :: r => .next { t with pc := t.pc + 1, st := a :: a :: r }
      | [] => .fault
    | .swap =>
      match t.st with
      | b :: a :: r => .next { t with pc := t.pc + 1, st := a :: b :: r }
      | _ => .fault
    | .add => bin (fun a b => a + b) t
    | .sub => bin (fun a b => a - b) t
    | .mul => bin (fun a b => a * b) t
    | .lt => bin (fun a b => if a < b then 1 else 0) t
    | .eq => bin (fun a b => if a = b then 1 else 0) t
    | .load k =>
      match t.loc[k]? with
      | some v => .next { t with pc := t.pc + 1, st := v :: t.st }
      | none => .fault
    | .store k =>
      match t.st with
      | v :: r => if k < t.loc.length then .next { t with pc := t.pc + 1, st := r, loc := t.loc.set k v } else .fault
      | [] => .fault
    | .jmp a => .next { t with pc := a }
    | .jz a =>
      match t.st with
      | v :: r => .next { t with pc := if v = 0 then a else t.pc + 1, st := r }
      | [] => .fault
    | .halt => .halt t.st.head?
    | .sys k => .sys k { t with pc := t.pc + 1 }

/-! ## 时间片 -/

/-- 时间片为什么停下：用完了（被抢占）、结束、出错、要调度器做事 -/
inductive Stop where
  | budget | halt (v : Option Int) | fault | sys (k : Sys)
  deriving DecidableEq, Repr

/-- 跑了几条指令、线程现在的样子、为什么停下 -/
structure R where
  used : Nat
  th : Th
  stop : Stop
  deriving DecidableEq, Repr

/-- 最多跑 n 条指令 -/
def slice (c : List Ins) : Nat → Th → R
  | 0, t => ⟨0, t, .budget⟩
  | n + 1, t =>
    match step c t with
    | .next u => ⟨(slice c n u).used + 1, (slice c n u).th, (slice c n u).stop⟩
    | .halt v => ⟨1, t, .halt v⟩
    | .fault => ⟨1, t, .fault⟩
    | .sys k u => ⟨1, u, .sys k⟩

theorem slice_le (c : List Ins) : ∀ (n : Nat) (t : Th), (slice c n t).used ≤ n
  | 0, _ => Nat.le_refl 0
  | n + 1, t => by
    cases h : step c t with
    | next u =>
      have := slice_le c n u
      simp only [slice, h]
      omega
    | halt v =>
      simp only [slice, h]
      omega
    | fault =>
      simp only [slice, h]
      omega
    | sys k u =>
      simp only [slice, h]
      omega

theorem slice_budget (c : List Ins) : ∀ (n : Nat) (t : Th), (slice c n t).stop = .budget → (slice c n t).used = n
  | 0, _, _ => rfl
  | n + 1, t, hs => by
    cases h : step c t with
    | next u =>
      simp only [slice, h] at hs ⊢
      have := slice_budget c n u hs
      omega
    | halt v =>
      simp [slice, h] at hs
    | fault =>
      simp [slice, h] at hs
    | sys k u =>
      simp [slice, h] at hs

theorem slice_split (c : List Ins) (m : Nat) : ∀ (n : Nat) (t : Th),
    (slice c n t).used = n → (slice c n t).stop = .budget →
    slice c (n + m) t =
      ⟨n + (slice c m (slice c n t).th).used, (slice c m (slice c n t).th).th, (slice c m (slice c n t).th).stop⟩
  | 0, t, _, _ => by
    simp only [Nat.zero_add]
    rfl
  | n + 1, t, hu, hs => by
    cases h : step c t with
    | next u =>
      simp only [slice, h] at hu hs ⊢
      have ih := slice_split c m n u (by omega) hs
      rw [Nat.add_right_comm n 1 m]
      simp only [slice, h, ih]
      congr 1
      omega
    | halt v =>
      simp [slice, h] at hs
    | fault =>
      simp [slice, h] at hs
    | sys k u =>
      simp [slice, h] at hs

theorem slice_one (c : List Ins) (t : Th) :
    slice c 1 t = match step c t with
      | .next u => ⟨1, u, .budget⟩
      | .halt v => ⟨1, t, .halt v⟩
      | .fault => ⟨1, t, .fault⟩
      | .sys k u => ⟨1, u, .sys k⟩ := by
  cases h : step c t <;> simp [slice, h]

/-! ## 例子 -/

-- 1 加到 10：loc0 = i，loc1 = s
def sum10 : List Ins :=
  [.push 10, .store 0, .push 0, .store 1,
   .load 0, .jz 15, .load 1, .load 0, .add, .store 1, .load 0, .push 1, .sub, .store 0, .jmp 4,
   .load 1, .halt]

def t0 : Th := ⟨0, [], [0, 0]⟩

#guard (slice sum10 1000 t0).stop == .halt (some 55)
-- 被抢占：跑 7 条停下，换回来接着跑，结果一样
#guard (slice sum10 7 t0).stop == .budget
#guard (slice sum10 1000 (slice sum10 7 t0).th).stop == .halt (some 55)
#guard (slice sum10 (7 + 1000) t0).stop == (slice sum10 1000 (slice sum10 7 t0).th).stop
-- 出错：栈是空的时候 add；局部变量越界
#guard (slice [.add] 10 t0).stop == .fault
#guard (slice [.push 1, .store 5] 10 t0).stop == .fault
-- 要调度器做事：停在下一条指令，参数在栈上
#guard slice [.push 3, .sys .sleep, .halt] 10 t0 == ⟨2, ⟨2, [3], [0, 0]⟩, .sys .sleep⟩

end VmCore
end Lark
