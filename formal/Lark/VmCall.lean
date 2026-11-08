/-
apps/lvm 的证明 · 阶段 3：函数调用（call / ret 和调用帧），抢占照样看不见
先证明，再改 apps/lvm/vm/core.lark。

在 VmCore 的线程上加调用帧 fr：每一帧记着返回到哪条指令（ret）和调用前的局部变量（loc）。
- call a：把（下一条指令、现在的局部变量）压成一帧，局部变量换成新的一份（都是 0，个数不变），跳到 a；
  参数和返回值都放在操作数栈上（栈是调用者和被调用者共用的）；
- ret：弹出一帧，回到记着的指令，局部变量换回调用前的；没有帧时 ret 出错。
调用深度有上限 D：已经有 D 帧时再 call 就出错（不会无限递归把内存用完）。
其余的指令和 VmCore 一样，不碰调用帧。

证明了：
- `slice_le`、`slice_budget`、`slice_split`、`slice_one`：加了调用以后时间片的性质照样成立——
  在函数里面被抢占也看不见，什么时候被换下去都不改变算出来的东西；
- `step_fr`：走一步，调用帧要么不变，要么多一帧（只在不到 D 帧时），要么少一帧；
- `depth_le`、`slice_depth`：所以调用帧最多 D 帧；
- `call_saves`、`ret_restores`：call 记下返回的地方和局部变量，ret 原样换回来（被调用的函数改不了调用者的局部变量）。
例子（#guard）里检查了：调用一个算平方的函数、调用以后调用者的局部变量还在、在函数里被抢占结果一样、递归太深出错。
-/
import Lark.VmCore

namespace Lark
namespace VmCall

open VmCore (Sys)

inductive Ins where
  | push (n : Int) | pop | dup | swap | add | sub | mul | lt | eq
  | load (i : Nat) | store (i : Nat) | jmp (a : Nat) | jz (a : Nat) | halt
  | sys (k : Sys) | call (a : Nat) | ret
  deriving DecidableEq, Repr

/-- 一帧：返回到哪条指令、调用前的局部变量 -/
structure Fr where
  ret : Nat
  loc : List Int
  deriving DecidableEq, Repr

structure Th where
  pc : Nat
  st : List Int
  loc : List Int
  fr : List Fr
  deriving DecidableEq, Repr

inductive Out where
  | next (t : Th) | halt (v : Option Int) | fault | sys (k : Sys) (t : Th)
  deriving DecidableEq, Repr

def bin (f : Int → Int → Int) (t : Th) : Out :=
  match t.st with
  | b :: a :: r => .next { t with pc := t.pc + 1, st := f a b :: r }
  | _ => .fault

def step (c : List Ins) (D : Nat) (t : Th) : Out :=
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
    | .call a =>
      if t.fr.length < D then
        .next { t with pc := a, loc := List.replicate t.loc.length 0, fr := ⟨t.pc + 1, t.loc⟩ :: t.fr }
      else .fault
    | .ret =>
      match t.fr with
      | f :: r => .next { t with pc := f.ret, loc := f.loc, fr := r }
      | [] => .fault

/-! ## 时间片（和 VmCore 一样） -/

inductive Stop where
  | budget | halt (v : Option Int) | fault | sys (k : Sys)
  deriving DecidableEq, Repr

structure R where
  used : Nat
  th : Th
  stop : Stop
  deriving DecidableEq, Repr

def slice (c : List Ins) (D : Nat) : Nat → Th → R
  | 0, t => ⟨0, t, .budget⟩
  | n + 1, t =>
    match step c D t with
    | .next u => ⟨(slice c D n u).used + 1, (slice c D n u).th, (slice c D n u).stop⟩
    | .halt v => ⟨1, t, .halt v⟩
    | .fault => ⟨1, t, .fault⟩
    | .sys k u => ⟨1, u, .sys k⟩

theorem slice_le (c : List Ins) (D : Nat) : ∀ (n : Nat) (t : Th), (slice c D n t).used ≤ n
  | 0, _ => Nat.le_refl 0
  | n + 1, t => by
    cases h : step c D t with
    | next u =>
      have := slice_le c D n u
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

theorem slice_budget (c : List Ins) (D : Nat) :
    ∀ (n : Nat) (t : Th), (slice c D n t).stop = .budget → (slice c D n t).used = n
  | 0, _, _ => rfl
  | n + 1, t, hs => by
    cases h : step c D t with
    | next u =>
      simp only [slice, h] at hs ⊢
      have := slice_budget c D n u hs
      omega
    | halt v =>
      simp [slice, h] at hs
    | fault =>
      simp [slice, h] at hs
    | sys k u =>
      simp [slice, h] at hs

theorem slice_split (c : List Ins) (D m : Nat) : ∀ (n : Nat) (t : Th),
    (slice c D n t).used = n → (slice c D n t).stop = .budget →
    slice c D (n + m) t =
      ⟨n + (slice c D m (slice c D n t).th).used, (slice c D m (slice c D n t).th).th,
        (slice c D m (slice c D n t).th).stop⟩
  | 0, t, _, _ => by
    simp only [Nat.zero_add]
    rfl
  | n + 1, t, hu, hs => by
    cases h : step c D t with
    | next u =>
      simp only [slice, h] at hu hs ⊢
      have ih := slice_split c D m n u (by omega) hs
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

theorem slice_one (c : List Ins) (D : Nat) (t : Th) :
    slice c D 1 t = match step c D t with
      | .next u => ⟨1, u, .budget⟩
      | .halt v => ⟨1, t, .halt v⟩
      | .fault => ⟨1, t, .fault⟩
      | .sys k u => ⟨1, u, .sys k⟩ := by
  cases h : step c D t <;> simp [slice, h]

/-! ## 调用帧 -/

theorem step_fr {c : List Ins} {D : Nat} {t u : Th} (h : step c D t = .next u) :
    u.fr = t.fr ∨ (u.fr.length = t.fr.length + 1 ∧ t.fr.length < D) ∨ u.fr.length + 1 = t.fr.length := by
  unfold step bin at h
  repeat' split at h
  all_goals cases h
  all_goals
    first
    | exact Or.inl rfl
    | exact Or.inr (Or.inl ⟨by simp, by assumption⟩)
    | exact Or.inr (Or.inr (by simp_all))

theorem step_sys_fr {c : List Ins} {D : Nat} {t u : Th} {k : Sys} (h : step c D t = .sys k u) : u.fr = t.fr := by
  unfold step bin at h
  repeat' split at h
  all_goals cases h
  all_goals rfl

theorem depth_le {c : List Ins} {D : Nat} {t u : Th} (h : step c D t = .next u) (ht : t.fr.length ≤ D) :
    u.fr.length ≤ D := by
  rcases step_fr h with e | ⟨e, _⟩ | e
  · rw [e]
    exact ht
  · omega
  · omega

theorem slice_depth (c : List Ins) (D : Nat) :
    ∀ (n : Nat) (t : Th), t.fr.length ≤ D → (slice c D n t).th.fr.length ≤ D
  | 0, _, ht => ht
  | n + 1, t, ht => by
    cases h : step c D t with
    | next u =>
      simp only [slice, h]
      exact slice_depth c D n u (depth_le h ht)
    | halt v =>
      simp only [slice, h]
      exact ht
    | fault =>
      simp only [slice, h]
      exact ht
    | sys k u =>
      simp only [slice, h]
      rw [step_sys_fr h]
      exact ht

theorem call_saves {c : List Ins} {D : Nat} {t : Th} {a : Nat} (hc : c[t.pc]? = some (.call a))
    (hd : t.fr.length < D) :
    step c D t = .next { t with pc := a, loc := List.replicate t.loc.length 0, fr := ⟨t.pc + 1, t.loc⟩ :: t.fr } := by
  simp [step, hc, hd]

theorem ret_restores {c : List Ins} {D : Nat} {t : Th} {f : Fr} {r : List Fr} (hc : c[t.pc]? = some .ret)
    (hf : t.fr = f :: r) : step c D t = .next { t with pc := f.ret, loc := f.loc, fr := r } := by
  simp [step, hc, hf]

/-! ## 例子 -/

-- 调用者 loc0 = 5，调用 sq(7)（sq 自己也用 loc0），回来以后加上调用者的 loc0：49 + 5 = 54
def sq : List Ins :=
  [.push 5, .store 0, .push 7, .call 7, .load 0, .add, .halt,
   .store 0, .load 0, .load 0, .mul, .ret]

def t0 : Th := ⟨0, [], [0, 0], []⟩

#guard (slice sq 4 1000 t0).stop == .halt (some 54)
-- 在函数里被抢占（跑 5 条时在 sq 里面），换回来接着跑，结果一样
#guard (slice sq 4 5 t0).stop == .budget
#guard ((slice sq 4 5 t0).th.fr).length == 1
#guard (slice sq 4 (5 + 1000) t0).stop == (slice sq 4 1000 (slice sq 4 5 t0).th).stop
-- 无限递归：第 4 次 call 时已经有 3 帧，出错
#guard (slice [.call 0] 3 100 t0).stop == .fault
#guard (slice [.call 0] 3 100 t0).used == 4
-- 没有帧时 ret 出错
#guard (slice [.ret] 3 100 t0).stop == .fault

end VmCall
end Lark
