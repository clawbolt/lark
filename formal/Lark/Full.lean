/-
Lark 可靠性证明 · 合并：跳出、defer、借用的 for / match、调用和闭包放在一门语言里

把 Exit.lean（嵌套作用域、defer、break / continue / return）和 Drop.lean 的借用冻结（R11、R16）合在一起：
- bor x s：借用的 for / match，s 里经由借用读 x 的盒子（useB k：第 k 层借用，0 是最里面的）。
  借用开始时记下 x 的地址；借用期间 x 冻结，不能移走、不能重新赋值。
- 借用期间可以声明、defer、break、continue、return，跳出时照样逐层释放、执行 defer。
- call m1 x1 m2 x2：两个参数的调用，每个参数是只读、inout 或 take（Call.lean）。调用时先取好每个参数的地址，
  再执行被调用的函数：读只读参数的盒子，给 inout 参数存新盒子（旧的释放），释放 take 参数的盒子。
  两个参数是同一个变量时，前一个参数做的事会让后一个参数的地址失效，所以要排他性（R7、R8）。

不变量是 Exit.lean 的 Own 加上 Pins：第 k 层借用记下的地址正是第 k 个冻结变量现在的地址。
Pins 只在 x 的值变的时候可能被破坏，而检查保证冻结的变量不被移走、不被赋值；离开 decl 的变量不在作用域里，
也就不可能是冻结的（冻结的变量有值，作用域外的变量是空的）。

定理 `full_sound`：通过检查的程序，不管从哪里、以什么方式离开，都不会读到空位或释放了的盒子（包括经由借用读）、
不会重复释放，defer 执行时读得到值；结束时堆是空的。
复用 Exit.lean 的存储、释放和引理，没有改它。闭包（Clo.lean）写成这些语句的组合（见文件后面），所以 full_sound 也管它们。
-/
import Lark.Exit
import Lark.Call
import Lark.Clo

namespace Lark
namespace Full
open Exit

inductive FS where
  | skip
  | use (x : Var)
  | useB (k : Nat)
  | assign (x : Var) (o : OE)
  | seq (s t : FS)
  | ite (b : Bool) (s t : FS)
  | brk
  | cont
  | ret
  | loop (b : FS)
  | decl (x : Var) (o : OE) (s : FS)
  | defer (x : Var) (s : FS)
  | bor (x : Var) (s : FS)
  | call (m1 : Mode) (x1 : Var) (m2 : Mode) (x2 : Var)
  deriving Repr

def nth : List Nat → Nat → Option Nat
  | [], _ => none
  | a :: _, 0 => some a
  | _ :: l, k + 1 => nth l k

/-- 经由第 k 层借用读：记下的地址已经释放了是错误 -/
def readB (bs : List Nat) (k : Nat) (μ : M) : Option M :=
  match nth bs k with
  | none => none
  | some a => if μ.heap a then some μ else none

/-- 被调用的函数对一个参数做的事。调用时先给每个参数取好地址 a（read、take 是盒子的地址，像生成的 C 那样传过去），
    然后函数体：read 读这个盒子；inout 经由指针读调用者的变量，再给它存一个新盒子（旧的释放）；
    take 释放这个盒子（调用者那边的变量清零）。两个参数是同一个变量时，前一个参数做的事会让后一个参数的地址失效 -/
def effect (μ : M) (md : Mode) (x : Var) (a : Option Nat) : Option M :=
  match md, a with
  | _, none => none
  | .read, some b => if μ.heap b then some μ else none
  | .inout, some _ =>
    match μ.st x with
    | none => none
    | some c =>
      if μ.heap c then place x (some μ.next) { μ with heap := put μ.heap μ.next true, next := μ.next + 1 }
      else none
  | .take, some b => if μ.heap b then some { μ with st := put μ.st x none, heap := put μ.heap b false } else none

/-- bs 是借用记下的地址，最里面的在前 -/
def evalF : Nat → List Nat → FS → M → Res
  | 0, _, _, _ => .out
  | _ + 1, _, .skip, μ => .ok μ
  | _ + 1, _, .use x, μ => lift .ok (useVar x) μ
  | _ + 1, bs, .useB k, μ => lift .ok (readB bs k) μ
  | _ + 1, _, .assign x o, μ =>
    match evalO μ o with
    | none => .err
    | some (a, μ1) => lift .ok (place x (some a)) μ1
  | n + 1, bs, .seq s t, μ =>
    match evalF n bs s μ with
    | .ok μ' => evalF n bs t μ'
    | .brk μ' => .brk μ'
    | .cont μ' => .cont μ'
    | .ret μ' => .ret μ'
    | .err => .err
    | .out => .out
  | n + 1, bs, .ite b s t, μ =>
    match b with
    | true => evalF n bs s μ
    | false => evalF n bs t μ
  | _ + 1, _, .brk, μ => .brk μ
  | _ + 1, _, .cont, μ => .cont μ
  | _ + 1, _, .ret, μ => .ret μ
  | n + 1, bs, .loop b, μ =>
    match evalF n bs b μ with
    | .ok μ' => evalF n bs (.loop b) μ'
    | .cont μ' => evalF n bs (.loop b) μ'
    | .brk μ' => .ok μ'
    | .ret μ' => .ret μ'
    | .err => .err
    | .out => .out
  | n + 1, bs, .decl x o s, μ =>
    match evalO μ o with
    | none => .err
    | some (a, μ1) =>
      match place x (some a) μ1 with
      | none => .err
      | some μ2 => (evalF n bs s μ2).fin (place x none)
  | n + 1, bs, .defer x s, μ => (evalF n bs s μ).fin (useVar x)
  | n + 1, bs, .bor x s, μ =>
    match μ.st x with
    | none => .err
    | some a => evalF n (a :: bs) s μ
  | _ + 1, _, .call m1 x1 m2 x2, μ =>
    match effect μ m1 x1 (μ.st x1) with
    | none => .err
    | some μ' => lift .ok (fun ν => effect ν m2 x2 (μ.st x2)) μ'

/-! ## 检查：在 Exit.lean 的检查上加 f（冻结的变量，最里面的借用在前） -/

/-- 右边移走的不能是冻结的 -/
def frozenOk (f : List Var) : OE → Bool
  | .move y => !decide (y ∈ f)
  | .mk => true

/-- 一个实参：在作用域里、有值；inout、take 的不是冻结的；take 的不是 defer 钉住的 -/
abbrev ArgOk (sc p f m : List Var) (md : Mode) (x : Var) : Prop :=
  x ∈ sc ∧ x ∉ m ∧ (md ≠ .read → x ∉ f) ∧ (md = .take → x ∉ p)

/-- take 的实参调用以后没有值了 -/
def addT (x : Var) (m : List Var) : Mode → List Var
  | .take => x :: m
  | _ => m

def chkF : List Var → List Var → List Var → FS → List Var → Option Exit.Out
  | _, _, _, .skip, m => some ⟨some m, [], [], []⟩
  | sc, _, _, .use x, m => if x ∈ sc ∧ x ∉ m then some ⟨some m, [], [], []⟩ else none
  | _, _, f, .useB k, m => if k < f.length then some ⟨some m, [], [], []⟩ else none
  | sc, p, f, .assign x o, m =>
    if x ∈ sc ∧ x ∉ f ∧ frozenOk f o = true then                              -- R16：冻结的不能重新赋值
      match chkO sc p m o with
      | none => none
      | some m1 => some ⟨some (m1.filter (fun y => y != x)), [], [], []⟩
    else none
  | sc, p, f, .seq s t, m =>
    match chkF sc p f s m with
    | none => none
    | some o1 =>
      match o1.fall with
      | none => some o1
      | some m1 =>
        match chkF sc p f t m1 with
        | none => none
        | some o2 => some ⟨o2.fall, o1.brks ++ o2.brks, o1.conts ++ o2.conts, o1.rets ++ o2.rets⟩
  | sc, p, f, .ite _ s t, m =>
    match chkF sc p f s m, chkF sc p f t m with
    | some os, some ot =>
      some ⟨joinF os.fall ot.fall, os.brks ++ ot.brks, os.conts ++ ot.conts, os.rets ++ ot.rets⟩
    | _, _ => none
  | _, _, _, .brk, m => some ⟨none, [m], [], []⟩
  | _, _, _, .cont, m => some ⟨none, [], [m], []⟩
  | _, _, _, .ret, m => some ⟨none, [], [], [m]⟩
  | sc, p, f, .loop b, m =>
    match chkF sc p f b m with
    | none => none
    | some o =>
      if subF o.fall m && o.conts.all (fun c => sub c m) then
        some ⟨some (m ++ o.fall.getD [] ++ unionAll o.brks), [], [], o.rets⟩
      else none
  | sc, p, f, .decl x o s, m =>
    if x ∉ sc ∧ frozenOk f o = true then
      match chkO sc p m o with
      | none => none
      | some m1 => (chkF (x :: sc) p f s (m1.filter (fun y => y != x))).map (Exit.Out.hide x)
    else none
  | sc, p, f, .defer x s, m => if x ∈ sc ∧ x ∉ m then chkF sc (x :: p) f s m else none
  | sc, p, f, .bor x s, m => if x ∈ sc ∧ x ∉ m then chkF sc p (x :: f) s m else none   -- R11
  -- R6–R8（own_call）：实参要有值；inout、take 的不能是冻结的；take 的不能是 defer 钉住的；
  -- 两个实参是同一个变量时两个都得是只读的（排他性，Call.lean 的 Excl）
  | sc, p, f, .call m1 x1 m2 x2, m =>
    if ArgOk sc p f m m1 x1 ∧ ArgOk sc p f m m2 x2 ∧ (x1 = x2 → m1 = .read ∧ m2 = .read) then
      some ⟨some (addT x2 (addT x1 m m1) m2), [], [], []⟩
    else none

/-! ## 不变量：Exit.lean 的 Own，加上 Pins -/

/-- 第 k 层借用记下的地址是第 k 个冻结变量现在的地址 -/
def Pins (st : Var → Option Nat) : List Var → List Nat → Prop
  | [], [] => True
  | y :: f, a :: bs => st y = some a ∧ Pins st f bs
  | _, _ => False

theorem pins_congr {st st' : Var → Option Nat} : ∀ (f : List Var) (bs : List Nat),
    (∀ y, y ∈ f → st' y = st y) → Pins st f bs → Pins st' f bs
  | [], [], _, _ => trivial
  | [], _ :: _, _, h => by simp [Pins] at h
  | _ :: _, [], _, h => by simp [Pins] at h
  | y :: f, a :: bs, hs, h => by
    simp only [Pins] at h ⊢
    exact ⟨by rw [hs y (by simp)]; exact h.1, pins_congr f bs (fun z hz => hs z (by simp [hz])) h.2⟩

/-- 冻结的变量有值 -/
theorem pins_some {st : Var → Option Nat} : ∀ (f : List Var) (bs : List Nat),
    Pins st f bs → ∀ y, y ∈ f → st y ≠ none
  | [], _, _, y, hy => by simp at hy
  | _ :: _, [], h, _, _ => by simp [Pins] at h
  | x :: f, a :: bs, h, y, hy => by
    simp only [Pins] at h
    rcases List.mem_cons.mp hy with e | hy
    · rw [e, h.1]
      simp
    · exact pins_some f bs h.2 y hy

theorem pins_nth {st : Var → Option Nat} : ∀ (f : List Var) (bs : List Nat),
    Pins st f bs → ∀ k, k < f.length → ∃ a y, nth bs k = some a ∧ st y = some a
  | [], _, _, k, hk => by simp at hk
  | _ :: _, [], h, _, _ => by simp [Pins] at h
  | x :: f, a :: bs, h, 0, _ => by
    simp only [Pins] at h
    exact ⟨a, x, rfl, h.1⟩
  | x :: f, a :: bs, h, k + 1, hk => by
    simp only [Pins] at h
    have hk' : k < f.length := by simp at hk; omega
    exact pins_nth f bs h.2 k hk'

/-- 算右边：冻结的变量不变 -/
theorem evalO_st {μ μ1 : M} {a : Nat} {f : List Var} : ∀ (o : OE), evalO μ o = some (a, μ1) →
    frozenOk f o = true → ∀ y, y ∈ f → μ1.st y = μ.st y
  | .mk, h, _, _, _ => by
    simp only [evalO, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    rfl
  | .move z, h, hf, y, hy => by
    simp [frozenOk] at hf
    cases hz : μ.st z with
    | none => simp [evalO, hz] at h
    | some b =>
      simp only [evalO, hz, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl⟩ := h
      have hyz : y ≠ z := fun e => hf (e ▸ hy)
      exact put_ne _ _ hyz

/-- 存进 x、释放 x：别的变量不变 -/
theorem place_st {x : Var} {v : Option Nat} {μ μ2 : M} (h : place x v μ = some μ2) :
    ∀ y, y ≠ x → μ2.st y = μ.st y := by
  intro y hy
  unfold place at h
  cases hx : μ.st x with
  | none =>
    simp only [hx, Option.some.injEq] at h
    rw [← h]
    exact put_ne _ _ hy
  | some b =>
    simp only [hx] at h
    split at h
    · simp only [Option.some.injEq] at h
      rw [← h]
      exact put_ne _ _ hy
    · cases h

def GoodF (sc p f : List Var) (bs : List Nat) (o : Exit.Out) : Res → Prop
  | .ok μ => ∃ mf, o.fall = some mf ∧ Own sc p mf μ ∧ Pins μ.st f bs
  | .brk μ => ∃ mb, mb ∈ o.brks ∧ Own sc p mb μ ∧ Pins μ.st f bs
  | .cont μ => ∃ mc, mc ∈ o.conts ∧ Own sc p mc μ ∧ Pins μ.st f bs
  | .ret μ => ∃ mr, mr ∈ o.rets ∧ Own sc p mr μ ∧ Pins μ.st f bs
  | .err => False
  | .out => True

/-- 离开一层时做 fn：fn 成功、换成外层的 Own，冻结的变量不变 -/
theorem good_finF {sc p sc' p' f : List Var} {bs : List Nat} {o : Exit.Out} {fn : M → Option M} {r : Res}
    (hf : ∀ m μ, Own sc p m μ → Pins μ.st f bs → ∃ μ', fn μ = some μ' ∧ Own sc' p' m μ' ∧ Pins μ'.st f bs)
    (g : GoodF sc p f bs o r) : GoodF sc' p' f bs o (r.fin fn) := by
  cases r with
  | ok μ =>
    simp only [GoodF] at g
    obtain ⟨mf, h1, h2, h3⟩ := g
    obtain ⟨μ', e, h4, h5⟩ := hf mf μ h2 h3
    simp only [Res.fin, lift, e, GoodF]
    exact ⟨mf, h1, h4, h5⟩
  | brk μ =>
    simp only [GoodF] at g
    obtain ⟨mb, h1, h2, h3⟩ := g
    obtain ⟨μ', e, h4, h5⟩ := hf mb μ h2 h3
    simp only [Res.fin, lift, e, GoodF]
    exact ⟨mb, h1, h4, h5⟩
  | cont μ =>
    simp only [GoodF] at g
    obtain ⟨mc, h1, h2, h3⟩ := g
    obtain ⟨μ', e, h4, h5⟩ := hf mc μ h2 h3
    simp only [Res.fin, lift, e, GoodF]
    exact ⟨mc, h1, h4, h5⟩
  | ret μ =>
    simp only [GoodF] at g
    obtain ⟨mr, h1, h2, h3⟩ := g
    obtain ⟨μ', e, h4, h5⟩ := hf mr μ h2 h3
    simp only [Res.fin, lift, e, GoodF]
    exact ⟨mr, h1, h4, h5⟩
  | err => exact g
  | out => trivial

/-- 离开 decl x：x 不是冻结的，所以 Pins 不受影响 -/
theorem good_hideF {sc p f : List Var} {bs : List Nat} {x : Var} {o : Exit.Out} {r : Res}
    (hx : x ∉ sc) (hxp : x ∉ p) (hxf : x ∉ f)
    (g : GoodF (x :: sc) p f bs o r) : GoodF sc p f bs (o.hide x) (r.fin (place x none)) := by
  have keep : ∀ (μ μ' : M), place x none μ = some μ' → Pins μ.st f bs → Pins μ'.st f bs :=
    fun μ μ' e hp => pins_congr f bs (fun y hy => place_st e y (fun e' => hxf (e' ▸ hy))) hp
  cases r with
  | ok μ =>
    simp only [GoodF] at g
    obtain ⟨mf, h1, h2, h3⟩ := g
    obtain ⟨μ', e, h4⟩ := drop_ok h2 hx hxp
    simp only [Res.fin, lift, e, GoodF]
    exact ⟨_, by simp [Exit.Out.hide, h1], own_hide hx h4, keep μ μ' e h3⟩
  | brk μ =>
    simp only [GoodF] at g
    obtain ⟨mb, h1, h2, h3⟩ := g
    obtain ⟨μ', e, h4⟩ := drop_ok h2 hx hxp
    simp only [Res.fin, lift, e, GoodF]
    exact ⟨_, List.mem_map.mpr ⟨mb, h1, rfl⟩, own_hide hx h4, keep μ μ' e h3⟩
  | cont μ =>
    simp only [GoodF] at g
    obtain ⟨mc, h1, h2, h3⟩ := g
    obtain ⟨μ', e, h4⟩ := drop_ok h2 hx hxp
    simp only [Res.fin, lift, e, GoodF]
    exact ⟨_, List.mem_map.mpr ⟨mc, h1, rfl⟩, own_hide hx h4, keep μ μ' e h3⟩
  | ret μ =>
    simp only [GoodF] at g
    obtain ⟨mr, h1, h2, h3⟩ := g
    obtain ⟨μ', e, h4⟩ := drop_ok h2 hx hxp
    simp only [Res.fin, lift, e, GoodF]
    exact ⟨_, List.mem_map.mpr ⟨mr, h1, rfl⟩, own_hide hx h4, keep μ μ' e h3⟩
  | err => exact g
  | out => trivial

theorem good_branchF {sc p f : List Var} {bs : List Nat} {os o : Exit.Out} {r : Res}
    (hf : ∀ mf, os.fall = some mf → ∃ mf', o.fall = some mf' ∧ ∀ x, x ∈ mf → x ∈ mf')
    (hb : ∀ mb, mb ∈ os.brks → mb ∈ o.brks)
    (hc : ∀ mc, mc ∈ os.conts → mc ∈ o.conts)
    (hr : ∀ mr, mr ∈ os.rets → mr ∈ o.rets)
    (g : GoodF sc p f bs os r) : GoodF sc p f bs o r := by
  cases r with
  | ok μ =>
    simp only [GoodF] at g ⊢
    obtain ⟨mf, h1, h2, h3⟩ := g
    obtain ⟨mf', h4, h5⟩ := hf mf h1
    exact ⟨mf', h4, own_mono h5 h2, h3⟩
  | brk μ =>
    simp only [GoodF] at g ⊢
    obtain ⟨mb, h1, h2, h3⟩ := g
    exact ⟨mb, hb mb h1, h2, h3⟩
  | cont μ =>
    simp only [GoodF] at g ⊢
    obtain ⟨mc, h1, h2, h3⟩ := g
    exact ⟨mc, hc mc h1, h2, h3⟩
  | ret μ =>
    simp only [GoodF] at g ⊢
    obtain ⟨mr, h1, h2, h3⟩ := g
    exact ⟨mr, hr mr h1, h2, h3⟩
  | err => exact g
  | out => trivial

/-- 借用结束：里面多冻结的一层去掉 -/
theorem good_pop {sc p f : List Var} {bs : List Nat} {x : Var} {a : Nat} {o : Exit.Out} {r : Res}
    (g : GoodF sc p (x :: f) (a :: bs) o r) : GoodF sc p f bs o r := by
  cases r with
  | ok μ =>
    simp only [GoodF, Pins] at g ⊢
    obtain ⟨mf, h1, h2, -, h3⟩ := g
    exact ⟨mf, h1, h2, h3⟩
  | brk μ =>
    simp only [GoodF, Pins] at g ⊢
    obtain ⟨mb, h1, h2, -, h3⟩ := g
    exact ⟨mb, h1, h2, h3⟩
  | cont μ =>
    simp only [GoodF, Pins] at g ⊢
    obtain ⟨mc, h1, h2, -, h3⟩ := g
    exact ⟨mc, h1, h2, h3⟩
  | ret μ =>
    simp only [GoodF, Pins] at g ⊢
    obtain ⟨mr, h1, h2, -, h3⟩ := g
    exact ⟨mr, h1, h2, h3⟩
  | err => exact g
  | out => trivial

/-! ## 调用 -/

theorem ex_some {o : Option Nat} (h : o ≠ none) : ∃ a, o = some a := by
  cases o with
  | none => exact absurd rfl h
  | some a => exact ⟨a, rfl⟩

theorem mem_addT {y x : Var} {m : List Var} : ∀ {md : Mode}, y ∈ addT x m md → (md = .take ∧ y = x) ∨ y ∈ m
  | .read, h => Or.inr h
  | .inout, h => Or.inr h
  | .take, h => by
    rcases List.mem_cons.mp h with e | h
    · exact Or.inl ⟨rfl, e⟩
    · exact Or.inr h

/-- 在路上的盒子释放掉 -/
theorem fly_free {sc p m : List Var} {a : Nat} {μ : M} (F : Fly sc p m a μ) :
    Own sc p m { μ with heap := put μ.heap a false } := by
  refine ⟨?_, F.uniq, ?_, ?_, F.out, F.full, F.pin⟩
  · intro y c hy
    have hca : c ≠ a := fun e => F.alone y (e ▸ hy)
    show put μ.heap a false c = true
    rw [put_ne _ _ hca]
    exact F.live y c hy
  · intro c hc
    have hc' : put μ.heap a false c = true := hc
    by_cases hca : c = a
    · rw [hca, put_same] at hc'
      cases hc'
    · rw [put_ne _ _ hca] at hc'
      rcases F.noleak c hc' with e | h
      · exact absurd e hca
      · exact h
  · intro c hc
    have hc' : put μ.heap a false c = true := hc
    by_cases hca : c = a
    · rw [hca, put_same] at hc'
      cases hc'
    · rw [put_ne _ _ hca] at hc'
      exact F.fresh c hc'

/-- 一个参数：被调用的函数做的事成功，不变量保持，只有这个变量可能变；只读的什么也不变 -/
theorem effect_ok {sc p f m : List Var} {bs : List Nat} {μ : M} {md : Mode} {x : Var} {b : Nat}
    (hO : Own sc p m μ) (hP : Pins μ.st f bs) (hsc : x ∈ sc) (hm : x ∉ m) (hx : μ.st x = some b)
    (hf : md ≠ .read → x ∉ f) (hp : md = .take → x ∉ p) :
    ∃ μ', effect μ md x (some b) = some μ' ∧ Own sc p (addT x m md) μ' ∧ Pins μ'.st f bs ∧
      (∀ y, y ≠ x → μ'.st y = μ.st y) ∧ (md = .read → μ' = μ) := by
  have hb := hO.live x b hx
  cases md with
  | read =>
    exact ⟨μ, by simp [effect, hb], hO, hP, fun _ _ => rfl, fun _ => rfl⟩
  | inout =>
    have hxf : x ∉ f := hf (by decide)
    obtain ⟨a', μ1, he, F⟩ := chkO_sound hO .mk m rfl
    simp only [evalO, Option.some.injEq, Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    obtain ⟨μ2, hs, hO2⟩ := store_ok (sc' := sc) (x := x) F hsc (fun _ h => h) (fun _ h _ => h)
    have hst : ∀ y, y ≠ x → μ2.st y = μ.st y := fun y hy => place_st hs y hy
    have e : effect μ .inout x (some b) =
        place x (some μ.next) { μ with heap := put μ.heap μ.next true, next := μ.next + 1 } := by
      simp [effect, hx, hb]
    refine ⟨μ2, by rw [e]; exact hs, own_mono (fun y hy => (List.mem_filter.mp hy).1) hO2,
      pins_congr f bs (fun y hy => hst y (fun e => hxf (e ▸ hy))) hP, hst, fun h => by cases h⟩
  | take =>
    have hxf : x ∉ f := hf (by decide)
    have hxp : x ∉ p := hp rfl
    have hc : chkO sc p m (.move x) = some (x :: m) := by simp [chkO, hsc, hm, hxp]
    obtain ⟨a', μ1, he, F⟩ := chkO_sound hO (.move x) (x :: m) hc
    simp only [evalO, hx, Option.some.injEq, Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    refine ⟨_, ?_, fly_free F, ?_, fun y hy => put_ne _ _ hy, fun h => by cases h⟩
    · simp [effect, hb]
    · exact pins_congr f bs (fun y hy => put_ne _ _ (fun e => hxf (e ▸ hy))) hP


theorem chk_soundF : ∀ (n : Nat) (s : FS) (sc p f : List Var) (bs : List Nat) (m : List Var) (o : Exit.Out) (μ : M),
    chkF sc p f s m = some o → Own sc p m μ → Pins μ.st f bs → GoodF sc p f bs o (evalF n bs s μ) := by
  intro n
  induction n with
  | zero =>
    intro s sc p f bs m o μ _ _ _
    simp [evalF, GoodF]
  | succ n ih =>
    intro s sc p f bs m o μ h hO hP
    cases s with
    | skip =>
      simp only [chkF, Option.some.injEq] at h
      subst h
      simp only [evalF, GoodF]
      exact ⟨m, rfl, hO, hP⟩
    | use x =>
      simp only [chkF] at h
      split at h
      · rename_i hc
        simp only [Option.some.injEq] at h
        subst h
        have hu := use_ok hO (hO.full x hc.1 hc.2)
        simp only [evalF, lift, hu, GoodF]
        exact ⟨m, rfl, hO, hP⟩
      · simp at h
    | useB k =>
      simp only [chkF] at h
      split at h
      · rename_i hk
        simp only [Option.some.injEq] at h
        subst h
        obtain ⟨a, y, hn, hy⟩ := pins_nth f bs hP k hk
        have hr : readB bs k μ = some μ := by simp [readB, hn, hO.live y a hy]
        simp only [evalF, lift, hr, GoodF]
        exact ⟨m, rfl, hO, hP⟩
      · simp at h
    | assign x o' =>
      simp only [chkF] at h
      split at h
      · rename_i hc
        obtain ⟨hxs, hxf, hfo⟩ := hc
        cases ho : chkO sc p m o' with
        | none => simp [ho] at h
        | some m1 =>
          simp only [ho, Option.some.injEq] at h
          subst h
          obtain ⟨a, μ1, he, F⟩ := chkO_sound hO o' m1 ho
          obtain ⟨μ2, hs, hO2⟩ := store_ok (sc' := sc) (x := x) F hxs (fun _ h => h) (fun _ h _ => h)
          have hP2 : Pins μ2.st f bs := pins_congr f bs (fun y hy =>
            (place_st hs y (fun e => hxf (e ▸ hy))).trans (evalO_st o' he hfo y hy)) hP
          simp only [evalF, he, lift, hs, GoodF]
          exact ⟨_, rfl, hO2, hP2⟩
      · simp at h
    | seq s t =>
      cases hs : chkF sc p f s m with
      | none => simp [chkF, hs] at h
      | some o1 =>
        have g1 := ih s sc p f bs m o1 μ hs hO hP
        cases hf : o1.fall with
        | none =>
          simp only [chkF, hs, hf, Option.some.injEq] at h
          subst h
          simp only [evalF]
          cases hr : evalF n bs s μ with
          | ok μ' =>
            rw [hr] at g1
            simp [GoodF, hf] at g1
          | brk μ' =>
            rw [hr] at g1
            exact g1
          | cont μ' =>
            rw [hr] at g1
            exact g1
          | ret μ' =>
            rw [hr] at g1
            exact g1
          | err =>
            rw [hr] at g1
            exact g1
          | out => exact trivial
        | some m1 =>
          cases ht : chkF sc p f t m1 with
          | none => simp [chkF, hs, hf, ht] at h
          | some o2 =>
            simp only [chkF, hs, hf, ht, Option.some.injEq] at h
            subst h
            simp only [evalF]
            cases hr : evalF n bs s μ with
            | ok μ' =>
              rw [hr] at g1
              simp only [GoodF] at g1
              obtain ⟨mf, hmf, hi', hp'⟩ := g1
              rw [hf] at hmf
              cases hmf
              have g2 := ih t sc p f bs m1 o2 μ' ht hi' hp'
              exact good_branchF (os := o2) (fun mf h => ⟨mf, h, fun _ hx => hx⟩)
                (fun _ h => List.mem_append_right _ h) (fun _ h => List.mem_append_right _ h)
                (fun _ h => List.mem_append_right _ h) g2
            | brk μ' =>
              rw [hr] at g1
              simp only [GoodF] at g1 ⊢
              obtain ⟨mb, h1, h2, h3⟩ := g1
              exact ⟨mb, List.mem_append_left _ h1, h2, h3⟩
            | cont μ' =>
              rw [hr] at g1
              simp only [GoodF] at g1 ⊢
              obtain ⟨mc, h1, h2, h3⟩ := g1
              exact ⟨mc, List.mem_append_left _ h1, h2, h3⟩
            | ret μ' =>
              rw [hr] at g1
              simp only [GoodF] at g1 ⊢
              obtain ⟨mr, h1, h2, h3⟩ := g1
              exact ⟨mr, List.mem_append_left _ h1, h2, h3⟩
            | err =>
              rw [hr] at g1
              exact g1
            | out => exact trivial
    | ite b s t =>
      cases hs : chkF sc p f s m with
      | none => simp [chkF, hs] at h
      | some os =>
        cases ht : chkF sc p f t m with
        | none => simp [chkF, hs, ht] at h
        | some ot =>
          simp only [chkF, hs, ht, Option.some.injEq] at h
          subst h
          cases b with
          | true =>
            simp only [evalF]
            exact good_branchF (os := os)
              (fun mf h => by
                simp only [h]
                exact joinF_left mf ot.fall)
              (fun _ h => List.mem_append_left _ h) (fun _ h => List.mem_append_left _ h)
              (fun _ h => List.mem_append_left _ h) (ih s sc p f bs m os μ hs hO hP)
          | false =>
            simp only [evalF]
            exact good_branchF (os := ot)
              (fun mf h => by
                simp only [h]
                exact joinF_right os.fall mf)
              (fun _ h => List.mem_append_right _ h) (fun _ h => List.mem_append_right _ h)
              (fun _ h => List.mem_append_right _ h) (ih t sc p f bs m ot μ ht hO hP)
    | brk =>
      simp only [chkF, Option.some.injEq] at h
      subst h
      simp only [evalF, GoodF]
      exact ⟨m, List.mem_singleton.mpr rfl, hO, hP⟩
    | cont =>
      simp only [chkF, Option.some.injEq] at h
      subst h
      simp only [evalF, GoodF]
      exact ⟨m, List.mem_singleton.mpr rfl, hO, hP⟩
    | ret =>
      simp only [chkF, Option.some.injEq] at h
      subst h
      simp only [evalF, GoodF]
      exact ⟨m, List.mem_singleton.mpr rfl, hO, hP⟩
    | loop b =>
      have hloop := h
      cases hb : chkF sc p f b m with
      | none => simp [chkF, hb] at h
      | some ob =>
        simp only [chkF, hb] at h
        split at h
        · rename_i hcond
          simp only [Option.some.injEq] at h
          simp only [Bool.and_eq_true, List.all_eq_true] at hcond
          obtain ⟨hfall, hconts⟩ := hcond
          have g := ih b sc p f bs m ob μ hb hO hP
          simp only [evalF]
          cases hr : evalF n bs b μ with
          | ok μ' =>
            rw [hr] at g
            simp only [GoodF] at g
            obtain ⟨mf, hmf, hi', hp'⟩ := g
            rw [hmf] at hfall
            exact ih (.loop b) sc p f bs m o μ' hloop (own_mono (sub_mem hfall) hi') hp'
          | cont μ' =>
            rw [hr] at g
            simp only [GoodF] at g
            obtain ⟨mc, hmc, hi', hp'⟩ := g
            exact ih (.loop b) sc p f bs m o μ' hloop (own_mono (sub_mem (hconts mc hmc)) hi') hp'
          | brk μ' =>
            rw [hr] at g
            simp only [GoodF] at g
            obtain ⟨mb, hmb, hi', hp'⟩ := g
            subst h
            simp only [GoodF]
            exact ⟨_, rfl, own_mono (fun x hx => List.mem_append_right _ (mem_unionAll hmb hx)) hi', hp'⟩
          | ret μ' =>
            rw [hr] at g
            subst h
            simp only [GoodF] at g ⊢
            exact g
          | err =>
            rw [hr] at g
            exact g
          | out => exact trivial
        · simp at h
    | decl x o' s =>
      simp only [chkF] at h
      split at h
      · rename_i hc
        obtain ⟨hxs, hfo⟩ := hc
        cases ho : chkO sc p m o' with
        | none => simp [ho] at h
        | some m1 =>
          simp only [ho] at h
          cases hc : chkF (x :: sc) p f s (m1.filter (fun y => y != x)) with
          | none => simp [hc] at h
          | some od =>
            simp only [hc, Option.map_some, Option.some.injEq] at h
            subst h
            -- x 不在作用域里，所以是空的；冻结的变量都有值，所以 x 不是冻结的
            have hxf : x ∉ f := fun hx => pins_some f bs hP x hx (hO.out x hxs)
            obtain ⟨a, μ1, he, F⟩ := chkO_sound hO o' m1 ho
            obtain ⟨μ2, hs, hO2⟩ := store_ok (sc' := x :: sc) (x := x) F (by simp) (fun y hy => by simp [hy])
              (fun y hy hyx => by simpa [hyx] using hy)
            have hP2 : Pins μ2.st f bs := pins_congr f bs (fun y hy =>
              (place_st hs y (fun e => hxf (e ▸ hy))).trans (evalO_st o' he hfo y hy)) hP
            have g := ih s (x :: sc) p f bs _ od μ2 hc hO2 hP2
            have hxp : x ∉ p := fun hp => hxs (hO.pin x hp).1
            simp only [evalF, he, hs]
            exact good_hideF hxs hxp hxf g
      · simp at h
    | defer x s =>
      simp only [chkF] at h
      split at h
      · rename_i hc
        have hpin : ∀ y, y ∈ x :: p → y ∈ sc ∧ μ.st y ≠ none := by
          intro y hy
          rcases List.mem_cons.mp hy with e | hy
          · rw [e]
            exact ⟨hc.1, hO.full x hc.1 hc.2⟩
          · exact hO.pin y hy
        have hO' : Own sc (x :: p) m μ := { hO with pin := hpin }
        have g := ih s sc (x :: p) f bs m o μ h hO' hP
        simp only [evalF]
        exact good_finF (fun m' μ' h' hp' => ⟨μ', use_ok h' (h'.pin x (by simp)).2,
          { h' with pin := fun y hy => h'.pin y (by simp [hy]) }, hp'⟩) g
      · simp at h
    | bor x s =>
      simp only [chkF] at h
      split at h
      · rename_i hc
        cases hx : μ.st x with
        | none => exact absurd hx (hO.full x hc.1 hc.2)
        | some a =>
          have g := ih s sc p (x :: f) (a :: bs) m o μ h hO ⟨hx, hP⟩
          simp only [evalF, hx]
          exact good_pop g
      · simp at h
    | call m1 x1 m2 x2 =>
      simp only [chkF] at h
      split at h
      · rename_i hc
        obtain ⟨⟨s1, n1, f1, p1⟩, ⟨s2, n2, f2, p2⟩, hex⟩ := hc
        simp only [Option.some.injEq] at h
        subst h
        obtain ⟨b1, hx1⟩ := ex_some (hO.full x1 s1 n1)
        obtain ⟨b2, hx2⟩ := ex_some (hO.full x2 s2 n2)
        obtain ⟨μ', e1, hO1, hP1, hst1, hid1⟩ := effect_ok hO hP s1 n1 hx1 f1 p1
        -- 第二个参数的地址还有效：不是同一个变量的话第一个参数没碰它；是同一个变量的话两个都是只读的
        have hx2' : μ'.st x2 = some b2 := by
          by_cases hxx : x2 = x1
          · rw [hid1 (hex hxx.symm).1]
            exact hx2
          · rw [hst1 x2 hxx]
            exact hx2
        have n2' : x2 ∉ addT x1 m m1 := by
          intro hm
          rcases mem_addT hm with ⟨ht, e⟩ | hm
          · have := (hex e.symm).1
            rw [ht] at this
            cases this
          · exact n2 hm
        obtain ⟨μ'', e2, hO2, hP2, -, -⟩ := effect_ok hO1 hP1 s2 n2' hx2' f2 p2
        simp only [evalF, hx1, e1, lift, hx2, e2, GoodF]
        exact ⟨_, rfl, hO2, hP2⟩
      · simp at h

theorem good_okF {sc p f : List Var} {bs : List Nat} {o : Exit.Out} {r : Res} (g : GoodF sc p f bs o r) :
    r.isErr = false ∧ ∀ μ, r.state = some μ → ∃ m, Own sc p m μ := by
  cases r with
  | ok μ =>
    simp only [GoodF] at g
    obtain ⟨mf, -, h, -⟩ := g
    refine ⟨rfl, fun μ' e => ?_⟩
    simp only [Res.state, Option.some.injEq] at e
    exact ⟨mf, e ▸ h⟩
  | brk μ =>
    simp only [GoodF] at g
    obtain ⟨mb, -, h, -⟩ := g
    refine ⟨rfl, fun μ' e => ?_⟩
    simp only [Res.state, Option.some.injEq] at e
    exact ⟨mb, e ▸ h⟩
  | cont μ =>
    simp only [GoodF] at g
    obtain ⟨mc, -, h, -⟩ := g
    refine ⟨rfl, fun μ' e => ?_⟩
    simp only [Res.state, Option.some.injEq] at e
    exact ⟨mc, e ▸ h⟩
  | ret μ =>
    simp only [GoodF] at g
    obtain ⟨mr, -, h, -⟩ := g
    refine ⟨rfl, fun μ' e => ?_⟩
    simp only [Res.state, Option.some.injEq] at e
    exact ⟨mr, e ▸ h⟩
  | err =>
    simp only [GoodF] at g
  | out => exact ⟨rfl, fun μ e => by simp [Res.state] at e⟩

/-- 定理：通过检查的程序（有作用域、defer、跳出和借用），给多少燃料都不会出错
    （读到空位或释放了的盒子，包括经由借用读；重复释放；defer 读不到值）；离开最外层时堆是空的 -/
theorem full_sound (n : Nat) (s : FS) (o : Exit.Out) (h : chkF [] [] [] s [] = some o) :
    (evalF n [] s start).isErr = false ∧
    ∀ μ, (evalF n [] s start).state = some μ → ∀ a, μ.heap a = false := by
  obtain ⟨h1, h2⟩ := good_okF (chk_soundF n s [] [] [] [] [] o start h own_start trivial)
  refine ⟨h1, fun μ e a => ?_⟩
  obtain ⟨m, hO⟩ := h2 μ e
  cases ha : μ.heap a with
  | false => rfl
  | true =>
    obtain ⟨x, hx⟩ := hO.noleak a ha
    rw [hO.out x (by simp)] at hx
    cases hx

/-! ## 闭包：写成上面这些语句的组合，所以 full_sound 直接适用，不用另外证

闭包体执行时，捕获的变量是借来的（Lark 按只读捕获）：写成 bor，体里经由借用读（useB 0），
体里移走捕获的值写成 decl w (move x) skip（放进局部变量 w，体结束时释放）。借用期间 x 冻结，所以检查拒绝移走（R18）。
闭包可能被调用任意多次，也可能一次都不调用：用 ite true 运行 k 次、另一边放一份体，
这样 k = 0 时体也照样被检查（检查看 if 的两边）。 -/

def rep (s : FS) : Nat → FS
  | 0 => .skip
  | k + 1 => .seq s (rep s k)

/-- 闭包体：rd 经由借用读捕获的 x，mv 把 x 移进局部变量 w -/
def bodyOn (x w : Var) : List Clo.BI → FS
  | [] => .skip
  | .rd :: b => .seq (.useB 0) (bodyOn x w b)
  | .mv :: b => .seq (.decl w (.move x) .skip) (bodyOn x w b)

/-- 借来的闭包（fn 参数）：被调用的函数调用它 k 次，调用期间捕获的 x 是借来的 -/
def applyF (x w : Var) (b : List Clo.BI) (k : Nat) : FS :=
  .bor x (.ite true (rep (bodyOn x w b) k) (bodyOn x w b))

/-- Fn 闭包：创建时经由借用读 x、复制一份（新盒子 c），之后和局部变量一样，离开作用域时释放 -/
def declFn (c x : Var) (s : FS) : FS :=
  .seq (.bor x (.useB 0)) (.decl c .mk s)

/-- 调用 Fn 闭包：体读的是闭包自己的副本 c -/
def callFn (c w : Var) (b : List Clo.BI) : FS :=
  .bor c (.ite true (bodyOn c w b) (bodyOn c w b))

-- 借来的闭包移走捕获的值：调用 2 次、0 次都不通过（R18）；不检查的话调用 2 次第二次读到空位
example : chkF [] [] [] (.decl 0 .mk (applyF 0 9 [.mv, .rd] 2)) [] = none := by decide
example : chkF [] [] [] (.decl 0 .mk (applyF 0 9 [.mv] 0)) [] = none := by decide
example : (evalF 30 [] (.decl 0 .mk (applyF 0 9 [.mv, .rd] 2)) start).isErr = true := by decide
-- 只读的借来闭包调用 3 次：通过
example : (chkF [] [] [] (.decl 0 .mk (applyF 0 9 [.rd, .rd] 3)) []).isSome = true := by decide

/-- x0 = box；f1 = Fn 闭包（复制 x0）；x2 = x0（移走原来的）；调用 f1 两次：读的是副本 -/
def outlive : FS := .decl 0 .mk (declFn 1 0 (.decl 2 (.move 0) (.seq (callFn 1 9 [.rd]) (callFn 1 9 [.rd]))))

def allFree3 (r : Res) : Bool :=
  match r with
  | .ok μ => !μ.heap 0 && !μ.heap 1 && !μ.heap 2
  | _ => false

example : (chkF [] [] [] outlive []).isSome = true := by decide
example : allFree3 (evalF 30 [] outlive start) = true := by decide
-- Fn 闭包的体移走副本：不通过
example : chkF [] [] [] (.decl 0 .mk (declFn 1 0 (callFn 1 9 [.mv]))) [] = none := by decide

/-- 交叉：defer 用到 x0；循环里借来的闭包读 x0、调用 f(&x1, x0)；return -/
def mixed : FS :=
  .decl 0 .mk (.decl 1 .mk (.defer 0 (.loop (.seq (applyF 0 9 [.rd] 2) (.seq (.call .inout 1 .read 0) .ret)))))

example : (chkF [] [] [] mixed []).isSome = true := by decide
example : (evalF 40 [] mixed start).isErr = false := by decide

/-! ## 例子 -/

/-- x0 = box；借用 x0 { x0 = box；读借来的 } -/
def reassign : FS := .decl 0 .mk (.bor 0 (.seq (.assign 0 .mk) (.useB 0)))

-- 检查不通过：借用期间 x0 冻结（R16）；不检查的话，重新赋值释放了借出去的盒子，再经由借用读就读到释放了的值
example : chkF [] [] [] reassign [] = none := by decide
example : (evalF 10 [] reassign start).isErr = true := by decide
-- 借用期间移走：不通过
example : chkF [] [] [] (.decl 0 .mk (.decl 1 .mk (.bor 0 (.assign 1 (.move 0))))) [] = none := by decide

/-- x0 = box；defer { 读 x0 }；loop { 借用 x0 { x1 = box；读借来的；return } }：从借用、循环、两层作用域里 return -/
def cross : FS := .decl 0 .mk (.defer 0 (.loop (.bor 0 (.decl 1 .mk (.seq (.useB 0) .ret)))))

def allFreed (r : Res) : Bool :=
  match r with
  | .ret μ => !μ.heap 0 && !μ.heap 1
  | _ => false

example : (chkF [] [] [] cross []).isSome = true := by decide
example : allFreed (evalF 20 [] cross start) = true := by decide

-- 借用期间只读地传冻结的变量：可以；inout 传：不行
example : (chkF [] [] [] (.decl 0 .mk (.bor 0 (.call .read 0 .read 0))) []).isSome = true := by decide
example : chkF [] [] [] (.decl 0 .mk (.decl 1 .mk (.bor 0 (.call .inout 0 .read 1)))) [] = none := by decide
-- defer 钉住的变量不能 take 走
example : chkF [] [] [] (.decl 0 .mk (.decl 1 .mk (.defer 0 (.call .take 0 .read 1)))) [] = none := by decide

/-- f(take v, v)、f(&v, v)：排他性不检查的话，前一个参数释放了盒子，后一个参数的地址就失效了 -/
example : chkF [] [] [] (.decl 0 .mk (.call .take 0 .read 0)) [] = none := by decide
example : (evalF 10 [] (.decl 0 .mk (.call .take 0 .read 0)) start).isErr = true := by decide
example : chkF [] [] [] (.decl 0 .mk (.call .inout 0 .read 0)) [] = none := by decide
example : (evalF 10 [] (.decl 0 .mk (.call .inout 0 .read 0)) start).isErr = true := by decide

/-- x0、x1 = box；f(&x0, take x1)；离开时两个作用域都释放 -/
def callOk : FS := .decl 0 .mk (.decl 1 .mk (.call .inout 0 .take 1))

def heapEmpty (r : Res) : Bool :=
  match r with
  | .ok μ => !μ.heap 0 && !μ.heap 1 && !μ.heap 2
  | _ => false

example : (chkF [] [] [] callOk []).isSome = true := by decide
example : heapEmpty (evalF 10 [] callOk start) = true := by decide

end Full
end Lark
