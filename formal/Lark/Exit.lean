/-
Lark 可靠性证明 · 第七部分：跳出时的释放和 defer（design/soundness.md 的 R12–R14、R21，代码生成约定 A2、A4）

代码生成（cg_expr.lark 的 drop_scope_at、drop_jump）给每层作用域记一张表：拥有的值和 defer 的体按出现的顺序登记，
离开这层时（正常走完、break、continue、return、?）从后往前执行：释放值、执行 defer。这里把一张表写成嵌套：
- decl x o s：声明局部变量 x = o，然后是这层剩下的 s；不管 s 怎么离开，最后释放 x（x 在 defer 之前声明的话，在 defer 之后释放）
- defer x s：登记 defer { 读 x }，然后是剩下的 s；不管 s 怎么离开，最后执行它
这样“从后往前”就是嵌套的由里到外。? 出错时就是 return 错误值，所有权上和 ret 一样，不单独建模。

检查（own.lark 的 R12–R14、R21）：defer 用到的变量钉住到这层结束，期间不能移走（可以重新赋值，defer 看到的是新值）；
循环的规则和 Loop.lean 一样，return 的状态单独记一份。

定理 `exit_sound`：通过检查的程序，不管从哪里、以什么方式离开，都不会读到空位或释放了的盒子、不会重复释放，
defer 执行时它读的变量有值；程序结束（包括 break、return 到最外面）时堆是空的，即每个值恰好释放一次。
defer 恰好执行一次、同一层按倒序，是语义（也就是 drop_jump 的做法）本身的结构，不需要证。
-/
import Lark.Loop

namespace Lark
namespace Exit

inductive OE where
  | move (y : Var)
  | mk
  deriving Repr

inductive St where
  | skip
  | use (x : Var)
  | assign (x : Var) (o : OE)
  | seq (s t : St)
  | ite (b : Bool) (s t : St)
  | brk
  | cont
  | ret
  | loop (b : St)
  | decl (x : Var) (o : OE) (s : St)
  | defer (x : Var) (s : St)
  deriving Repr

structure M where
  st : Var → Option Nat
  heap : Nat → Bool
  next : Nat

def put {α : Type} (f : Nat → α) (k : Nat) (v : α) : Nat → α := fun j => if j = k then v else f j

def evalO (μ : M) : OE → Option (Nat × M)
  | .move y =>
    match μ.st y with
    | none => none
    | some a => some (a, { μ with st := put μ.st y none })
  | .mk => some (μ.next, { μ with heap := put μ.heap μ.next true, next := μ.next + 1 })

/-- 把 x 换成 v：先释放 x 原来的值（空位什么也不做）。赋值时 v 是新值，离开 decl 时 v 是空位 -/
def place (x : Var) (v : Option Nat) (μ : M) : Option M :=
  match μ.st x with
  | none => some { μ with st := put μ.st x v }
  | some b => if μ.heap b then some { μ with st := put μ.st x v, heap := put μ.heap b false } else none

/-- 读 x：空位或者释放了的盒子是错误 -/
def useVar (x : Var) (μ : M) : Option M :=
  match μ.st x with
  | none => none
  | some b => if μ.heap b then some μ else none

inductive Res where
  | ok (μ : M)
  | brk (μ : M)
  | cont (μ : M)
  | ret (μ : M)
  | err
  | out

def Res.isErr : Res → Bool
  | .err => true
  | _ => false

def Res.state : Res → Option M
  | .ok μ => some μ
  | .brk μ => some μ
  | .cont μ => some μ
  | .ret μ => some μ
  | _ => none

def lift (k : M → Res) (f : M → Option M) (μ : M) : Res :=
  match f μ with
  | none => .err
  | some μ' => k μ'

/-- 离开一层时做 f（释放或者执行 defer），离开的方式不变 -/
def Res.fin (f : M → Option M) : Res → Res
  | .ok μ => lift .ok f μ
  | .brk μ => lift .brk f μ
  | .cont μ => lift .cont f μ
  | .ret μ => lift .ret f μ
  | .err => .err
  | .out => .out

def evalX : Nat → St → M → Res
  | 0, _, _ => .out
  | _ + 1, .skip, μ => .ok μ
  | _ + 1, .use x, μ => lift .ok (useVar x) μ
  | _ + 1, .assign x o, μ =>
    match evalO μ o with
    | none => .err
    | some (a, μ1) => lift .ok (place x (some a)) μ1
  | n + 1, .seq s t, μ =>
    match evalX n s μ with
    | .ok μ' => evalX n t μ'
    | .brk μ' => .brk μ'
    | .cont μ' => .cont μ'
    | .ret μ' => .ret μ'
    | .err => .err
    | .out => .out
  | n + 1, .ite b s t, μ =>
    match b with
    | true => evalX n s μ
    | false => evalX n t μ
  | _ + 1, .brk, μ => .brk μ
  | _ + 1, .cont, μ => .cont μ
  | _ + 1, .ret, μ => .ret μ
  | n + 1, .loop b, μ =>
    match evalX n b μ with
    | .ok μ' => evalX n (.loop b) μ'
    | .cont μ' => evalX n (.loop b) μ'
    | .brk μ' => .ok μ'
    | .ret μ' => .ret μ'
    | .err => .err
    | .out => .out
  | n + 1, .decl x o s, μ =>
    match evalO μ o with
    | none => .err
    | some (a, μ1) =>
      match place x (some a) μ1 with
      | none => .err
      | some μ2 => (evalX n s μ2).fin (place x none)
  | n + 1, .defer x s, μ => (evalX n s μ).fin (useVar x)

/-! ## 检查：sc 是在作用域里的变量，p 是钉住的变量，m 是可能没有值的变量 -/

structure Out where
  fall : Option (List Var)
  brks : List (List Var)
  conts : List (List Var)
  rets : List (List Var)
  deriving DecidableEq, Repr

/-- 离开 x 的作用域：各个出口记的“可能没有值”里去掉 x（x 已经释放了，外面也看不见它）。
    没有这一步的话，循环里声明、又在循环里移走的局部变量会被当成“在循环里被移走、本轮结束前没有重新赋值”（对拍发现的） -/
def Out.hide (x : Var) (o : Out) : Out :=
  ⟨o.fall.map (·.filter (fun y => y != x)), o.brks.map (·.filter (fun y => y != x)),
   o.conts.map (·.filter (fun y => y != x)), o.rets.map (·.filter (fun y => y != x))⟩

def chkO (sc p m : List Var) : OE → Option (List Var)
  | .move y => if y ∈ sc ∧ y ∉ m ∧ y ∉ p then some (y :: m) else none    -- R21：钉住的不能移走
  | .mk => some m

def chk : List Var → List Var → St → List Var → Option Out
  | _, _, .skip, m => some ⟨some m, [], [], []⟩
  | sc, _, .use x, m => if x ∈ sc ∧ x ∉ m then some ⟨some m, [], [], []⟩ else none
  | sc, p, .assign x o, m =>
    if x ∈ sc then
      match chkO sc p m o with
      | none => none
      | some m1 => some ⟨some (m1.filter (fun y => y != x)), [], [], []⟩
    else none
  | sc, p, .seq s t, m =>
    match chk sc p s m with
    | none => none
    | some o1 =>
      match o1.fall with
      | none => some o1
      | some m1 =>
        match chk sc p t m1 with
        | none => none
        | some o2 => some ⟨o2.fall, o1.brks ++ o2.brks, o1.conts ++ o2.conts, o1.rets ++ o2.rets⟩
  | sc, p, .ite _ s t, m =>
    match chk sc p s m, chk sc p t m with
    | some os, some ot =>
      some ⟨joinF os.fall ot.fall, os.brks ++ ot.brks, os.conts ++ ot.conts, os.rets ++ ot.rets⟩
    | _, _ => none
  | _, _, .brk, m => some ⟨none, [m], [], []⟩
  | _, _, .cont, m => some ⟨none, [], [m], []⟩
  | _, _, .ret, m => some ⟨none, [], [], [m]⟩                              -- R14
  | sc, p, .loop b, m =>
    match chk sc p b m with
    | none => none
    | some o =>
      if subF o.fall m && o.conts.all (fun c => sub c m) then                -- R12、R13
        some ⟨some (m ++ o.fall.getD [] ++ unionAll o.brks), [], [], o.rets⟩
      else none
  | sc, p, .decl x o s, m =>
    if x ∉ sc then
      match chkO sc p m o with
      | none => none
      | some m1 => (chk (x :: sc) p s (m1.filter (fun y => y != x))).map (Out.hide x)   -- 离开作用域：x 不再算
    else none
  | sc, p, .defer x s, m => if x ∈ sc ∧ x ∉ m then chk sc (x :: p) s m else none   -- R21

def start : M := ⟨fun _ => none, fun _ => false, 0⟩

/-! ## 不变量

- live、uniq、noleak、fresh：同 Drop.lean（地址都没释放、一个盒子一个主人、没释放的盒子有主人、新地址没人用过）
- out：不在作用域里的变量是空的（离开 decl 时释放了）
- full：作用域里不在 m 里的变量有值
- pin：钉住的变量在作用域里而且有值（defer 执行时读得到） -/

structure Own (sc p m : List Var) (μ : M) : Prop where
  live : ∀ x a, μ.st x = some a → μ.heap a = true
  uniq : ∀ x y a, μ.st x = some a → μ.st y = some a → x = y
  noleak : ∀ a, μ.heap a = true → ∃ x, μ.st x = some a
  fresh : ∀ a, μ.heap a = true → a < μ.next
  out : ∀ x, x ∉ sc → μ.st x = none
  full : ∀ x, x ∈ sc → x ∉ m → μ.st x ≠ none
  pin : ∀ x, x ∈ p → x ∈ sc ∧ μ.st x ≠ none

/-- 算完右边、还没存进去：盒子 a 在路上，没有主人 -/
structure Fly (sc p m : List Var) (a : Nat) (μ : M) : Prop where
  live : ∀ x b, μ.st x = some b → μ.heap b = true
  uniq : ∀ x y b, μ.st x = some b → μ.st y = some b → x = y
  noleak : ∀ b, μ.heap b = true → b = a ∨ ∃ x, μ.st x = some b
  fresh : ∀ b, μ.heap b = true → b < μ.next
  out : ∀ x, x ∉ sc → μ.st x = none
  full : ∀ x, x ∈ sc → x ∉ m → μ.st x ≠ none
  pin : ∀ x, x ∈ p → x ∈ sc ∧ μ.st x ≠ none
  alive : μ.heap a = true
  alone : ∀ y, μ.st y ≠ some a

theorem put_same {α : Type} (f : Nat → α) (k : Nat) (v : α) : put f k v k = v := by simp [put]

theorem put_ne {α : Type} (f : Nat → α) {k j : Nat} (v : α) (h : j ≠ k) : put f k v j = f j := by
  simp [put, h]

theorem own_mono {sc p m m' : List Var} {μ : M} (hs : ∀ x, x ∈ m → x ∈ m') (hO : Own sc p m μ) :
    Own sc p m' μ :=
  { hO with full := fun x hx hm => hO.full x hx (fun h => hm (hs x h)) }

theorem own_start : Own [] [] [] start :=
  ⟨fun _ _ h => by simp [start] at h, fun _ _ _ h => by simp [start] at h,
   fun _ h => by simp [start] at h, fun _ h => by simp [start] at h,
   fun _ _ => rfl, fun _ h => by simp at h, fun _ h => by simp at h⟩

theorem chkO_sound {sc p m : List Var} {μ : M} (hO : Own sc p m μ) :
    ∀ (o : OE) (m1 : List Var), chkO sc p m o = some m1 →
      ∃ a μ1, evalO μ o = some (a, μ1) ∧ Fly sc p m1 a μ1
  | .move y, m1, h => by
    simp only [chkO] at h
    split at h
    · rename_i hc
      obtain ⟨hsc, hm, hp⟩ := hc
      simp only [Option.some.injEq] at h
      subst h
      cases hy : μ.st y with
      | none => exact absurd hy (hO.full y hsc hm)
      | some a =>
        refine ⟨a, { μ with st := put μ.st y none }, by simp [evalO, hy], ?_⟩
        refine ⟨?_, ?_, ?_, hO.fresh, ?_, ?_, ?_, hO.live y a hy, ?_⟩
        · intro z b hz
          by_cases hzy : z = y
          · simp [put, hzy] at hz
          · simp [put, hzy] at hz
            exact hO.live z b hz
        · intro z w b hz hw
          by_cases hzy : z = y
          · simp [put, hzy] at hz
          · by_cases hwy : w = y
            · simp [put, hwy] at hw
            · simp [put, hzy] at hz
              simp [put, hwy] at hw
              exact hO.uniq z w b hz hw
        · intro b hb
          obtain ⟨z, hz⟩ := hO.noleak b hb
          by_cases hzy : z = y
          · left
            rw [hzy, hy] at hz
            exact (Option.some.inj hz).symm
          · right
            exact ⟨z, by simp [put, hzy, hz]⟩
        · intro z hz
          by_cases hzy : z = y
          · simp [put, hzy]
          · show put μ.st y none z = none
            rw [put_ne _ _ hzy]
            exact hO.out z hz
        · intro z hz hzm
          simp only [List.mem_cons, not_or] at hzm
          show put μ.st y none z ≠ none
          rw [put_ne _ _ hzm.1]
          exact hO.full z hz hzm.2
        · intro z hz
          obtain ⟨h1, h2⟩ := hO.pin z hz
          have hzy : z ≠ y := fun e => hp (e ▸ hz)
          refine ⟨h1, ?_⟩
          show put μ.st y none z ≠ none
          rw [put_ne _ _ hzy]
          exact h2
        · intro z hz
          by_cases hzy : z = y
          · simp [put, hzy] at hz
          · simp [put, hzy] at hz
            exact hzy (hO.uniq z y a hz hy)
    · simp at h
  | .mk, m1, h => by
    simp only [chkO, Option.some.injEq] at h
    subst h
    have hfree : μ.heap μ.next = false := by
      cases hh : μ.heap μ.next with
      | false => rfl
      | true => exact absurd (hO.fresh _ hh) (Nat.lt_irrefl _)
    refine ⟨μ.next, { μ with heap := put μ.heap μ.next true, next := μ.next + 1 }, rfl, ?_⟩
    refine ⟨?_, hO.uniq, ?_, ?_, hO.out, hO.full, hO.pin, ?_, ?_⟩
    · intro z b hz
      have hl := hO.live z b hz
      have hb : b ≠ μ.next := fun e => by
        have := hO.fresh b hl
        omega
      show put μ.heap μ.next true b = true
      rw [put_ne _ _ hb]
      exact hl
    · intro b hb
      by_cases hbn : b = μ.next
      · exact Or.inl hbn
      · have hb' : put μ.heap μ.next true b = true := hb
        rw [put_ne _ _ hbn] at hb'
        exact Or.inr (hO.noleak b hb')
    · intro b hb
      show b < μ.next + 1
      by_cases hbn : b = μ.next
      · omega
      · have hb' : put μ.heap μ.next true b = true := hb
        rw [put_ne _ _ hbn] at hb'
        have := hO.fresh b hb'
        omega
    · show put μ.heap μ.next true μ.next = true
      rw [put_same]
    · intro y hy
      have := hO.fresh _ (hO.live y _ hy)
      omega

/-- 释放变量 x 里的值以后：x 空了，只有 x 的盒子被释放 -/
theorem free_char (x : Var) (v : Option Nat) (μ : M) (h : ∀ b, μ.st x = some b → μ.heap b = true) :
    ∃ μ2, place x v μ = some μ2 ∧
      (∀ y, μ2.st y = put μ.st x v y) ∧ μ2.next = μ.next ∧
      ∀ c, (μ2.heap c = true ↔ μ.heap c = true ∧ μ.st x ≠ some c) := by
  cases hx : μ.st x with
  | none => exact ⟨{ μ with st := put μ.st x v }, by simp [place, hx], fun _ => rfl, rfl, fun c => by simp⟩
  | some b =>
    have hb := h b hx
    refine ⟨{ μ with st := put μ.st x v, heap := put μ.heap b false }, by simp [place, hx, hb],
      fun _ => rfl, rfl, ?_⟩
    intro c
    by_cases hcb : c = b
    · rw [hcb]
      simp [put]
    · simp [put, hcb, Ne.symm hcb]

/-- 存进 x（x 原来的值先释放）：sc' 是存完以后的作用域（赋值时不变，decl 时加上 x） -/
theorem store_ok {sc sc' p m1 : List Var} {a : Nat} {μ1 : M} {x : Var} (F : Fly sc p m1 a μ1)
    (hx : x ∈ sc') (hsc : ∀ y, y ∈ sc → y ∈ sc') (hsc' : ∀ y, y ∈ sc' → y ≠ x → y ∈ sc) :
    ∃ μ2, place x (some a) μ1 = some μ2 ∧ Own sc' p (m1.filter (fun y => y != x)) μ2 := by
  obtain ⟨μ2, hs, hst, hnx, hh⟩ := free_char x (some a) μ1 (fun b hb => F.live x b hb)
  refine ⟨μ2, hs, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · intro y c hy
    rw [hst] at hy
    rw [hh]
    by_cases hyx : y = x
    · simp [put, hyx] at hy
      rw [← hy]
      exact ⟨F.alive, F.alone x⟩
    · simp [put, hyx] at hy
      exact ⟨F.live y c hy, fun hxc => hyx (F.uniq y x c hy hxc)⟩
  · intro y z c hy hz
    rw [hst] at hy hz
    by_cases hyx : y = x
    · by_cases hzx : z = x
      · exact hyx.trans hzx.symm
      · simp [put, hyx] at hy
        simp [put, hzx] at hz
        rw [← hy] at hz
        exact absurd hz (F.alone z)
    · by_cases hzx : z = x
      · simp [put, hzx] at hz
        simp [put, hyx] at hy
        rw [← hz] at hy
        exact absurd hy (F.alone y)
      · simp [put, hyx] at hy
        simp [put, hzx] at hz
        exact F.uniq y z c hy hz
  · intro c hc
    rw [hh] at hc
    rcases F.noleak c hc.1 with hca | ⟨z, hz⟩
    · exact ⟨x, by rw [hst]; simp [put, hca]⟩
    · have hzx : z ≠ x := fun e => hc.2 (e ▸ hz)
      exact ⟨z, by rw [hst]; simp [put, hzx, hz]⟩
  · intro c hc
    rw [hh] at hc
    rw [hnx]
    exact F.fresh c hc.1
  · intro y hy
    have hyx : y ≠ x := fun e => hy (e ▸ hx)
    rw [hst, put_ne _ _ hyx]
    exact F.out y (fun h => hy (hsc y h))
  · intro y hy hym
    rw [hst]
    by_cases hyx : y = x
    · simp [put, hyx]
    · have hm1 : y ∉ m1 := fun hm => hym (by simp [List.mem_filter, hm, hyx])
      rw [put_ne _ _ hyx]
      exact F.full y (hsc' y hy hyx) hm1
  · intro y hp
    obtain ⟨h1, h2⟩ := F.pin y hp
    refine ⟨hsc y h1, ?_⟩
    rw [hst]
    by_cases hyx : y = x
    · simp [put, hyx]
    · rw [put_ne _ _ hyx]
      exact h2

/-- 离开 decl x：释放 x，作用域去掉 x -/
theorem drop_ok {sc p m : List Var} {x : Var} {μ : M} (hO : Own (x :: sc) p m μ)
    (hxs : x ∉ sc) (hxp : x ∉ p) : ∃ μ', place x none μ = some μ' ∧ Own sc p m μ' := by
  obtain ⟨μ2, hd, hst, hnx, hh⟩ := free_char x none μ (fun b hb => hO.live x b hb)
  refine ⟨μ2, hd, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · intro y c hy
    rw [hst] at hy
    by_cases hyx : y = x
    · simp [put, hyx] at hy
    · rw [put_ne _ _ hyx] at hy
      rw [hh]
      exact ⟨hO.live y c hy, fun hxc => hyx (hO.uniq y x c hy hxc)⟩
  · intro y z c hy hz
    rw [hst] at hy hz
    by_cases hyx : y = x
    · simp [put, hyx] at hy
    · by_cases hzx : z = x
      · simp [put, hzx] at hz
      · rw [put_ne _ _ hyx] at hy
        rw [put_ne _ _ hzx] at hz
        exact hO.uniq y z c hy hz
  · intro c hc
    rw [hh] at hc
    obtain ⟨z, hz⟩ := hO.noleak c hc.1
    have hzx : z ≠ x := fun e => hc.2 (e ▸ hz)
    exact ⟨z, by rw [hst, put_ne _ _ hzx]; exact hz⟩
  · intro c hc
    rw [hh] at hc
    rw [hnx]
    exact hO.fresh c hc.1
  · intro y hy
    rw [hst]
    by_cases hyx : y = x
    · simp [put, hyx]
    · rw [put_ne _ _ hyx]
      exact hO.out y (by simp [hyx, hy])
  · intro y hy hym
    have hyx : y ≠ x := fun e => hxs (e ▸ hy)
    rw [hst, put_ne _ _ hyx]
    exact hO.full y (by simp [hy]) hym
  · intro y hp
    obtain ⟨h1, h2⟩ := hO.pin y hp
    have hyx : y ≠ x := fun e => hxp (e ▸ hp)
    refine ⟨by simpa [hyx] using h1, ?_⟩
    rw [hst, put_ne _ _ hyx]
    exact h2

/-- 读一个有值的变量：成功，状态不变 -/
theorem use_ok {sc p m : List Var} {x : Var} {μ : M} (hO : Own sc p m μ) (hx : μ.st x ≠ none) :
    useVar x μ = some μ := by
  cases h : μ.st x with
  | none => exact absurd h hx
  | some a => simp [useVar, h, hO.live x a h]

/-! ## 结局和检查结果对得上 -/

def Good (sc p : List Var) (o : Out) : Res → Prop
  | .ok μ => ∃ mf, o.fall = some mf ∧ Own sc p mf μ
  | .brk μ => ∃ mb, mb ∈ o.brks ∧ Own sc p mb μ
  | .cont μ => ∃ mc, mc ∈ o.conts ∧ Own sc p mc μ
  | .ret μ => ∃ mr, mr ∈ o.rets ∧ Own sc p mr μ
  | .err => False
  | .out => True

/-- 离开一层时做 f：f 在每个满足不变量的状态上都成功，而且换成外层的不变量 -/
theorem good_fin {sc p sc' p' : List Var} {o : Out} {f : M → Option M} {r : Res}
    (hf : ∀ m μ, Own sc p m μ → ∃ μ', f μ = some μ' ∧ Own sc' p' m μ') (g : Good sc p o r) :
    Good sc' p' o (r.fin f) := by
  cases r with
  | ok μ =>
    simp only [Good] at g
    obtain ⟨mf, h1, h2⟩ := g
    obtain ⟨μ', e, h3⟩ := hf mf μ h2
    simp only [Res.fin, lift, e, Good]
    exact ⟨mf, h1, h3⟩
  | brk μ =>
    simp only [Good] at g
    obtain ⟨mb, h1, h2⟩ := g
    obtain ⟨μ', e, h3⟩ := hf mb μ h2
    simp only [Res.fin, lift, e, Good]
    exact ⟨mb, h1, h3⟩
  | cont μ =>
    simp only [Good] at g
    obtain ⟨mc, h1, h2⟩ := g
    obtain ⟨μ', e, h3⟩ := hf mc μ h2
    simp only [Res.fin, lift, e, Good]
    exact ⟨mc, h1, h3⟩
  | ret μ =>
    simp only [Good] at g
    obtain ⟨mr, h1, h2⟩ := g
    obtain ⟨μ', e, h3⟩ := hf mr μ h2
    simp only [Res.fin, lift, e, Good]
    exact ⟨mr, h1, h3⟩
  | err => exact g
  | out => trivial

theorem own_hide {sc p m : List Var} {x : Var} {μ : M} (hx : x ∉ sc) (hO : Own sc p m μ) :
    Own sc p (m.filter (fun y => y != x)) μ :=
  { hO with full := fun y hy hym => hO.full y hy (fun hm => hym (by
      have hyx : y ≠ x := fun e => hx (e ▸ hy)
      simp [List.mem_filter, hm, hyx])) }

/-- 离开 decl x：释放 x，作用域去掉 x，各个出口的记录里去掉 x -/
theorem good_hide {sc p : List Var} {x : Var} {o : Out} {r : Res} (hx : x ∉ sc) (hxp : x ∉ p)
    (g : Good (x :: sc) p o r) : Good sc p (o.hide x) (r.fin (place x none)) := by
  cases r with
  | ok μ =>
    simp only [Good] at g
    obtain ⟨mf, h1, h2⟩ := g
    obtain ⟨μ', e, h3⟩ := drop_ok h2 hx hxp
    simp only [Res.fin, lift, e, Good]
    exact ⟨_, by simp [Out.hide, h1], own_hide hx h3⟩
  | brk μ =>
    simp only [Good] at g
    obtain ⟨mb, h1, h2⟩ := g
    obtain ⟨μ', e, h3⟩ := drop_ok h2 hx hxp
    simp only [Res.fin, lift, e, Good]
    exact ⟨_, List.mem_map.mpr ⟨mb, h1, rfl⟩, own_hide hx h3⟩
  | cont μ =>
    simp only [Good] at g
    obtain ⟨mc, h1, h2⟩ := g
    obtain ⟨μ', e, h3⟩ := drop_ok h2 hx hxp
    simp only [Res.fin, lift, e, Good]
    exact ⟨_, List.mem_map.mpr ⟨mc, h1, rfl⟩, own_hide hx h3⟩
  | ret μ =>
    simp only [Good] at g
    obtain ⟨mr, h1, h2⟩ := g
    obtain ⟨μ', e, h3⟩ := drop_ok h2 hx hxp
    simp only [Res.fin, lift, e, Good]
    exact ⟨_, List.mem_map.mpr ⟨mr, h1, rfl⟩, own_hide hx h3⟩
  | err => exact g
  | out => trivial

theorem good_branch {sc p : List Var} {os o : Out} {r : Res}
    (hf : ∀ mf, os.fall = some mf → ∃ mf', o.fall = some mf' ∧ ∀ x, x ∈ mf → x ∈ mf')
    (hb : ∀ mb, mb ∈ os.brks → mb ∈ o.brks)
    (hc : ∀ mc, mc ∈ os.conts → mc ∈ o.conts)
    (hr : ∀ mr, mr ∈ os.rets → mr ∈ o.rets)
    (g : Good sc p os r) : Good sc p o r := by
  cases r with
  | ok μ =>
    simp only [Good] at g ⊢
    obtain ⟨mf, h1, h2⟩ := g
    obtain ⟨mf', h3, h4⟩ := hf mf h1
    exact ⟨mf', h3, own_mono h4 h2⟩
  | brk μ =>
    simp only [Good] at g ⊢
    obtain ⟨mb, h1, h2⟩ := g
    exact ⟨mb, hb mb h1, h2⟩
  | cont μ =>
    simp only [Good] at g ⊢
    obtain ⟨mc, h1, h2⟩ := g
    exact ⟨mc, hc mc h1, h2⟩
  | ret μ =>
    simp only [Good] at g ⊢
    obtain ⟨mr, h1, h2⟩ := g
    exact ⟨mr, hr mr h1, h2⟩
  | err => exact g
  | out => trivial

theorem sub_mem {a m : List Var} (h : sub a m = true) : ∀ x, x ∈ a → x ∈ m := by
  simp only [sub, List.all_eq_true, decide_eq_true_eq] at h
  exact h

theorem chk_sound : ∀ (n : Nat) (s : St) (sc p m : List Var) (o : Out) (μ : M),
    chk sc p s m = some o → Own sc p m μ → Good sc p o (evalX n s μ) := by
  intro n
  induction n with
  | zero =>
    intro s sc p m o μ _ _
    simp [evalX, Good]
  | succ n ih =>
    intro s sc p m o μ h hO
    cases s with
    | skip =>
      simp only [chk, Option.some.injEq] at h
      subst h
      simp only [evalX, Good]
      exact ⟨m, rfl, hO⟩
    | use x =>
      simp only [chk] at h
      split at h
      · rename_i hc
        simp only [Option.some.injEq] at h
        subst h
        have hu := use_ok hO (hO.full x hc.1 hc.2)
        simp only [evalX, lift, hu, Good]
        exact ⟨m, rfl, hO⟩
      · simp at h
    | assign x o' =>
      simp only [chk] at h
      split at h
      · rename_i hc
        cases ho : chkO sc p m o' with
        | none => simp [ho] at h
        | some m1 =>
          simp only [ho, Option.some.injEq] at h
          subst h
          obtain ⟨a, μ1, he, F⟩ := chkO_sound hO o' m1 ho
          obtain ⟨μ2, hs, hO2⟩ := store_ok (sc' := sc) (x := x) F hc (fun _ h => h) (fun _ h _ => h)
          simp only [evalX, he, lift, hs, Good]
          exact ⟨_, rfl, hO2⟩
      · simp at h
    | seq s t =>
      cases hs : chk sc p s m with
      | none => simp [chk, hs] at h
      | some o1 =>
        have g1 := ih s sc p m o1 μ hs hO
        cases hf : o1.fall with
        | none =>
          simp only [chk, hs, hf, Option.some.injEq] at h
          subst h
          simp only [evalX]
          cases hr : evalX n s μ with
          | ok μ' =>
            rw [hr] at g1
            simp [Good, hf] at g1
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
          cases ht : chk sc p t m1 with
          | none => simp [chk, hs, hf, ht] at h
          | some o2 =>
            simp only [chk, hs, hf, ht, Option.some.injEq] at h
            subst h
            simp only [evalX]
            cases hr : evalX n s μ with
            | ok μ' =>
              rw [hr] at g1
              simp only [Good] at g1
              obtain ⟨mf, hmf, hi'⟩ := g1
              rw [hf] at hmf
              cases hmf
              have g2 := ih t sc p m1 o2 μ' ht hi'
              exact good_branch (os := o2) (fun mf h => ⟨mf, h, fun _ hx => hx⟩)
                (fun _ h => List.mem_append_right _ h) (fun _ h => List.mem_append_right _ h)
                (fun _ h => List.mem_append_right _ h) g2
            | brk μ' =>
              rw [hr] at g1
              simp only [Good] at g1 ⊢
              obtain ⟨mb, h1, h2⟩ := g1
              exact ⟨mb, List.mem_append_left _ h1, h2⟩
            | cont μ' =>
              rw [hr] at g1
              simp only [Good] at g1 ⊢
              obtain ⟨mc, h1, h2⟩ := g1
              exact ⟨mc, List.mem_append_left _ h1, h2⟩
            | ret μ' =>
              rw [hr] at g1
              simp only [Good] at g1 ⊢
              obtain ⟨mr, h1, h2⟩ := g1
              exact ⟨mr, List.mem_append_left _ h1, h2⟩
            | err =>
              rw [hr] at g1
              exact g1
            | out => exact trivial
    | ite b s t =>
      cases hs : chk sc p s m with
      | none => simp [chk, hs] at h
      | some os =>
        cases ht : chk sc p t m with
        | none => simp [chk, hs, ht] at h
        | some ot =>
          simp only [chk, hs, ht, Option.some.injEq] at h
          subst h
          cases b with
          | true =>
            simp only [evalX]
            exact good_branch (os := os)
              (fun mf h => by
                simp only [h]
                exact joinF_left mf ot.fall)
              (fun _ h => List.mem_append_left _ h) (fun _ h => List.mem_append_left _ h)
              (fun _ h => List.mem_append_left _ h) (ih s sc p m os μ hs hO)
          | false =>
            simp only [evalX]
            exact good_branch (os := ot)
              (fun mf h => by
                simp only [h]
                exact joinF_right os.fall mf)
              (fun _ h => List.mem_append_right _ h) (fun _ h => List.mem_append_right _ h)
              (fun _ h => List.mem_append_right _ h) (ih t sc p m ot μ ht hO)
    | brk =>
      simp only [chk, Option.some.injEq] at h
      subst h
      simp only [evalX, Good]
      exact ⟨m, List.mem_singleton.mpr rfl, hO⟩
    | cont =>
      simp only [chk, Option.some.injEq] at h
      subst h
      simp only [evalX, Good]
      exact ⟨m, List.mem_singleton.mpr rfl, hO⟩
    | ret =>
      simp only [chk, Option.some.injEq] at h
      subst h
      simp only [evalX, Good]
      exact ⟨m, List.mem_singleton.mpr rfl, hO⟩
    | loop b =>
      have hloop := h
      cases hb : chk sc p b m with
      | none => simp [chk, hb] at h
      | some ob =>
        simp only [chk, hb] at h
        split at h
        · rename_i hcond
          simp only [Option.some.injEq] at h
          simp only [Bool.and_eq_true, List.all_eq_true] at hcond
          obtain ⟨hfall, hconts⟩ := hcond
          have g := ih b sc p m ob μ hb hO
          simp only [evalX]
          cases hr : evalX n b μ with
          | ok μ' =>
            rw [hr] at g
            simp only [Good] at g
            obtain ⟨mf, hmf, hi'⟩ := g
            rw [hmf] at hfall
            exact ih (.loop b) sc p m o μ' hloop (own_mono (sub_mem hfall) hi')
          | cont μ' =>
            rw [hr] at g
            simp only [Good] at g
            obtain ⟨mc, hmc, hi'⟩ := g
            exact ih (.loop b) sc p m o μ' hloop (own_mono (sub_mem (hconts mc hmc)) hi')
          | brk μ' =>
            rw [hr] at g
            simp only [Good] at g
            obtain ⟨mb, hmb, hi'⟩ := g
            subst h
            simp only [Good]
            exact ⟨_, rfl, own_mono (fun x hx => List.mem_append_right _ (mem_unionAll hmb hx)) hi'⟩
          | ret μ' =>
            rw [hr] at g
            subst h
            simp only [Good] at g ⊢
            exact g
          | err =>
            rw [hr] at g
            exact g
          | out => exact trivial
        · simp at h
    | decl x o' s =>
      simp only [chk] at h
      split at h
      · rename_i hxs
        cases ho : chkO sc p m o' with
        | none => simp [ho] at h
        | some m1 =>
          simp only [ho] at h
          cases hc : chk (x :: sc) p s (m1.filter (fun y => y != x)) with
          | none => simp [hc] at h
          | some od =>
            simp only [hc, Option.map_some, Option.some.injEq] at h
            subst h
            obtain ⟨a, μ1, he, F⟩ := chkO_sound hO o' m1 ho
            obtain ⟨μ2, hs, hO2⟩ := store_ok (sc' := x :: sc) (x := x) F (by simp) (fun y hy => by simp [hy])
              (fun y hy hyx => by simpa [hyx] using hy)
            have g := ih s (x :: sc) p _ od μ2 hc hO2
            have hxp : x ∉ p := fun hp => hxs (hO.pin x hp).1
            simp only [evalX, he, hs]
            exact good_hide hxs hxp g
      · simp at h
    | defer x s =>
      simp only [chk] at h
      split at h
      · rename_i hc
        have hpin : ∀ y, y ∈ x :: p → y ∈ sc ∧ μ.st y ≠ none := by
          intro y hy
          rcases List.mem_cons.mp hy with e | hy
          · rw [e]
            exact ⟨hc.1, hO.full x hc.1 hc.2⟩
          · exact hO.pin y hy
        have hO' : Own sc (x :: p) m μ := { hO with pin := hpin }
        have g := ih s sc (x :: p) m o μ h hO'
        simp only [evalX]
        exact good_fin (fun m' μ' h' => ⟨μ', use_ok h' (h'.pin x (by simp)).2,
          { h' with pin := fun y hy => h'.pin y (by simp [hy]) }⟩) g
      · simp at h

theorem good_ok {sc p : List Var} {o : Out} {r : Res} (g : Good sc p o r) :
    r.isErr = false ∧ ∀ μ, r.state = some μ → ∃ m, Own sc p m μ := by
  cases r with
  | ok μ =>
    simp only [Good] at g
    obtain ⟨mf, -, h⟩ := g
    refine ⟨rfl, fun μ' e => ?_⟩
    simp only [Res.state, Option.some.injEq] at e
    exact ⟨mf, e ▸ h⟩
  | brk μ =>
    simp only [Good] at g
    obtain ⟨mb, -, h⟩ := g
    refine ⟨rfl, fun μ' e => ?_⟩
    simp only [Res.state, Option.some.injEq] at e
    exact ⟨mb, e ▸ h⟩
  | cont μ =>
    simp only [Good] at g
    obtain ⟨mc, -, h⟩ := g
    refine ⟨rfl, fun μ' e => ?_⟩
    simp only [Res.state, Option.some.injEq] at e
    exact ⟨mc, e ▸ h⟩
  | ret μ =>
    simp only [Good] at g
    obtain ⟨mr, -, h⟩ := g
    refine ⟨rfl, fun μ' e => ?_⟩
    simp only [Res.state, Option.some.injEq] at e
    exact ⟨mr, e ▸ h⟩
  | err =>
    simp only [Good] at g
  | out => exact ⟨rfl, fun μ e => by simp [Res.state] at e⟩

/-- 定理：通过检查的程序，给多少燃料都不会出错（读到空位或释放了的盒子、重复释放、defer 读不到值）；
    走完或者以 break、continue、return 离开最外层时，堆是空的 -/
theorem exit_sound (n : Nat) (s : St) (o : Out) (h : chk [] [] s [] = some o) :
    (evalX n s start).isErr = false ∧
    ∀ μ, (evalX n s start).state = some μ → ∀ a, μ.heap a = false := by
  obtain ⟨h1, h2⟩ := good_ok (chk_sound n s [] [] [] o start h own_start)
  refine ⟨h1, fun μ e a => ?_⟩
  obtain ⟨m, hO⟩ := h2 μ e
  cases ha : μ.heap a with
  | false => rfl
  | true =>
    obtain ⟨x, hx⟩ := hO.noleak a ha
    rw [hO.out x (by simp)] at hx
    cases hx

/-! ## 例子 -/

/-- x0 = box；x1 = box；defer { 读 x0 }；x1 = x0（把 x0 移走） -/
def pinned : St := .decl 0 .mk (.decl 1 .mk (.defer 0 (.assign 1 (.move 0))))

-- 检查不通过：x0 被 defer 钉住了（R21）
example : chk [] [] pinned [] = none := by decide
-- 不检查的话，defer 执行时读到空位
example : (evalX 10 pinned start).isErr = true := by decide
-- 钉住的变量可以重新赋值
example : chk [] [] (.decl 0 .mk (.defer 0 (.assign 0 .mk))) [] = some ⟨some [], [], [], []⟩ := by decide

/-- x0 = box；loop { x1 = box；loop { return } } -/
def nested : St := .decl 0 .mk (.loop (.decl 1 .mk (.loop .ret)))

def allFreed (r : Res) : Bool :=
  match r with
  | .ret μ => !μ.heap 0 && !μ.heap 1
  | _ => false

-- 从两层循环里 return：检查通过，两个盒子都释放了
example : (chk [] [] nested []).isSome = true := by decide
example : allFreed (evalX 20 nested start) = true := by decide

end Exit
end Lark
