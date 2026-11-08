/-
Lark 可靠性证明 · 第三部分：调用、三种参数模式和排他性（design/soundness.md 的规则 R6、R7、R8）

Lark 的代码生成把 read 和 inout 参数都传成指针（指向调用者的变量），take 参数是把值移进被调用的函数。
语言的意思却是“按值”：调用时把实参复制给被调用的函数，返回时把 inout 参数复制回去。两种理解一般一样，
但 f(&v, v) 这样同一个变量既以 inout 又以只读传进去时就不一样了：被调用的函数改 inout 参数，经由只读参数读到的值也跟着变。

这里有两套语义：`callR`（按指针，和生成的 C 一样）和 `callV`（按值复制进出，语言的意思）。
定理 `call_agree`：调用满足排他性（`Excl`，即 own_call 的检查：inout 和 take 的实参的根变量不出现在别的实参里），
被调用的函数不写只读参数（`BodyOk`，即“x 是只读的，不能赋值”），两套语义得到的调用者的存储完全一样。
推论：只读借用在调用期间看到的值不变，inout 借用期间没有别的路径读写同一个变量（soundness.md 第 1 节的第 3、4 条）。

位置只到根变量：own.lark 的 R7、R8 也只看根（`root`），所以 f(&a.x, a.y) 在这里和实现里一样算重叠。
-/
import Lark.Core

namespace Lark

inductive Mode where
  | read
  | inout
  | take
  deriving DecidableEq, Repr

/-- 被调用的函数里的表达式：rd i 读第 i 个参数 -/
inductive PE where
  | num (k : Int)
  | rd (i : Nat)
  | add (a b : PE)
  deriving Repr

/-- 被调用的函数的函数体：write i e 给第 i 个参数赋值 -/
inductive Body where
  | skip
  | write (i : Nat) (e : PE)
  | seq (s t : Body)
  | ite (c : PE) (s t : Body)
  deriving Repr

def PE.eval (f : Nat → Val) : PE → Int
  | .num k => k
  | .rd i => (f i).toInt
  | .add a b => a.eval f + b.eval f

/-- 一次调用：n 个实参，第 i 个的模式和它的根变量（调用者的哪个变量） -/
structure Call where
  n : Nat
  mode : Nat → Mode
  loc : Nat → Var

/-! ## 按值的语义（语言的意思）：参数放在被调用的函数自己的帧里 -/

def updN (φ : Nat → Val) (i : Nat) (v : Val) : Nat → Val := fun j => if j = i then v else φ j

def execV : Body → (Nat → Val) → (Nat → Val)
  | .skip, φ => φ
  | .write i e, φ => updN φ i (.int (e.eval φ))
  | .seq s t, φ => execV t (execV s φ)
  | .ite c s t, φ => if c.eval φ = 0 then execV t φ else execV s φ

/-! ## 按指针的语义（生成的 C）：read、inout 参数是调用者的变量的地址，take 参数在被调用的函数的帧里 -/

inductive Addr where
  | caller (x : Var)
  | frame (i : Nat)
  deriving DecidableEq

def updA (μ : Addr → Val) (a : Addr) (v : Val) : Addr → Val := fun b => if b = a then v else μ b

def execR (addr : Nat → Addr) : Body → (Addr → Val) → (Addr → Val)
  | .skip, μ => μ
  | .write i e, μ => updA μ (addr i) (.int (e.eval (fun j => μ (addr j))))
  | .seq s t, μ => execR addr t (execR addr s μ)
  | .ite c s t, μ => if c.eval (fun j => μ (addr j)) = 0 then execR addr t μ else execR addr s μ

def Call.addr (k : Call) (i : Nat) : Addr := if k.mode i = .take then .frame i else .caller (k.loc i)

/-! ## 调用前后：take 的实参移走（调用者那边变成空位），返回后 inout 的参数复制回去 -/

def moveOut (k : Call) : Nat → Store → Store
  | 0, σ => σ
  | j + 1, σ => if k.mode j = .take then upd (moveOut k j σ) (k.loc j) .bot else moveOut k j σ

def copyOut (k : Call) : Nat → (Nat → Val) → Store → Store
  | 0, _, σ => σ
  | j + 1, φ, σ => fun x => if k.mode j = .inout ∧ k.loc j = x then φ j else copyOut k j φ σ x

def initMem (k : Call) (σ : Store) : Addr → Val
  | .caller x => moveOut k k.n σ x
  | .frame i => σ (k.loc i)

/-- 按指针：被调用的函数直接读写调用者的变量 -/
def callR (k : Call) (b : Body) (σ : Store) : Store :=
  fun x => execR k.addr b (initMem k σ) (.caller x)

/-- 按值：复制进去，运行，再把 inout 参数复制回来 -/
def callV (k : Call) (b : Body) (σ : Store) : Store :=
  copyOut k k.n (execV b (fun i => σ (k.loc i))) (moveOut k k.n σ)

/-! ## 检查（对应 own.lark 的 own_call 和“x 是只读的”） -/

/-- 排他性（R7、R8）：inout 或 take 的实参的根变量不出现在别的实参里 -/
def Excl (k : Call) : Prop :=
  ∀ i, i < k.n → ∀ j, j < k.n → i ≠ j → k.mode i ≠ .read → k.loc i ≠ k.loc j

instance (k : Call) : Decidable (Excl k) := by
  unfold Excl
  infer_instance

def PEOk (n : Nat) : PE → Prop
  | .num _ => True
  | .rd i => i < n
  | .add a b => PEOk n a ∧ PEOk n b

/-- 被调用的函数只写 inout 和 take 参数（只读参数不能赋值），只用到存在的参数 -/
def BodyOk (k : Call) : Body → Prop
  | .skip => True
  | .write i e => i < k.n ∧ k.mode i ≠ .read ∧ PEOk k.n e
  | .seq s t => BodyOk k s ∧ BodyOk k t
  | .ite c s t => PEOk k.n c ∧ BodyOk k s ∧ BodyOk k t

/-! ## 证明 -/

/-- 排他时，一个能写的参数的地址和别的参数的地址都不同 -/
theorem addr_ne {k : Call} (hx : Excl k) {i j : Nat} (hi : i < k.n) (hj : j < k.n) (hij : i ≠ j)
    (hm : k.mode i ≠ .read) : k.addr j ≠ k.addr i := by
  intro h
  unfold Call.addr at h
  by_cases hti : k.mode i = .take
  · by_cases htj : k.mode j = .take
    · simp only [hti, htj, ↓reduceIte, Addr.frame.injEq] at h
      exact hij h.symm
    · simp [hti, htj] at h
  · by_cases htj : k.mode j = .take
    · simp [hti, htj] at h
    · simp only [hti, htj, ↓reduceIte, Addr.caller.injEq] at h
      exact hx i hi j hj hij hm h.symm

theorem pe_agree {n : Nat} {f g : Nat → Val} (e : PE) (he : PEOk n e)
    (hfg : ∀ j, j < n → f j = g j) : e.eval f = e.eval g := by
  induction e with
  | num k => rfl
  | rd i =>
    simp only [PEOk] at he
    simp only [PE.eval]
    rw [hfg i he]
  | add a b iha ihb =>
    simp only [PEOk] at he
    simp only [PE.eval]
    rw [iha he.1, ihb he.2]

/-- 两套语义一步步对得上：每个参数在指针语义里的地址上的值等于按值语义的帧里的值（R1），
    不是 inout 实参的调用者的变量保持不变（R2） -/
theorem exec_rel (k : Call) (hx : Excl k) (β : Store) (b : Body) (hb : BodyOk k b) :
    ∀ (μ : Addr → Val) (φ : Nat → Val),
      (∀ j, j < k.n → μ (k.addr j) = φ j) →
      (∀ x, (∀ i, i < k.n → k.mode i = .inout → k.loc i ≠ x) → μ (.caller x) = β x) →
      (∀ j, j < k.n → execR k.addr b μ (k.addr j) = execV b φ j) ∧
      (∀ x, (∀ i, i < k.n → k.mode i = .inout → k.loc i ≠ x) → execR k.addr b μ (.caller x) = β x) := by
  induction b with
  | skip =>
    intro μ φ h1 h2
    exact ⟨h1, h2⟩
  | write i e =>
    intro μ φ h1 h2
    simp only [BodyOk] at hb
    obtain ⟨hi, hm, he⟩ := hb
    have hv : e.eval (fun j => μ (k.addr j)) = e.eval φ := pe_agree e he h1
    constructor
    · intro j hj
      show (if k.addr j = k.addr i then Val.int (e.eval (fun j => μ (k.addr j))) else μ (k.addr j))
        = (if j = i then Val.int (e.eval φ) else φ j)
      by_cases hji : j = i
      · rw [ite_eq_left (congrArg k.addr hji), ite_eq_left hji, hv]
      · rw [ite_eq_right (addr_ne hx hi hj (Ne.symm hji) hm), ite_eq_right hji]
        exact h1 j hj
    · intro x hxin
      show (if Addr.caller x = k.addr i then Val.int (e.eval (fun j => μ (k.addr j))) else μ (.caller x)) = β x
      have hne : Addr.caller x ≠ k.addr i := by
        unfold Call.addr
        by_cases ht : k.mode i = .take
        · simp [ht]
        · have hinout : k.mode i = .inout := by
            cases hmi : k.mode i with
            | read => exact absurd hmi hm
            | inout => rfl
            | take => exact absurd hmi ht
          have hl : k.loc i ≠ x := hxin i hi hinout
          simp only [ht, ↓reduceIte, ne_eq, Addr.caller.injEq]
          exact fun h => hl h.symm
      rw [ite_eq_right hne]
      exact h2 x hxin
  | seq s t ihs iht =>
    intro μ φ h1 h2
    simp only [BodyOk] at hb
    obtain ⟨r1, r2⟩ := ihs hb.1 μ φ h1 h2
    exact iht hb.2 _ _ r1 r2
  | ite c s t ihs iht =>
    intro μ φ h1 h2
    simp only [BodyOk] at hb
    obtain ⟨hc, hs, ht⟩ := hb
    have hv : c.eval (fun j => μ (k.addr j)) = c.eval φ := pe_agree c hc h1
    by_cases h0 : c.eval φ = 0
    · have e1 : execR k.addr (.ite c s t) μ = execR k.addr t μ := by simp [execR, hv, h0]
      have e2 : execV (.ite c s t) φ = execV t φ := by simp [execV, h0]
      rw [e1, e2]
      exact iht ht μ φ h1 h2
    · have e1 : execR k.addr (.ite c s t) μ = execR k.addr s μ := by simp [execR, hv, h0]
      have e2 : execV (.ite c s t) φ = execV s φ := by simp [execV, h0]
      rw [e1, e2]
      exact ihs hs μ φ h1 h2

theorem moveOut_miss (k : Call) (σ : Store) (x : Var) :
    ∀ j, (∀ i, i < j → k.mode i = .take → k.loc i ≠ x) → moveOut k j σ x = σ x := by
  intro j
  induction j with
  | zero => intro _; rfl
  | succ j ih =>
    intro h
    have ih' := ih (fun i hi => h i (Nat.lt_succ_of_lt hi))
    by_cases ht : k.mode j = .take
    · have hl : k.loc j ≠ x := h j (Nat.lt_succ_self j) ht
      have hxl : x ≠ k.loc j := fun e => hl e.symm
      show (if k.mode j = .take then upd (moveOut k j σ) (k.loc j) .bot else moveOut k j σ) x = σ x
      rw [ite_eq_left ht]
      show (if x = k.loc j then Val.bot else moveOut k j σ x) = σ x
      rw [ite_eq_right hxl]
      exact ih'
    · show (if k.mode j = .take then upd (moveOut k j σ) (k.loc j) .bot else moveOut k j σ) x = σ x
      rw [ite_eq_right ht]
      exact ih'

theorem copyOut_miss (k : Call) (φ : Nat → Val) (σ : Store) (x : Var) :
    ∀ j, (∀ i, i < j → k.mode i = .inout → k.loc i ≠ x) → copyOut k j φ σ x = σ x := by
  intro j
  induction j with
  | zero => intro _; rfl
  | succ j ih =>
    intro h
    have hc : ¬(k.mode j = .inout ∧ k.loc j = x) := fun hc => h j (Nat.lt_succ_self j) hc.1 hc.2
    show (if k.mode j = .inout ∧ k.loc j = x then φ j else copyOut k j φ σ x) = σ x
    rw [ite_eq_right hc]
    exact ih (fun i hi => h i (Nat.lt_succ_of_lt hi))

theorem copyOut_hit (k : Call) (hx : Excl k) (φ : Nat → Val) (σ : Store) (x : Var) (i : Nat)
    (hi : i < k.n) (hm : k.mode i = .inout) (hl : k.loc i = x) :
    ∀ j, j ≤ k.n → i < j → copyOut k j φ σ x = φ i := by
  intro j
  induction j with
  | zero => intro _ h; exact absurd h (Nat.not_lt_zero i)
  | succ j ih =>
    intro hjn hij
    show (if k.mode j = .inout ∧ k.loc j = x then φ j else copyOut k j φ σ x) = φ i
    by_cases hc : k.mode j = .inout ∧ k.loc j = x
    · rw [ite_eq_left hc]
      by_cases hji : j = i
      · rw [hji]
      · exfalso
        have hjlt : j < k.n := Nat.lt_of_succ_le hjn
        exact hx i hi j hjlt (Ne.symm hji) (by rw [hm]; decide) (hl.trans hc.2.symm)
    · rw [ite_eq_right hc]
      have hne : i ≠ j := by
        intro e
        subst e
        exact hc ⟨hm, hl⟩
      exact ih (Nat.le_of_succ_le hjn) (Nat.lt_of_le_of_ne (Nat.le_of_lt_succ hij) hne)

/-- 定理：满足排他性、被调用的函数不写只读参数时，按指针传参和按值复制进出的结果一样 -/
theorem call_agree (k : Call) (b : Body) (σ : Store) (hx : Excl k) (hb : BodyOk k b) :
    callR k b σ = callV k b σ := by
  funext x
  have init1 : ∀ j, j < k.n → initMem k σ (k.addr j) = σ (k.loc j) := by
    intro j hj
    unfold Call.addr
    by_cases ht : k.mode j = .take
    · simp [ht, initMem]
    · rw [ite_eq_right ht]
      show moveOut k k.n σ (k.loc j) = σ (k.loc j)
      apply moveOut_miss
      intro i hi hti heq
      have hij : i ≠ j := fun e => ht (e ▸ hti)
      exact hx i hi j hj hij (by rw [hti]; decide) heq
  have init2 : ∀ y, (∀ i, i < k.n → k.mode i = .inout → k.loc i ≠ y) →
      initMem k σ (.caller y) = moveOut k k.n σ y := fun _ _ => rfl
  obtain ⟨r1, r2⟩ := exec_rel k hx (moveOut k k.n σ) b hb (initMem k σ) (fun i => σ (k.loc i)) init1 init2
  show execR k.addr b (initMem k σ) (.caller x)
    = copyOut k k.n (execV b (fun i => σ (k.loc i))) (moveOut k k.n σ) x
  by_cases hin : ∃ i, i < k.n ∧ k.mode i = .inout ∧ k.loc i = x
  · obtain ⟨i, hi, hm, hl⟩ := hin
    rw [copyOut_hit k hx _ _ x i hi hm hl k.n (Nat.le_refl _) hi]
    have ha : k.addr i = .caller x := by
      unfold Call.addr
      simp [hm, hl]
    rw [← ha]
    exact r1 i hi
  · rw [copyOut_miss k _ _ x k.n (fun i hi hm hl => hin ⟨i, hi, hm, hl⟩)]
    exact r2 x (fun i hi hm hl => hin ⟨i, hi, hm, hl⟩)

/-! ## 例子 -/

/-- f(&v, v)：v 既以 inout 又以只读传进去 -/
def aliased : Call := ⟨2, fun i => if i = 0 then .inout else .read, fun _ => 0⟩

/-- 函数体：a = b + 1 两次（a 是 inout 参数，b 是只读参数） -/
def twice : Body := .seq (.write 0 (.add (.rd 1) (.num 1))) (.write 0 (.add (.rd 1) (.num 1)))

-- 检查不通过（own_call：“以 inout 传入的同时又被其它参数使用”）
example : ¬ Excl aliased := by decide
-- 不检查的话两套语义真的不一样：按值是 5 + 1，按指针第二次读到的 b 已经是 6
example : callV aliased twice (fun _ => .int 5) 0 = .int 6 := by decide
example : callR aliased twice (fun _ => .int 5) 0 = .int 7 := by decide
-- f(v, v)：两个只读可以；f(&v, &w)：不同的变量可以；f(v_take, v)：被移走的同时又被使用，不行
example : Excl ⟨2, fun _ => .read, fun _ => 0⟩ := by decide
example : Excl ⟨2, fun _ => .inout, fun i => i⟩ := by decide
example : ¬ Excl ⟨2, fun i => if i = 0 then .take else .read, fun _ => 0⟩ := by decide

end Lark
