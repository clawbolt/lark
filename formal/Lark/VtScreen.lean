/-
apps/lterm 的证明 · 阶段 3：屏幕
先证明，再写 apps/lterm/vt/screen.lark。

屏幕是 R 行 × C 列的格子。格子里是普通字符（ch）、宽字符的左半（wide）或者右半（spacer）。
光标在 (x, y)；pend 是 “写满了最后一列、下一个字要先换行” 的标记（DEC 的自动换行）；
滚动区域是 [top, bot] 这几行（DECSTBM），换行到 bot 时只滚动这几行。
解析器的动作（VtParse）在 Lark 里换成这里的 Op（CSI 的参数原样传进来，0 表示默认值）。

每一行改完都经过 rowFix：先补齐或截断成正好 C 格（fit），再把拆散了的宽字符的另一半换成空格（heal）。

证明了：
- `step_ok`、`run_ok`：任何操作、任何操作序列以后屏幕都是好的（Ok）：正好 R 行、每行正好 C 格、
  宽字符不会只剩一半（wf）、光标在屏幕里（x < C、y < R）、滚动区域 top ≤ bot < R；`init_ok`：一开始就是好的；
- `heal_wf`、`heal_len`：heal 以后宽字符都是完整的、长度不变；
- `up_outside`、`down_outside`：滚动只动区域里的行，区域外面的行原样不动。
例子（#guard）里检查了：写字、自动换行和 pend、滚动、宽字符被覆盖一半、宽字符写不下时换行、
擦除（EL、ED）、插入删除字符（ICH、DCH）、滚动区域（DECSTBM + SU）、移动光标（CUP）。
没做（以后的阶段）：样式（SGR）、模式（DECSET）、备用屏幕、滚动缓冲、改大小；组合字符（宽度 0）直接丢掉。
-/
import Lark.Lsp

namespace Lark
namespace VtScreen

inductive Cell
  | ch (c : Nat)       -- 普通字符
  | wide (c : Nat)     -- 宽字符的左半
  | spacer             -- 宽字符的右半
deriving DecidableEq, Repr

def blank : Cell := .ch 32

structure S where
  rows : List (List Cell)
  R : Nat
  C : Nat
  x : Nat
  y : Nat
  pend : Bool
  top : Nat
  bot : Nat

/-! ## 一行：补齐、修补宽字符 -/

/-- 正好 n 格：多的截掉，少的补空格 -/
def fit : Nat → List Cell → List Cell
  | 0, _ => []
  | n + 1, [] => blank :: fit n []
  | n + 1, c :: r => c :: fit n r

/-- 宽字符都是完整的：wide 后面紧跟 spacer，spacer 前面紧挨 wide -/
def wf : List Cell → Bool
  | [] => true
  | .ch _ :: r => wf r
  | .spacer :: _ => false
  | .wide _ :: r =>
    match r with
    | .spacer :: r' => wf r'
    | _ => false

/-- 拆散了的宽字符：剩下的那一半换成空格。p 是前一格的宽字符左半（还没看到它的右半），每步只看一格 -/
def heal' : Option Nat → List Cell → List Cell
  | none, [] => []
  | some _, [] => [blank]
  | none, .ch c :: r => .ch c :: heal' none r
  | none, .spacer :: r => blank :: heal' none r
  | none, .wide c :: r => heal' (some c) r
  | some c, .spacer :: r => .wide c :: .spacer :: heal' none r
  | some _, .ch d :: r => blank :: .ch d :: heal' none r
  | some _, .wide d :: r => blank :: heal' (some d) r

def heal (l : List Cell) : List Cell := heal' none l

def rowFix (C : Nat) (l : List Cell) : List Cell := heal (fit C l)
def blankRow (C : Nat) : List Cell := rowFix C []

abbrev RowOk (C : Nat) (r : List Cell) : Prop := r.length = C ∧ wf r = true

/-- 第 i 个开始的格子换成 v（超出时不变） -/
def setAt : List Cell → Nat → Cell → List Cell
  | [], _, _ => []
  | _ :: r, 0, v => v :: r
  | a :: r, n + 1, v => a :: setAt r n v

/-- [a, b) 里的格子换成空格；i 是这一格的下标 -/
def fillR : List Cell → Nat → Nat → Nat → List Cell
  | [], _, _, _ => []
  | c :: r, i, a, b => (if a ≤ i ∧ i < b then blank else c) :: fillR r (i + 1) a b

/-- 在 x 插入 n 个空格（后面的往右挤，挤出去的丢掉：rowFix 截断） -/
def insR (r : List Cell) (x n : Nat) : List Cell := r.take x ++ List.replicate n blank ++ r.drop x

/-- 删掉 x 开始的 n 格（后面的往左移，右边补空格：rowFix 补齐） -/
def dchR (r : List Cell) (x n : Nat) : List Cell := r.take x ++ r.drop (x + n)

def writeRow (r : List Cell) (x c w : Nat) : List Cell :=
  if w = 2 then setAt (setAt r x (.wide c)) (x + 1) .spacer else setAt r x (.ch c)

/-! ## 整个屏幕 -/

def getAt : List (List Cell) → Nat → List Cell
  | [], _ => []
  | a :: _, 0 => a
  | _ :: r, n + 1 => getAt r n

/-- 第 k、k+1、… 行（共 n 行）是 g k、g (k+1)、… -/
def buildF (g : Nat → List Cell) : Nat → Nat → List (List Cell)
  | 0, _ => []
  | n + 1, k => g k :: buildF g n (k + 1)

def withRows (s : S) (g : Nat → List Cell) : S := { s with rows := buildF g s.R 0 }
def moveTo (s : S) (x y : Nat) (p : Bool) : S := { s with x := x, y := y, pend := p }

/-- 放进 [0, n)：太大时是 n - 1 -/
def lim (n v : Nat) : Nat := if v < n then v else n - 1

/-- CSI 的参数：0（省略）表示 1 -/
def one (n : Nat) : Nat := if n = 0 then 1 else n

/-- 区间 [a, b] 里的行往上移 n 行，下面空出来的是空行 -/
def upRows (s : S) (a b n : Nat) (i : Nat) : List Cell :=
  if a ≤ i ∧ i ≤ b then (if i + n ≤ b then getAt s.rows (i + n) else blankRow s.C) else getAt s.rows i

/-- 区间 [a, b] 里的行往下移 n 行，上面空出来的是空行 -/
def downRows (s : S) (a b n : Nat) (i : Nat) : List Cell :=
  if a ≤ i ∧ i ≤ b then (if a + n ≤ i then getAt s.rows (i - n) else blankRow s.C) else getAt s.rows i

def scrollUp (s : S) (a b n : Nat) : S := withRows s (upRows s a b n)
def scrollDown (s : S) (a b n : Nat) : S := withRows s (downRows s a b n)

/-- 换行（LF / IND）：在区域的最后一行时滚动区域，否则下移一行（到屏幕底就不动） -/
def lf (s : S) : S :=
  if s.y = s.bot then moveTo (scrollUp s s.top s.bot 1) s.x s.y false
  else moveTo s s.x (lim s.R (s.y + 1)) false

/-- 反向换行（RI）：在区域的第一行时往下滚动区域，否则上移一行 -/
def ri (s : S) : S :=
  if s.y = s.top then moveTo (scrollDown s s.top s.bot 1) s.x s.y false
  else moveTo s s.x (s.y - 1) false

/-- 改光标所在的一行 -/
def modRow (s : S) (f : List Cell → List Cell) : S :=
  withRows s (fun i => if i = s.y then rowFix s.C (f (getAt s.rows i)) else getAt s.rows i)

/-- 上一个字写满了最后一列：先回到行首、换行 -/
def wrapIf (s : S) : S := if s.pend then lf (moveTo s 0 s.y false) else s

/-- 宽字符在最后一列写不下：先换行 -/
def wideWrap (s : S) (w : Nat) : S :=
  if w = 2 ∧ s.C ≤ s.x + 1 ∧ 2 ≤ s.C then lf (moveTo s 0 s.y false) else s

def put (s : S) (c w : Nat) : S :=
  if s.x + w < s.C then moveTo (modRow s (fun r => writeRow r s.x c w)) (s.x + w) s.y false
  else moveTo (modRow s (fun r => writeRow r s.x c w)) (s.C - 1) s.y true

/-- 写一个字符，w 是它的宽度：0（组合字符）丢掉；宽字符在只有一列的屏幕上写不下，也丢掉 -/
def print (s : S) (c w : Nat) : S :=
  if w = 0 ∨ (w = 2 ∧ s.C < 2) then s else put (wideWrap (wrapIf s) w) c w

/-- EL 的范围：0 光标到行尾、1 行首到光标、2 整行 -/
def elRows (s : S) (m : Nat) (i : Nat) : List Cell :=
  if m = 0 ∧ i = s.y then rowFix s.C (fillR (getAt s.rows i) 0 s.x s.C)
  else if m = 1 ∧ i = s.y then rowFix s.C (fillR (getAt s.rows i) 0 0 (s.x + 1))
  else if m = 2 ∧ i = s.y then blankRow s.C
  else getAt s.rows i

/-- ED：0 光标到屏幕末尾、1 屏幕开头到光标、2 整个屏幕 -/
def edRows (s : S) (m : Nat) (i : Nat) : List Cell :=
  if m = 0 then (if i = s.y then elRows s 0 i else if s.y < i then blankRow s.C else getAt s.rows i)
  else if m = 1 then (if i = s.y then elRows s 1 i else if i < s.y then blankRow s.C else getAt s.rows i)
  else if m = 2 then blankRow s.C
  else getAt s.rows i

def bnd (s : S) (b : Nat) : Nat := if b = 0 then s.R - 1 else lim s.R (b - 1)

/-- DECSTBM：参数是从 1 开始的行号，0 是默认（第一行、最后一行）；合法时光标回到左上角 -/
def stbm (s : S) (t b : Nat) : S :=
  if one t - 1 < bnd s b then { moveTo s 0 0 false with top := one t - 1, bot := bnd s b } else s

inductive Op
  | print (c w : Nat)
  | cr | lf | ri | bs | tab
  | cup (r c : Nat) | up (n : Nat) | down (n : Nat) | fwd (n : Nat) | back (n : Nat)
  | ed (m : Nat) | el (m : Nat) | ech (n : Nat) | ich (n : Nat) | dch (n : Nat)
  | il (n : Nat) | dl (n : Nat) | su (n : Nat) | sd (n : Nat) | stbm (t b : Nat)

def step (s : S) : Op → S
  | .print c w => print s c w
  | .cr => moveTo s 0 s.y false
  | .lf => lf s
  | .ri => ri s
  | .bs => moveTo s (s.x - 1) s.y false
  | .tab => moveTo s (lim s.C ((s.x / 8 + 1) * 8)) s.y false
  | .cup r c => moveTo s (lim s.C (one c - 1)) (lim s.R (one r - 1)) false
  | .up n => moveTo s s.x (s.y - one n) false
  | .down n => moveTo s s.x (lim s.R (s.y + one n)) false
  | .fwd n => moveTo s (lim s.C (s.x + one n)) s.y false
  | .back n => moveTo s (s.x - one n) s.y false
  | .ed m => withRows s (edRows s m)
  | .el m => withRows s (elRows s m)
  | .ech n => modRow s (fun r => fillR r 0 s.x (s.x + one n))
  | .ich n => modRow s (fun r => insR r s.x (one n))
  | .dch n => modRow s (fun r => dchR r s.x (one n))
  | .il n => if s.top ≤ s.y ∧ s.y ≤ s.bot then moveTo (scrollDown s s.y s.bot (one n)) 0 s.y false else s
  | .dl n => if s.top ≤ s.y ∧ s.y ≤ s.bot then moveTo (scrollUp s s.y s.bot (one n)) 0 s.y false else s
  | .su n => scrollUp s s.top s.bot (one n)
  | .sd n => scrollDown s s.top s.bot (one n)
  | .stbm t b => stbm s t b

def run (s : S) : List Op → S
  | [] => s
  | o :: r => run (step s o) r

def init (R C : Nat) : S :=
  { rows := buildF (fun _ => blankRow C) R 0, R := R, C := C, x := 0, y := 0, pend := false, top := 0, bot := R - 1 }

/-- 屏幕是好的 -/
abbrev Ok (s : S) : Prop :=
  0 < s.R ∧ 0 < s.C ∧ s.rows.length = s.R ∧ (∀ r ∈ s.rows, RowOk s.C r) ∧
  s.x < s.C ∧ s.y < s.R ∧ s.top ≤ s.bot ∧ s.bot < s.R

/-! ## 一行的性质 -/

theorem fit_len : ∀ (n : Nat) (l : List Cell), (fit n l).length = n
  | 0, _ => rfl
  | n + 1, [] => congrArg (· + 1) (fit_len n [])
  | n + 1, _ :: r => congrArg (· + 1) (fit_len n r)

def pl : Option Nat → Nat
  | none => 0
  | some _ => 1

theorem heal'_len : ∀ (p : Option Nat) (l : List Cell), (heal' p l).length = l.length + pl p
  | none, [] => rfl
  | some _, [] => rfl
  | none, .ch _ :: r => by simp [heal', heal'_len none r, pl]
  | none, .spacer :: r => by simp [heal', heal'_len none r, pl]
  | none, .wide _ :: r => by simp [heal', heal'_len _ r, pl]
  | some _, .spacer :: r => by simp [heal', heal'_len none r, pl]
  | some _, .ch _ :: r => by simp [heal', heal'_len none r, pl]
  | some _, .wide _ :: r => by simp [heal', heal'_len _ r, pl]

theorem heal_len (l : List Cell) : (heal l).length = l.length := heal'_len none l

theorem heal'_wf : ∀ (p : Option Nat) (l : List Cell), wf (heal' p l) = true
  | none, [] => rfl
  | some _, [] => rfl
  | none, .ch _ :: r => heal'_wf none r
  | none, .spacer :: r => heal'_wf none r
  | none, .wide _ :: r => heal'_wf _ r
  | some _, .spacer :: r => heal'_wf none r
  | some _, .ch _ :: r => heal'_wf none r
  | some _, .wide _ :: r => heal'_wf _ r

theorem heal_wf (l : List Cell) : wf (heal l) = true := heal'_wf none l

theorem rowFix_ok {C : Nat} {l : List Cell} : RowOk C (rowFix C l) :=
  ⟨by rw [rowFix, heal_len, fit_len], heal_wf _⟩

theorem ite_ok {C : Nat} {c : Prop} [Decidable c] {a b : List Cell}
    (ha : c → RowOk C a) (hb : ¬c → RowOk C b) : RowOk C (if c then a else b) := by
  by_cases hc : c
  · rw [Lsp.iteT hc]
    exact ha hc
  · rw [Lsp.iteF hc]
    exact hb hc

/-! ## 行的列表 -/

theorem getAt_mem : ∀ (l : List (List Cell)) (n : Nat), n < l.length → getAt l n ∈ l
  | [], _, h => by simp at h
  | _ :: _, 0, _ => by simp [getAt]
  | _ :: r, n + 1, h => by
    simp only [getAt]
    exact List.mem_cons_of_mem _ (getAt_mem r n (by simp at h; omega))

theorem buildF_len {g : Nat → List Cell} : ∀ (n k : Nat), (buildF g n k).length = n
  | 0, _ => rfl
  | n + 1, k => congrArg (· + 1) (buildF_len n (k + 1))

theorem buildF_mem {g : Nat → List Cell} : ∀ (n k : Nat) (r : List Cell),
    r ∈ buildF g n k → ∃ i, k ≤ i ∧ i < k + n ∧ r = g i
  | 0, _, _, h => by simp [buildF] at h
  | n + 1, k, r, h => by
    simp only [buildF, List.mem_cons] at h
    rcases h with h | h
    · exact ⟨k, by omega, by omega, h⟩
    · obtain ⟨i, h1, h2, h3⟩ := buildF_mem n (k + 1) r h
      exact ⟨i, by omega, by omega, h3⟩

theorem buildF_get {g : Nat → List Cell} : ∀ (n k i : Nat), i < n → getAt (buildF g n k) i = g (k + i)
  | 0, _, _, h => absurd h (by omega)
  | n + 1, k, 0, _ => by simp [buildF, getAt]
  | n + 1, k, i + 1, h => by
    simp only [buildF, getAt]
    rw [buildF_get n (k + 1) i (by omega), show k + 1 + i = k + (i + 1) by omega]

/-! ## 屏幕的每个操作都保持 Ok -/

theorem lim_lt {n v : Nat} (h : 0 < n) : lim n v < n := by
  unfold lim
  split <;> omega

theorem old_ok {s : S} (h : Ok s) {j : Nat} (hj : j < s.R) : RowOk s.C (getAt s.rows j) := by
  obtain ⟨_, _, hl, hr, _⟩ := h
  exact hr _ (getAt_mem s.rows j (by omega))

theorem withRows_ok {s : S} (h : Ok s) {g : Nat → List Cell} (hg : ∀ i, i < s.R → RowOk s.C (g i)) :
    Ok (withRows s g) := by
  obtain ⟨hR, hC, _, _, hx, hy, htb, hb⟩ := h
  refine ⟨hR, hC, buildF_len _ _, ?_, hx, hy, htb, hb⟩
  intro r hm
  obtain ⟨i, _, h2, rfl⟩ := buildF_mem s.R 0 r hm
  exact hg i (by omega)

theorem cur_ok {s : S} (h : Ok s) (x y : Nat) (p : Bool) (hx : x < s.C) (hy : y < s.R) :
    Ok (moveTo s x y p) := by
  obtain ⟨hR, hC, hl, hr, _, _, htb, hb⟩ := h
  exact ⟨hR, hC, hl, hr, hx, hy, htb, hb⟩

theorem modRow_ok {s : S} (h : Ok s) (f : List Cell → List Cell) : Ok (modRow s f) :=
  withRows_ok h (fun _ hi => ite_ok (fun _ => rowFix_ok) (fun _ => old_ok h hi))

theorem scrollUp_ok {s : S} (h : Ok s) {a b n : Nat} (hb : b < s.R) : Ok (scrollUp s a b n) := by
  refine withRows_ok h (fun i hi => ?_)
  unfold upRows
  exact ite_ok (fun _ => ite_ok (fun _ => old_ok h (by omega)) (fun _ => rowFix_ok)) (fun _ => old_ok h hi)

theorem scrollDown_ok {s : S} (h : Ok s) {a b n : Nat} (_hb : b < s.R) : Ok (scrollDown s a b n) := by
  refine withRows_ok h (fun i hi => ?_)
  unfold downRows
  exact ite_ok (fun _ => ite_ok (fun _ => old_ok h (by omega)) (fun _ => rowFix_ok)) (fun _ => old_ok h hi)

theorem lf_ok {s : S} (h : Ok s) : Ok (lf s) := by
  obtain ⟨hR, _, _, _, hx, hy, _, hb⟩ := id h
  unfold lf
  split
  · exact cur_ok (scrollUp_ok h hb) s.x s.y false hx hy
  · exact cur_ok h s.x _ false hx (lim_lt hR)

theorem ri_ok {s : S} (h : Ok s) : Ok (ri s) := by
  obtain ⟨_, _, _, _, hx, hy, _, hb⟩ := id h
  unfold ri
  split
  · exact cur_ok (scrollDown_ok h hb) s.x s.y false hx hy
  · exact cur_ok h s.x _ false hx (by omega)

theorem home_ok {s : S} (h : Ok s) : Ok (moveTo s 0 s.y false) := by
  obtain ⟨_, hC, _, _, _, hy, _, _⟩ := id h
  exact cur_ok h 0 s.y false hC hy

theorem wrapIf_ok {s : S} (h : Ok s) : Ok (wrapIf s) := by
  unfold wrapIf
  split
  · exact lf_ok (home_ok h)
  · exact h

theorem wideWrap_ok {s : S} (h : Ok s) (w : Nat) : Ok (wideWrap s w) := by
  unfold wideWrap
  split
  · exact lf_ok (home_ok h)
  · exact h

theorem put_ok {s : S} (h : Ok s) (c w : Nat) : Ok (put s c w) := by
  obtain ⟨_, hC, _, _, _, hy, _, _⟩ := id h
  have hm := modRow_ok h (fun r => writeRow r s.x c w)
  unfold put
  split
  · next hlt => exact cur_ok hm _ _ _ hlt hy
  · exact cur_ok hm _ _ _ (Nat.sub_lt hC Nat.one_pos) hy

theorem print_ok {s : S} (h : Ok s) (c w : Nat) : Ok (print s c w) := by
  unfold print
  split
  · exact h
  · exact put_ok (wideWrap_ok (wrapIf_ok h) w) c w

theorem el_ok {s : S} (h : Ok s) (m : Nat) : ∀ i, i < s.R → RowOk s.C (elRows s m i) := by
  intro i hi
  unfold elRows
  exact ite_ok (fun _ => rowFix_ok) (fun _ => ite_ok (fun _ => rowFix_ok)
    (fun _ => ite_ok (fun _ => rowFix_ok) (fun _ => old_ok h hi)))

theorem ed_ok {s : S} (h : Ok s) (m : Nat) : ∀ i, i < s.R → RowOk s.C (edRows s m i) := by
  intro i hi
  unfold edRows
  exact ite_ok
    (fun _ => ite_ok (fun _ => el_ok h 0 i hi) (fun _ => ite_ok (fun _ => rowFix_ok) (fun _ => old_ok h hi)))
    (fun _ => ite_ok
      (fun _ => ite_ok (fun _ => el_ok h 1 i hi) (fun _ => ite_ok (fun _ => rowFix_ok) (fun _ => old_ok h hi)))
      (fun _ => ite_ok (fun _ => rowFix_ok) (fun _ => old_ok h hi)))

theorem bnd_lt {s : S} (hR : 0 < s.R) (b : Nat) : bnd s b < s.R := by
  unfold bnd
  split
  · omega
  · exact lim_lt hR

theorem stbm_ok {s : S} (h : Ok s) (t b : Nat) : Ok (stbm s t b) := by
  obtain ⟨hR, hC, hl, hr, _, _, _, _⟩ := id h
  unfold stbm
  split
  · next hlt => exact ⟨hR, hC, hl, hr, hC, hR, Nat.le_of_lt hlt, bnd_lt hR b⟩
  · exact h

theorem step_ok (s : S) (op : Op) (h : Ok s) : Ok (step s op) := by
  obtain ⟨hR, hC, _, _, hx, hy, _, hb⟩ := id h
  cases op with
  | print c w => exact print_ok h c w
  | cr => exact cur_ok h 0 s.y false hC hy
  | lf => exact lf_ok h
  | ri => exact ri_ok h
  | bs => exact cur_ok h (s.x - 1) s.y false (by omega) hy
  | tab => exact cur_ok h _ s.y false (lim_lt hC) hy
  | cup r c => exact cur_ok h _ _ false (lim_lt hC) (lim_lt hR)
  | up n => exact cur_ok h s.x (s.y - one n) false hx (by omega)
  | down n => exact cur_ok h s.x _ false hx (lim_lt hR)
  | fwd n => exact cur_ok h _ s.y false (lim_lt hC) hy
  | back n => exact cur_ok h (s.x - one n) s.y false (by omega) hy
  | ed m => exact withRows_ok h (ed_ok h m)
  | el m => exact withRows_ok h (el_ok h m)
  | ech n => exact modRow_ok h _
  | ich n => exact modRow_ok h _
  | dch n => exact modRow_ok h _
  | il n =>
    show Ok (if s.top ≤ s.y ∧ s.y ≤ s.bot then moveTo (scrollDown s s.y s.bot (one n)) 0 s.y false else s)
    split
    · exact cur_ok (scrollDown_ok h hb) 0 s.y false hC hy
    · exact h
  | dl n =>
    show Ok (if s.top ≤ s.y ∧ s.y ≤ s.bot then moveTo (scrollUp s s.y s.bot (one n)) 0 s.y false else s)
    split
    · exact cur_ok (scrollUp_ok h hb) 0 s.y false hC hy
    · exact h
  | su n => exact scrollUp_ok h hb
  | sd n => exact scrollDown_ok h hb
  | stbm t b => exact stbm_ok h t b

theorem run_ok : ∀ (ops : List Op) (s : S), Ok s → Ok (run s ops)
  | [], _, h => h
  | o :: r, s, h => run_ok r (step s o) (step_ok s o h)

theorem init_ok {R C : Nat} (hR : 0 < R) (hC : 0 < C) : Ok (init R C) := by
  refine ⟨hR, hC, buildF_len _ _, ?_, hC, hR, Nat.zero_le _, show R - 1 < R by omega⟩
  intro r hm
  obtain ⟨_, _, _, rfl⟩ := buildF_mem R 0 r hm
  exact rowFix_ok

/-! ## 滚动只动区域里的行 -/

theorem up_outside {s : S} {a b n i : Nat} (hi : i < s.R) (ho : ¬(a ≤ i ∧ i ≤ b)) :
    getAt (scrollUp s a b n).rows i = getAt s.rows i := by
  show getAt (buildF (upRows s a b n) s.R 0) i = getAt s.rows i
  rw [buildF_get _ _ _ hi, Nat.zero_add]
  unfold upRows
  rw [Lsp.iteF ho]

theorem down_outside {s : S} {a b n i : Nat} (hi : i < s.R) (ho : ¬(a ≤ i ∧ i ≤ b)) :
    getAt (scrollDown s a b n).rows i = getAt s.rows i := by
  show getAt (buildF (downRows s a b n) s.R 0) i = getAt s.rows i
  rw [buildF_get _ _ _ hi, Nat.zero_add]
  unfold downRows
  rw [Lsp.iteF ho]

/-! ## 例子 -/

def bs (s : String) : List Nat := s.toList.map Char.toNat

def cellCh : Cell → Nat
  | .ch c => c
  | .wide c => c
  | .spacer => 0

/-- 第 i 行的字符（宽字符的右半是 0） -/
def line (s : S) (i : Nat) : List Nat := (getAt s.rows i).map cellCh

def texts (l : List Nat) : List Op := l.map (fun c => .print c 1)

-- 写字、回车换行；光标在 c 的后面
#guard (fun s => line s 0 == bs "ab   " && line s 1 == bs "c    " && s.x == 1 && s.y == 1)
  (run (init 3 5) (texts (bs "ab") ++ [.cr, .lf] ++ texts (bs "c")))
-- 写满最后一列：光标停在最后一列、pend；下一个字先换行
#guard (fun s => s.x == 2 && s.y == 0 && s.pend) (run (init 2 3) (texts (bs "abc")))
#guard (fun s => line s 0 == bs "abc" && line s 1 == bs "d  " && s.x == 1 && s.y == 1)
  (run (init 2 3) (texts (bs "abcd")))
-- 在最后一行换行：整个屏幕往上滚一行
#guard (fun s => line s 0 == bs "b  " && line s 1 == bs "c  ")
  (run (init 2 3) (texts (bs "a") ++ [.cr, .lf] ++ texts (bs "b") ++ [.cr, .lf] ++ texts (bs "c")))
-- 宽字符占两格；覆盖了它的右半，左半变成空格
#guard (fun s => line s 0 == [20013, 0, 32, 32] && s.x == 2) (run (init 1 4) [.print 20013 2])
#guard (fun s => line s 0 == [32, 120, 32, 32]) (run (init 1 4) [.print 20013 2, .cr, .fwd 1, .print 120 1])
-- 宽字符在最后一列写不下：换到下一行
#guard (fun s => line s 0 == bs "ab " && line s 1 == [20013, 0, 32] && s.x == 2 && s.y == 1)
  (run (init 2 3) (texts (bs "ab") ++ [.print 20013 2]))
-- EL 0：光标到行尾；ED 2：整个屏幕
#guard (fun s => line s 0 == bs "ab   ") (run (init 1 5) (texts (bs "abcde") ++ [.back 2, .el 0]))
#guard (fun s => line s 0 == bs "   " && line s 1 == bs "   ") (run (init 2 3) (texts (bs "abcd") ++ [.ed 2]))
-- ICH：插入两个空格，挤出去的丢掉；DCH：删掉两格，右边补空格
#guard (fun s => line s 0 == bs "a  bc") (run (init 1 5) (texts (bs "abc") ++ [.cr, .fwd 1, .ich 2]))
#guard (fun s => line s 0 == bs "ade  ") (run (init 1 5) (texts (bs "abcde") ++ [.cr, .fwd 1, .dch 2]))
-- 滚动区域：第 2、3 行（DECSTBM 2;3）往上滚，第 1、4 行不动
#guard (fun s => line s 0 == bs "1" && line s 1 == bs "3" && line s 2 == bs " " && line s 3 == bs "4")
  (run (init 4 1) (texts (bs "1") ++ [.cr, .lf] ++ texts (bs "2") ++ [.cr, .lf] ++ texts (bs "3") ++
    [.cr, .lf] ++ texts (bs "4") ++ [.stbm 2 3, .su 1]))
-- CUP：从 1 开始的行列；超出屏幕的停在边上
#guard (fun s => s.y == 1 && s.x == 2) (run (init 3 5) [.cup 2 3])
#guard (fun s => s.y == 2 && s.x == 4) (run (init 3 5) [.cup 99 99])

end VtScreen
end Lark
