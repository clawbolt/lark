import Lark.Url

/-
标准库的证明 · 语义化版本（std/semver.lark，先证明再写库）

照 semver.org 2.0.0：版本是 主.次.修订[-预发布][+构建]，比较时（第 11 条）：
- 主、次、修订按数字比；都一样时，有预发布的比没有的小；
- 预发布按 . 分成标识符逐个比：都是数字时按数字比，都是字母数字时按 ASCII 比，数字的比字母数字的小；
  前面都一样时，标识符多的大；
- 构建信息不参与比较。

这一块证明比较是全序（`lawV`）：交换两边结果反过来、结果是相等当且仅当（除了构建信息）两个版本一样、
自己和自己相等、小于可以传递。写法是先证明“逐项比”和“按字典序比列表”保持这四条（`lawPair`、`lawList`），
再一层层搭起来。后一块是写出来和解析：合法的版本写出来再解析回到原样（`parse_format`）。
-/

namespace Lark
namespace Semver

/-- 比较函数的四条性质 -/
structure Law {α : Type} (c : α → α → Ordering) : Prop where
  swap : ∀ a b, c b a = (c a b).swap
  eq : ∀ a b, c a b = .eq → a = b
  refl : ∀ a, c a a = .eq
  trans : ∀ a b d, c a b = .lt → c b d = .lt → c a d = .lt

/-! ## 数 -/

def cmpN (a b : Nat) : Ordering := if a < b then .lt else if b < a then .gt else .eq

theorem cmpN_lt (a b : Nat) : cmpN a b = .lt ↔ a < b := by
  by_cases h1 : a < b
  · simp [cmpN, h1]
  · by_cases h2 : b < a <;> simp [cmpN, h1, h2]

theorem cmpN_eq (a b : Nat) : cmpN a b = .eq ↔ a = b := by
  by_cases h1 : a < b <;> by_cases h2 : b < a <;> simp [cmpN, h1, h2] <;> omega

theorem lawN : Law cmpN :=
  ⟨fun a b => by
      by_cases h1 : a < b <;> by_cases h2 : b < a <;> simp [cmpN, h1, h2, Ordering.swap] <;> omega,
    fun a b h => (cmpN_eq a b).1 h,
    fun a => (cmpN_eq a a).2 rfl,
    fun a b d h1 h2 => (cmpN_lt a d).2 (by
      have := (cmpN_lt a b).1 h1
      have := (cmpN_lt b d).1 h2
      omega)⟩

/-! ## 先比前一项，一样时再比后一项 -/

def lex : Ordering → Ordering → Ordering
  | .lt, _ => .lt
  | .eq, o => o
  | .gt, _ => .gt

theorem lex_lt (x y : Ordering) : lex x y = .lt ↔ x = .lt ∨ (x = .eq ∧ y = .lt) := by
  cases x <;> cases y <;> simp [lex]

theorem lex_eq (x y : Ordering) : lex x y = .eq ↔ x = .eq ∧ y = .eq := by
  cases x <;> cases y <;> simp [lex]

theorem lex_swap (x y : Ordering) : lex x.swap y.swap = (lex x y).swap := by
  cases x <;> cases y <;> rfl

def cmpPair {α β : Type} (c1 : α → α → Ordering) (c2 : β → β → Ordering) (a b : α × β) : Ordering :=
  lex (c1 a.1 b.1) (c2 a.2 b.2)

theorem lawPair {α β : Type} {c1 : α → α → Ordering} {c2 : β → β → Ordering} (h1 : Law c1) (h2 : Law c2) :
    Law (cmpPair c1 c2) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro a b
    simp only [cmpPair]
    rw [h1.swap a.1, h2.swap a.2, lex_swap]
  · intro a b h
    simp only [cmpPair] at h
    obtain ⟨e1, e2⟩ := (lex_eq _ _).1 h
    exact Prod.ext (h1.eq _ _ e1) (h2.eq _ _ e2)
  · intro a
    simp [cmpPair, h1.refl, h2.refl, lex]
  · intro a b d hab hbd
    simp only [cmpPair] at hab hbd ⊢
    rw [lex_lt] at hab hbd ⊢
    rcases hab with hab | ⟨e1, hab⟩ <;> rcases hbd with hbd | ⟨e2, hbd⟩
    · exact Or.inl (h1.trans _ _ _ hab hbd)
    · rw [← h1.eq _ _ e2]
      exact Or.inl hab
    · rw [h1.eq _ _ e1]
      exact Or.inl hbd
    · refine Or.inr ⟨?_, h2.trans _ _ _ hab hbd⟩
      rw [h1.eq _ _ e1]
      exact e2

/-! ## 按字典序比列表：前面都一样时短的小 -/

def cmpList {α : Type} (c : α → α → Ordering) : List α → List α → Ordering
  | [], [] => .eq
  | [], _ :: _ => .lt
  | _ :: _, [] => .gt
  | x :: xs, y :: ys => lex (c x y) (cmpList c xs ys)

section
variable {α : Type} {c : α → α → Ordering}

theorem list_swap (h : Law c) : ∀ a b : List α, cmpList c b a = (cmpList c a b).swap
  | [], [] => rfl
  | [], _ :: _ => rfl
  | _ :: _, [] => rfl
  | x :: xs, y :: ys => by
    simp only [cmpList]
    rw [h.swap x y, list_swap h xs ys, lex_swap]

theorem list_eq (h : Law c) : ∀ a b : List α, cmpList c a b = .eq → a = b
  | [], [], _ => rfl
  | [], _ :: _, e => by simp [cmpList] at e
  | _ :: _, [], e => by simp [cmpList] at e
  | x :: xs, y :: ys, e => by
    simp only [cmpList] at e
    obtain ⟨e1, e2⟩ := (lex_eq _ _).1 e
    rw [h.eq _ _ e1, list_eq h xs ys e2]

theorem list_refl (h : Law c) : ∀ a : List α, cmpList c a a = .eq
  | [] => rfl
  | x :: xs => by simp [cmpList, h.refl x, list_refl h xs, lex]

theorem list_trans (h : Law c) : ∀ a b d : List α, cmpList c a b = .lt → cmpList c b d = .lt → cmpList c a d = .lt
  | [], b, d, h1, h2 => by
    cases d with
    | nil =>
      cases b with
      | nil => simp [cmpList] at h1
      | cons _ _ => simp [cmpList] at h2
    | cons _ _ => rfl
  | x :: xs, b, d, h1, h2 => by
    cases b with
    | nil => simp [cmpList] at h1
    | cons y ys =>
      cases d with
      | nil => simp [cmpList] at h2
      | cons z zs =>
        simp only [cmpList] at h1 h2 ⊢
        rw [lex_lt] at h1 h2 ⊢
        rcases h1 with h1 | ⟨e1, h1⟩ <;> rcases h2 with h2 | ⟨e2, h2⟩
        · exact Or.inl (h.trans _ _ _ h1 h2)
        · rw [← h.eq _ _ e2]
          exact Or.inl h1
        · rw [h.eq _ _ e1]
          exact Or.inl h2
        · refine Or.inr ⟨?_, list_trans h xs ys zs h1 h2⟩
          rw [h.eq _ _ e1]
          exact e2

theorem lawList (h : Law c) : Law (cmpList c) := ⟨list_swap h, list_eq h, list_refl h, list_trans h⟩

end

/-! ## 预发布的标识符：数字的比字母数字的小 -/

inductive Id where
  | num (n : Nat)
  | alnum (s : List Nat)
  deriving DecidableEq

def cmpId : Id → Id → Ordering
  | .num a, .num b => cmpN a b
  | .num _, .alnum _ => .lt
  | .alnum _, .num _ => .gt
  | .alnum a, .alnum b => cmpList cmpN a b

theorem lawId : Law cmpId := by
  have hN := lawN
  have hL := lawList lawN
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro a b
    cases a <;> cases b <;> simp only [cmpId] <;> first | contradiction | rfl | exact hN.swap _ _ | exact hL.swap _ _
  · intro a b e
    cases a <;> cases b <;> simp only [cmpId] at e <;>
      first | contradiction | (congr 1; exact hN.eq _ _ e) | (congr 1; exact hL.eq _ _ e)
  · intro a
    cases a <;> simp only [cmpId] <;> first | contradiction | exact hN.refl _ | exact hL.refl _
  · intro a b d h1 h2
    cases a <;> cases b <;> cases d <;> simp only [cmpId] at h1 h2 ⊢ <;>
      first | contradiction | rfl | exact hN.trans _ _ _ h1 h2 | exact hL.trans _ _ _ h1 h2

/-- 预发布：没有的比有的大；都有时按标识符的列表比 -/
def cmpPre : List Id → List Id → Ordering
  | [], [] => .eq
  | [], _ :: _ => .gt
  | _ :: _, [] => .lt
  | x :: xs, y :: ys => cmpList cmpId (x :: xs) (y :: ys)

theorem lawPre : Law cmpPre := by
  have hL := lawList lawId
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro a b
    cases a <;> cases b <;> simp only [cmpPre] <;> first | contradiction | rfl | exact hL.swap _ _
  · intro a b e
    cases a <;> cases b <;> simp only [cmpPre] at e <;> first | contradiction | rfl | exact hL.eq _ _ e
  · intro a
    cases a <;> simp only [cmpPre] <;> exact hL.refl _
  · intro a b d h1 h2
    cases a <;> cases b <;> cases d <;> simp only [cmpPre] at h1 h2 ⊢ <;>
      first | contradiction | rfl | exact hL.trans _ _ _ h1 h2

/-! ## 版本 -/

structure V where
  major : Nat
  minor : Nat
  patch : Nat
  pre : List Id
  build : List (List Nat)

/-- 参与比较的部分（构建信息不算） -/
def key (v : V) : Nat × Nat × Nat × List Id := (v.major, v.minor, v.patch, v.pre)

def cmpK : Nat × Nat × Nat × List Id → Nat × Nat × Nat × List Id → Ordering :=
  cmpPair cmpN (cmpPair cmpN (cmpPair cmpN cmpPre))

def cmpV (a b : V) : Ordering := cmpK (key a) (key b)

theorem lawK : Law cmpK := lawPair lawN (lawPair lawN (lawPair lawN lawPre))

/-- 版本的比较是全序：交换两边结果反过来；相等当且仅当除了构建信息都一样；自反；小于可以传递 -/
theorem lawV :
    (∀ a b, cmpV b a = (cmpV a b).swap) ∧
    (∀ a b, cmpV a b = .eq ↔ key a = key b) ∧
    (∀ a, cmpV a a = .eq) ∧
    (∀ a b d, cmpV a b = .lt → cmpV b d = .lt → cmpV a d = .lt) :=
  ⟨fun a b => lawK.swap (key a) (key b),
    fun a b => ⟨lawK.eq (key a) (key b), fun e => by unfold cmpV; rw [e]; exact lawK.refl _⟩,
    fun a => lawK.refl (key a),
    fun a b d => lawK.trans (key a) (key b) (key d)⟩

-- semver.org 第 11 条的例子：1.0.0-alpha < 1.0.0-alpha.1 < 1.0.0-alpha.beta < 1.0.0-beta
--   < 1.0.0-beta.2 < 1.0.0-beta.11 < 1.0.0-rc.1 < 1.0.0；还有 1.0.0 < 2.0.0 < 2.1.0 < 2.1.1
section examples
private def alpha : Id := .alnum [97, 108, 112, 104, 97]
private def beta : Id := .alnum [98, 101, 116, 97]
private def rc : Id := .alnum [114, 99]
private def v1 (pre : List Id) : V := ⟨1, 0, 0, pre, []⟩
private def chain : List V :=
  [v1 [alpha], v1 [alpha, .num 1], v1 [alpha, beta], v1 [beta], v1 [beta, .num 2], v1 [beta, .num 11],
    v1 [rc, .num 1], v1 [], ⟨2, 0, 0, [], []⟩, ⟨2, 1, 0, [], []⟩, ⟨2, 1, 1, [], []⟩]

#guard (chain.zip chain.tail).all (fun p => cmpV p.1 p.2 == .lt)
-- 构建信息不参与比较
#guard cmpV ⟨1, 0, 0, [], [[115, 104, 97]]⟩ (v1 []) == .eq
end examples

/-! ## 写出来和解析（第 2、9、10 条）

字符串记成字节的列表。数字不能有前导零；预发布和构建信息按 . 分成标识符，标识符不能是空的，
只能用 0-9 A-Z a-z -；预发布的标识符全是数字时当数字，这时也不能有前导零。
按 + 切开（第一个 +），前一半再按 - 切开（第一个 -，主版本号里没有 -，预发布的标识符里可以有）。
`parse_format`：合法的版本写出来再解析回到原样。 -/

def isDigit (c : Nat) : Bool := decide (48 ≤ c ∧ c ≤ 57)

def identChar (c : Nat) : Bool :=
  decide ((48 ≤ c ∧ c ≤ 57) ∨ (65 ≤ c ∧ c ≤ 90) ∨ (97 ≤ c ∧ c ≤ 122) ∨ c = 45)

/-- 十进制，没有前导零 -/
def dec (n : Nat) : List Nat := if h : n < 10 then [48 + n] else dec (n / 10) ++ [48 + n % 10]

def val (s : List Nat) : Nat := s.foldl (fun x c => x * 10 + (c - 48)) 0

def noLead (s : List Nat) : Bool := decide (s.length ≤ 1 ∨ s.head? ≠ some 48)

def parseNum (s : List Nat) : Option Nat :=
  if s ≠ [] ∧ s.all isDigit = true ∧ noLead s = true then some (val s) else none

/-- 第一个 sep 前后两半；没有 sep 时是 none -/
def cut (sep : Nat) : List Nat → Option (List Nat × List Nat)
  | [] => none
  | c :: r => if c = sep then some ([], r) else (cut sep r).map (fun p => (c :: p.1, p.2))

def splitOpt (sep : Nat) (s : List Nat) : List Nat × Option (List Nat) :=
  match cut sep s with
  | none => (s, none)
  | some p => (p.1, some p.2)

def parseId (s : List Nat) : Option Id :=
  if s.all isDigit then (parseNum s).map Id.num
  else if s.all identChar then some (Id.alnum s) else none

def parseIds : List (List Nat) → Option (List Id)
  | [] => some []
  | x :: xs =>
    match parseId x, parseIds xs with
    | some i, some is => some (i :: is)
    | _, _ => none

def parseBuilds : List (List Nat) → Option (List (List Nat))
  | [] => some []
  | x :: xs => if x ≠ [] ∧ x.all identChar = true then (parseBuilds xs).map (x :: ·) else none

def parseMain (m : List Nat) : Option (Nat × Nat × Nat) :=
  match Url.splitOn 46 m with
  | [a, b, c] =>
    match parseNum a, parseNum b, parseNum c with
    | some x, some y, some z => some (x, y, z)
    | _, _, _ => none
  | _ => none

def parsePre : Option (List Nat) → Option (List Id)
  | none => some []
  | some p => parseIds (Url.splitOn 46 p)

def parseBuild : Option (List Nat) → Option (List (List Nat))
  | none => some []
  | some b => parseBuilds (Url.splitOn 46 b)

def parseCore (core : List Nat) (b : Option (List Nat)) : Option V :=
  match parseMain (splitOpt 45 core).1, parsePre (splitOpt 45 core).2, parseBuild b with
  | some (x, y, z), some pre, some bl => some ⟨x, y, z, pre, bl⟩
  | _, _, _ => none

def parse (s : List Nat) : Option V := parseCore (splitOpt 43 s).1 (splitOpt 43 s).2

def fmtId : Id → List Nat
  | .num n => dec n
  | .alnum s => s

def mainS (a b c : Nat) : List Nat := dec a ++ 46 :: (dec b ++ 46 :: dec c)

def fmtPre : List Id → List Nat
  | [] => []
  | i :: is => 45 :: Url.joinL 46 ((i :: is).map fmtId)

def fmtBuild : List (List Nat) → List Nat
  | [] => []
  | b :: bs => 43 :: Url.joinL 46 (b :: bs)

def format (v : V) : List Nat := (mainS v.major v.minor v.patch ++ fmtPre v.pre) ++ fmtBuild v.build

def okId : Id → Prop
  | .num _ => True
  | .alnum s => s.all identChar = true ∧ s.all isDigit = false

/-- 合法的版本：预发布的字母数字标识符不是全数字，构建信息的标识符不是空的；都只用 0-9 A-Z a-z - -/
def Valid (v : V) : Prop := (∀ i ∈ v.pre, okId i) ∧ (∀ b ∈ v.build, b ≠ [] ∧ b.all identChar = true)

section examples
private def S (s : String) : List Nat := s.toList.map Char.toNat
#guard (parse (S "1.0.0-alpha.1+sha.5")).map format == some (S "1.0.0-alpha.1+sha.5")
#guard (parse (S "10.20.30-rc.1-x.0a+b-1")).map format == some (S "10.20.30-rc.1-x.0a+b-1")
#guard (parse (S "01.0.0")).isNone
#guard (parse (S "1.0")).isNone
#guard (parse (S "1.0.0-")).isNone
#guard (parse (S "1.0.0-01")).isNone
#guard (parse (S "1.0.0+")).isNone
#guard (parse (S "1.0.0-a..b")).isNone
#guard (parse (S "1.0.0+a_b")).isNone
end examples

/-! ### 十进制 -/

theorem dec_digits (n : Nat) : ∀ c ∈ dec n, 48 ≤ c ∧ c ≤ 57 := by
  rw [dec]
  split
  · intro c hc
    simp only [List.mem_singleton] at hc
    omega
  · intro c hc
    rcases List.mem_append.1 hc with hc | hc
    · exact dec_digits (n / 10) c hc
    · simp only [List.mem_singleton] at hc
      have := Nat.mod_lt n (by omega : 10 > 0)
      omega
termination_by n

theorem val_dec (n : Nat) : val (dec n) = n := by
  rw [dec]
  split
  · simp only [val, List.foldl_cons, List.foldl_nil]
    omega
  · have ih : val (dec (n / 10)) = n / 10 := val_dec (n / 10)
    simp only [val, List.foldl_append, List.foldl_cons, List.foldl_nil] at ih ⊢
    rw [ih]
    omega
termination_by n

theorem dec_head (n : Nat) (h : 0 < n) : ∃ d r, dec n = d :: r ∧ d ≠ 48 := by
  rw [dec]
  split
  · exact ⟨48 + n, [], rfl, by omega⟩
  · obtain ⟨d, r, e, hd⟩ := dec_head (n / 10) (by omega)
    exact ⟨d, r ++ [48 + n % 10], by rw [e]; rfl, hd⟩
termination_by n

theorem dec_ne (n : Nat) : dec n ≠ [] := by
  rw [dec]
  split <;> simp

theorem dec_all (n : Nat) : (dec n).all isDigit = true :=
  List.all_eq_true.2 (fun c hc => by simp only [isDigit, decide_eq_true_eq]; exact dec_digits n c hc)

theorem noLead_dec (n : Nat) : noLead (dec n) = true := by
  by_cases h : n = 0
  · subst h
    rw [dec]
    simp [noLead]
  · obtain ⟨d, r, e, hd⟩ := dec_head n (by omega)
    rw [e]
    simp [noLead, hd]

theorem parseNum_dec (n : Nat) : parseNum (dec n) = some n := by
  unfold parseNum
  rw [ite_eq_left ⟨dec_ne n, dec_all n, noLead_dec n⟩, val_dec]

/-! ### 切开 -/

theorem cut_none (sep : Nat) : ∀ x : List Nat, sep ∉ x → cut sep x = none
  | [], _ => rfl
  | c :: r, h => by
    have hc : ¬c = sep := fun e => h (by simp [e])
    simp [cut, hc, cut_none sep r (fun m => h (List.mem_cons_of_mem _ m))]

theorem cut_app (sep : Nat) (y : List Nat) : ∀ x : List Nat, sep ∉ x → cut sep (x ++ sep :: y) = some (x, y)
  | [], _ => by simp [cut]
  | c :: r, h => by
    have hc : ¬c = sep := fun e => h (by simp [e])
    simp [cut, hc, cut_app sep y r (fun m => h (List.mem_cons_of_mem _ m))]

theorem splitOpt_none {sep : Nat} {x : List Nat} (h : sep ∉ x) : splitOpt sep x = (x, none) := by
  simp [splitOpt, cut_none sep x h]

theorem splitOpt_app {sep : Nat} {x y : List Nat} (h : sep ∉ x) : splitOpt sep (x ++ sep :: y) = (x, some y) := by
  simp [splitOpt, cut_app sep y x h]

/-! ### 每一部分解析回来 -/

theorem ident_not {c : Nat} (h : identChar c = true) : c ≠ 43 ∧ c ≠ 46 := by
  simp only [identChar, decide_eq_true_eq] at h
  omega

theorem fmtId_ok (i : Id) (h : okId i) : ∀ c ∈ fmtId i, identChar c = true := by
  cases i with
  | num n =>
    intro c hc
    have := dec_digits n c hc
    simp only [identChar, decide_eq_true_eq]
    omega
  | alnum s =>
    have h' : s.all identChar = true ∧ s.all isDigit = false := h
    exact List.all_eq_true.1 h'.1

theorem parseId_fmt (i : Id) (h : okId i) : parseId (fmtId i) = some i := by
  cases i with
  | num n =>
    show parseId (dec n) = some (.num n)
    unfold parseId
    rw [ite_eq_left (dec_all n), parseNum_dec]
    rfl
  | alnum s =>
    have h' : s.all identChar = true ∧ s.all isDigit = false := h
    show parseId s = some (.alnum s)
    unfold parseId
    rw [ite_eq_right (by rw [h'.2]; decide), ite_eq_left h'.1]

theorem parseIds_map : ∀ pre : List Id, (∀ i ∈ pre, okId i) → parseIds (pre.map fmtId) = some pre
  | [], _ => rfl
  | i :: is, h => by
    simp only [List.map_cons, parseIds]
    rw [parseId_fmt i (h i (List.mem_cons_self ..)), parseIds_map is (fun j hj => h j (List.mem_cons_of_mem _ hj))]

theorem parseBuilds_ok : ∀ bs : List (List Nat), (∀ b ∈ bs, b ≠ [] ∧ b.all identChar = true) →
    parseBuilds bs = some bs
  | [], _ => rfl
  | b :: bs, h => by
    simp only [parseBuilds]
    rw [ite_eq_left (h b (List.mem_cons_self ..)),
      parseBuilds_ok bs (fun x hx => h x (List.mem_cons_of_mem _ hx))]
    rfl

theorem main_chars (a b c : Nat) : ∀ x ∈ mainS a b c, (48 ≤ x ∧ x ≤ 57) ∨ x = 46 := by
  intro x hx
  simp only [mainS, List.mem_append, List.mem_cons] at hx
  rcases hx with hx | hx | hx | hx | hx
  · exact Or.inl (dec_digits a x hx)
  · exact Or.inr hx
  · exact Or.inl (dec_digits b x hx)
  · exact Or.inr hx
  · exact Or.inl (dec_digits c x hx)

theorem parseMain_ok (a b c : Nat) : parseMain (mainS a b c) = some (a, b, c) := by
  have n46 : ∀ n, 46 ∉ dec n := fun n m => by have := dec_digits n 46 m; omega
  unfold parseMain mainS
  rw [Url.split_app 46 _ (dec a) (n46 a), Url.split_app 46 _ (dec b) (n46 b), Url.split_free 46 (dec c) (n46 c)]
  simp only [parseNum_dec]

theorem pre_n43 (pre : List Id) (hp : ∀ i ∈ pre, okId i) : 43 ∉ fmtPre pre := by
  cases pre with
  | nil => simp [fmtPre]
  | cons i is =>
    intro m
    simp only [fmtPre, List.mem_cons] at m
    rcases m with m | m
    · omega
    · rcases Url.mem_joinL 46 43 _ m with e | ⟨x, hx, hc⟩
      · omega
      · obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hx
        exact (ident_not (fmtId_ok j (hp j hj) 43 hc)).1 rfl

def preOpt : List Id → Option (List Nat)
  | [] => none
  | i :: is => some (Url.joinL 46 ((i :: is).map fmtId))

def buildOpt : List (List Nat) → Option (List Nat)
  | [] => none
  | b :: bs => some (Url.joinL 46 (b :: bs))

theorem preOpt_ok (pre : List Id) (hp : ∀ i ∈ pre, okId i) : parsePre (preOpt pre) = some pre := by
  cases pre with
  | nil => rfl
  | cons i is =>
    have hs : ∀ x ∈ (i :: is).map fmtId, 46 ∉ x := by
      intro x hx m
      obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hx
      exact (ident_not (fmtId_ok j (hp j hj) 46 m)).2 rfl
    show parseIds (Url.splitOn 46 (Url.joinL 46 ((i :: is).map fmtId))) = some (i :: is)
    rw [Url.split_join 46 _ (by simp) hs]
    exact parseIds_map _ hp

theorem buildOpt_ok (bl : List (List Nat)) (hb : ∀ b ∈ bl, b ≠ [] ∧ b.all identChar = true) :
    parseBuild (buildOpt bl) = some bl := by
  cases bl with
  | nil => rfl
  | cons x xs =>
    have hs : ∀ y ∈ x :: xs, 46 ∉ y := fun y hy m => (ident_not (List.all_eq_true.1 (hb y hy).2 46 m)).2 rfl
    show parseBuilds (Url.splitOn 46 (Url.joinL 46 (x :: xs))) = some (x :: xs)
    rw [Url.split_join 46 _ (List.cons_ne_nil _ _) hs]
    exact parseBuilds_ok _ hb

/-- 合法的版本写出来再解析，回到原样（包括构建信息） -/
theorem parse_format (v : V) (h : Valid v) : parse (format v) = some v := by
  cases v with
  | mk a b c pre bl =>
  obtain ⟨hp, hb⟩ := h
  have hM43 : 43 ∉ mainS a b c := fun m => by rcases main_chars a b c 43 m with e | e <;> omega
  have hM45 : 45 ∉ mainS a b c := fun m => by rcases main_chars a b c 45 m with e | e <;> omega
  have hA : 43 ∉ mainS a b c ++ fmtPre pre := by
    intro m
    rcases List.mem_append.1 m with m | m
    · exact hM43 m
    · exact pre_n43 pre hp m
  have e1 : splitOpt 43 (format ⟨a, b, c, pre, bl⟩) = (mainS a b c ++ fmtPre pre, buildOpt bl) := by
    cases bl with
    | nil =>
      show splitOpt 43 ((mainS a b c ++ fmtPre pre) ++ []) = _
      rw [List.append_nil]
      exact splitOpt_none hA
    | cons x xs =>
      show splitOpt 43 ((mainS a b c ++ fmtPre pre) ++ 43 :: Url.joinL 46 (x :: xs)) = _
      exact splitOpt_app hA
  have e2 : splitOpt 45 (mainS a b c ++ fmtPre pre) = (mainS a b c, preOpt pre) := by
    cases pre with
    | nil =>
      show splitOpt 45 (mainS a b c ++ []) = _
      rw [List.append_nil]
      exact splitOpt_none hM45
    | cons i is =>
      show splitOpt 45 (mainS a b c ++ 45 :: Url.joinL 46 ((i :: is).map fmtId)) = _
      exact splitOpt_app hM45
  have e3 := parseMain_ok a b c
  have e4 := preOpt_ok pre hp
  have e5 := buildOpt_ok bl hb
  unfold parse parseCore
  simp only [e1, e2, e3, e4, e5]
end Semver
end Lark
