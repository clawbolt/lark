/-
标准库的证明 · JSON（std/json.lark）

照着 std/json.lark 写一份，字节串写成 List Nat，读的函数写成带燃料的递归，出错是 none。分几步：

- 字符串：quote 写出来的字符串，read_str 读回来不变（`rs_quote`）。quote 只转义 " \ 和控制字符，
  控制字符里 \n \t \r 写成 \n \t \r，其它写成 \u00XX；read_str 认 \" \\ \/ \n \t \r \b \f 和 \uXXXX（包括代理对）。
- 数、数组、对象，最后是整个值：`parse_format`，满足 `Good 0 j` 时 parse(format(j)) = j
  （Int 在 64 位里，Float 不是 inf / nan、文字合乎 FloatText，嵌套不超过 512 层，对象的键和值一样多）。
-/
import Lark.Utf8

namespace Lark
namespace Json

/-! ## 写：quote -/

/-- 0..15 写成十六进制的一个字符（小写） -/
def hexD (d : Nat) : Nat := if d < 10 then 48 + d else 87 + d

/-- 一个字节转义以后 -/
def escB (b : Nat) : List Nat :=
  if b = 34 then [92, 34] else if b = 92 then [92, 92] else if b = 10 then [92, 110]
  else if b = 9 then [92, 116] else if b = 13 then [92, 114]
  else if b < 32 then [92, 117, 48, 48, hexD (b / 16), hexD (b % 16)] else [b]

def escS : List Nat → List Nat
  | [] => []
  | b :: r => escB b ++ escS r

def quote (s : List Nat) : List Nat := 34 :: escS s ++ [34]

/-! ## 读：read_str（开头的引号已经吃掉） -/

/-- hex_val：不是十六进制数字时是 none（Lark 里是 -1） -/
def hv (b : Nat) : Option Nat :=
  if 48 ≤ b ∧ b ≤ 57 then some (b - 48)
  else if 97 ≤ b ∧ b ≤ 102 then some (b - 97 + 10)
  else if 65 ≤ b ∧ b ≤ 70 then some (b - 65 + 10)
  else none

/-- read_hex4 -/
def hex4 : List Nat → Option (Nat × List Nat)
  | a :: b :: c :: d :: r =>
    match hv a, hv b, hv c, hv d with
    | some x1, some x2, some x3, some x4 => some (((x1 * 16 + x2) * 16 + x3) * 16 + x4, r)
    | _, _, _, _ => none
  | _ => none

/-- unescape：\ 后面的字符；不认识的是 none -/
def unesc (e : Nat) : Option Nat :=
  if e = 34 then some 34 else if e = 92 then some 92 else if e = 47 then some 47
  else if e = 110 then some 10 else if e = 116 then some 9 else if e = 114 then some 13
  else if e = 98 then some 8 else if e = 102 then some 12 else none

/-- read_str 的循环：读到结束的引号，返回内容和后面剩下的 -/
def rsF : Nat → List Nat → List Nat → Option (List Nat × List Nat)
  | 0, _, _ => none
  | _ + 1, _, [] => none
  | n + 1, acc, b :: r =>
    if b = 34 then some (acc, r)
    else if b < 32 then none
    else if b = 92 then
      match r with
      | [] => none
      | e :: r2 =>
        if e = 117 then
          match hex4 r2 with
          | none => none
          | some (cp, r3) =>
            if 56320 ≤ cp ∧ cp ≤ 57343 then none
            else if 55296 ≤ cp ∧ cp ≤ 56319 then
              match r3 with
              | 92 :: 117 :: r4 =>
                match hex4 r4 with
                | none => none
                | some (lo, r5) =>
                  if lo < 56320 ∨ 57343 < lo then none
                  else rsF n (acc ++ Utf8.enc (65536 + (cp - 55296) * 1024 + (lo - 56320))) r5
              | _ => none
            else rsF n (acc ++ Utf8.enc cp) r3
        else
          match unesc e with
          | none => none
          | some c => rsF n (acc ++ [c]) r2
    else rsF n (acc ++ [b]) r

/-! ## 例子：和 tests/unit/json.lark 对上 -/

-- a " 换行 \x01：写成 a\"\n\u0001，读回来不变
example : escS [97, 34, 10, 1] = [97, 92, 34, 92, 110, 92, 117, 48, 48, 48, 49] := by decide
example : rsF 20 [] (escS [97, 34, 10, 1] ++ [34]) = some ([97, 34, 10, 1], []) := by decide
-- 😀 是 😀（F0 9F 98 80）
example : rsF 20 [] [92, 117, 100, 56, 51, 100, 92, 117, 100, 101, 48, 48, 34] = some ([240, 159, 152, 128], []) := by
  decide
-- 单独的后一半、单独的前一半、不认识的转义、直接出现的控制字符、没有结束
example : rsF 20 [] [92, 117, 100, 101, 48, 48, 34] = none := by decide
example : rsF 20 [] [92, 117, 100, 56, 51, 100, 34] = none := by decide
example : rsF 20 [] [92, 120, 34] = none := by decide
example : rsF 20 [] [10, 34] = none := by decide
example : rsF 20 [] [97] = none := by decide

/-! ## 写出来再读回去 -/

theorem hv_hex : ∀ d, d < 16 → hv (hexD d) = some d := by decide

theorem hex4_ctl {b : Nat} (hb : b < 32) (t : List Nat) :
    hex4 (48 :: 48 :: hexD (b / 16) :: hexD (b % 16) :: t) = some (b, t) := by
  have d1 : b / 16 < 16 := by omega
  have d2 : b % 16 < 16 := by omega
  have h48 : hv 48 = some 0 := by decide
  simp [hex4, h48, hv_hex _ d1, hv_hex _ d2] <;> omega

/-- 一个字节：转义以后读一步，正好读回这个字节 -/
theorem rs_step (n : Nat) (acc t : List Nat) (b : Nat) : rsF (n + 1) acc (escB b ++ t) = rsF n (acc ++ [b]) t := by
  unfold escB
  by_cases h1 : b = 34
  · subst h1
    simp [rsF, unesc]
  by_cases h2 : b = 92
  · subst h2
    simp [rsF, unesc]
  by_cases h3 : b = 10
  · subst h3
    simp [rsF, unesc]
  by_cases h4 : b = 9
  · subst h4
    simp [rsF, unesc]
  by_cases h5 : b = 13
  · subst h5
    simp [rsF, unesc]
  rw [ite_eq_right h1, ite_eq_right h2, ite_eq_right h3, ite_eq_right h4, ite_eq_right h5]
  by_cases h6 : b < 32
  · rw [ite_eq_left h6]
    have c1 : ¬(56320 ≤ b ∧ b ≤ 57343) := by omega
    have c2 : ¬(55296 ≤ b ∧ b ≤ 56319) := by omega
    have he : Utf8.enc b = [b] := by
      unfold Utf8.enc
      rw [ite_eq_left (by omega : b < 128)]
    simp [rsF, hex4_ctl h6, c1, c2, he]
  · rw [ite_eq_right h6]
    simp [rsF, h1, h2, h6]

/-- quote 写出来的字符串，read_str 读回来不变，停在结束的引号后面 -/
theorem rs_quote : ∀ (s acc rest : List Nat) (n : Nat), s.length < n →
    rsF n acc (escS s ++ 34 :: rest) = some (acc ++ s, rest)
  | _, _, _, 0, h => absurd h (Nat.not_lt_zero _)
  | [], acc, rest, n + 1, _ => by simp [escS, rsF]
  | b :: s, acc, rest, n + 1, h => by
    rw [escS, List.append_assoc, rs_step, rs_quote s (acc ++ [b]) rest n (by simp at h; omega)]
    simp

/-! ## 整数：int_str 写出来，int_of 读回来

int_str(n) 是 C 的 %lld：n ≥ 0 时是 n 的十进制，n < 0 时是 - 加上 -n 的十进制（最小的 int 也一样）。
int_of 用负数累计：n = n * 10 - d，每步之前检查 n < (MIN + d) / 10（C 的除法向 0 取整，Lean 里是 Int.tdiv）。 -/

/-- 十进制的数字（最高位在前，0 是 "0"），燃料给 m + 1 -/
def decF : Nat → Nat → List Nat
  | 0, _ => []
  | f + 1, m => if m < 10 then [48 + m] else decF f (m / 10) ++ [48 + m % 10]

def dec (m : Nat) : List Nat := decF (m + 1) m

/-- 一串数字的值 -/
def valF : Nat → List Nat → Nat
  | a, [] => a
  | a, c :: r => valF (a * 10 + (c - 48)) r

/-- int_of 的循环，照着 Lark 写 -/
def ioI : Int → List Nat → Option Int
  | n, [] => some n
  | n, c :: r =>
    if n < Int.tdiv (-9223372036854775808 + ((c : Int) - 48)) 10 then none else ioI (n * 10 - ((c : Int) - 48)) r

def intOf (s : List Nat) (neg : Bool) : Option Int :=
  match ioI 0 s with
  | none => none
  | some n => if neg then some n else if n = -9223372036854775808 then none else some (-n)

-- 最大和最小的 int 都能读回来，再大一个就不是 int 了（read_num 改按 Float 读）
example : intOf (dec 9223372036854775807) false = some 9223372036854775807 := by decide
example : intOf (dec 9223372036854775808) true = some (-9223372036854775808) := by decide
example : intOf (dec 9223372036854775808) false = none := by decide
example : intOf (dec 9223372036854775809) true = none := by decide
example : dec 0 = [48] := by decide
example : dec 120 = [49, 50, 48] := by decide

abbrev Digits (s : List Nat) : Prop := ∀ c ∈ s, 48 ≤ c ∧ c ≤ 57

/-- 用自然数写的同一个循环：a 是已经读到的值，超过 2^63 就停 -/
def ioN : Nat → List Nat → Option Nat
  | a, [] => some a
  | a, c :: r => if 9223372036854775808 < a * 10 + (c - 48) then none else ioN (a * 10 + (c - 48)) r

theorem valF_ge : ∀ (s : List Nat) (a : Nat), a ≤ valF a s
  | [], _ => Nat.le_refl _
  | c :: r, a => by
    have := valF_ge r (a * 10 + (c - 48))
    show a ≤ valF (a * 10 + (c - 48)) r
    omega

theorem ioN_eq : ∀ (s : List Nat) (a : Nat), a ≤ 9223372036854775808 →
    ioN a s = if valF a s ≤ 9223372036854775808 then some (valF a s) else none
  | [], a, ha => by
    show some a = if a ≤ 9223372036854775808 then some a else none
    rw [ite_eq_left ha]
  | c :: r, a, _ => by
    show (if 9223372036854775808 < a * 10 + (c - 48) then none else ioN (a * 10 + (c - 48)) r) =
      if valF (a * 10 + (c - 48)) r ≤ 9223372036854775808 then some (valF (a * 10 + (c - 48)) r) else none
    by_cases h : 9223372036854775808 < a * 10 + (c - 48)
    · have := valF_ge r (a * 10 + (c - 48))
      have h2 : ¬ valF (a * 10 + (c - 48)) r ≤ 9223372036854775808 := by omega
      rw [ite_eq_left h, ite_eq_right h2]
    · rw [ite_eq_right h, ioN_eq r _ (by omega)]

/-- C 的 (MIN + d) / 10 -/
theorem tdiv_min : ∀ d : Nat, d < 10 → Int.tdiv (-9223372036854775808 + (d : Int)) 10 =
    if d = 9 then -922337203685477579 else -922337203685477580 := by decide

/-- Lark 的检查 n < (MIN + d) / 10 就是 n * 10 - d 会小于 MIN -/
theorem chk (a d : Nat) (hd : d < 10) :
    -(a : Int) < Int.tdiv (-9223372036854775808 + (d : Int)) 10 ↔ 9223372036854775808 < a * 10 + d := by
  rw [tdiv_min d hd]
  split <;> omega

theorem ioI_eq : ∀ (s : List Nat) (a : Nat), Digits s → ioI (-(a : Int)) s = (ioN a s).map (fun b => -(b : Int))
  | [], a, _ => rfl
  | c :: r, a, hs => by
    have hc := hs c (List.mem_cons_self ..)
    have hr : Digits r := fun x hx => hs x (List.mem_cons_of_mem _ hx)
    have e1 : ((c : Int) - 48) = ((c - 48 : Nat) : Int) := by omega
    have e2 : -(a : Int) * 10 - ((c - 48 : Nat) : Int) = -((a * 10 + (c - 48) : Nat) : Int) := by omega
    simp only [ioI, ioN]
    rw [e1, e2]
    by_cases h : 9223372036854775808 < a * 10 + (c - 48)
    · rw [ite_eq_left ((chk a (c - 48) (by omega)).mpr h), ite_eq_left h]
      rfl
    · rw [ite_eq_right (fun h2 => h ((chk a (c - 48) (by omega)).mp h2)), ite_eq_right h, ioI_eq r _ hr]

/-- int_of 读一串数字：带 - 时在 -2^63 .. 0 里的读成 int，不带时在 0 .. 2^63 - 1 里的读成 int，其它是 None -/
theorem intOf_spec (s : List Nat) (hs : Digits s) :
    intOf s true = (if valF 0 s ≤ 9223372036854775808 then some (-(valF 0 s : Int)) else none) ∧
    intOf s false = (if valF 0 s < 9223372036854775808 then some (valF 0 s : Int) else none) := by
  have h : ioI 0 s = (ioN 0 s).map (fun b => -(b : Int)) := ioI_eq s 0 hs
  rw [ioN_eq s 0 (Nat.zero_le _)] at h
  unfold intOf
  rw [h]
  by_cases hv : valF 0 s ≤ 9223372036854775808
  · rw [ite_eq_left hv]
    simp only
    refine ⟨by simp [hv], ?_⟩
    by_cases hv2 : valF 0 s < 9223372036854775808
    · have : ¬ (-((valF 0 s : Nat) : Int) = -9223372036854775808) := by omega
      simp [this, hv2]
    · have : -((valF 0 s : Nat) : Int) = -9223372036854775808 := by omega
      simp [this, hv2]
  · rw [ite_eq_right hv]
    have hv2 : ¬ valF 0 s < 9223372036854775808 := by omega
    simp [hv, hv2]

theorem valF_snoc : ∀ (l : List Nat) (a c : Nat), valF a (l ++ [c]) = valF a l * 10 + (c - 48)
  | [], _, _ => rfl
  | x :: l, a, c => valF_snoc l (a * 10 + (x - 48)) c

/-- dec 写出来的都是数字，值就是原来的数 -/
theorem dec_ok : ∀ (f m : Nat), m < f → Digits (decF f m) ∧ valF 0 (decF f m) = m
  | 0, _, h => absurd h (Nat.not_lt_zero _)
  | f + 1, m, h => by
    simp only [decF]
    by_cases hm : m < 10
    · rw [ite_eq_left hm]
      refine ⟨fun c hc => ?_, by show 0 * 10 + (48 + m - 48) = m; omega⟩
      simp at hc
      omega
    · rw [ite_eq_right hm]
      obtain ⟨d1, v1⟩ := dec_ok f (m / 10) (by omega)
      refine ⟨fun c hc => ?_, ?_⟩
      · rcases List.mem_append.mp hc with hc | hc
        · exact d1 c hc
        · simp at hc
          omega
      · rw [valF_snoc, v1]
        omega

/-- int_str(n) 去掉 - 以后的数字，int_of 读回来就是 n：最大和最小的 int 都一样 -/
theorem int_roundtrip (n : Int) (h1 : -9223372036854775808 ≤ n) (h2 : n < 9223372036854775808) :
    intOf (dec n.natAbs) (decide (n < 0)) = some n := by
  obtain ⟨hd, hv⟩ := dec_ok (n.natAbs + 1) n.natAbs (by omega)
  obtain ⟨t, f⟩ := intOf_spec (dec n.natAbs) hd
  unfold dec at t f
  unfold dec
  rw [hv] at t f
  by_cases hn : n < 0
  · have e : decide (n < 0) = true := by simp [hn]
    rw [e, t, ite_eq_left (by omega)]
    congr 1
    omega
  · have e : decide (n < 0) = false := by simp [hn]
    rw [e, f, ite_eq_left (by omega)]
    congr 1
    omega

/-! ## read_num 扫描数的写法：-?(0|[1-9][0-9]*)(.[0-9]+)?([eE][+-]?[0-9]+)?

照着 read_num 拆成几块：负号、整数部分（skip_digits）、小数部分、指数部分。返回
(负号, 整数部分的数字, 是不是 Float, 剩下的)；格式不对时是 none。 -/

def isD (c : Nat) : Bool := decide (48 ≤ c ∧ c ≤ 57)

/-- skip_digits：开头的一串数字和后面剩下的 -/
def span : List Nat → List Nat × List Nat
  | [] => ([], [])
  | c :: r => if isD c then (c :: (span r).1, (span r).2) else ([], c :: r)

def sign : List Nat → Bool × List Nat
  | c :: r => if c = 45 then (true, r) else (false, c :: r)
  | [] => (false, [])

def frac : List Nat → Option (Bool × List Nat)
  | c :: r => if c = 46 then (if (span r).1 = [] then none else some (true, (span r).2)) else some (false, c :: r)
  | [] => some (false, [])

def sgn : List Nat → List Nat
  | c :: t => if c = 43 ∨ c = 45 then t else c :: t
  | [] => []

def expo : List Nat → Option (Bool × List Nat)
  | c :: r =>
    if c = 101 ∨ c = 69 then (if (span (sgn r)).1 = [] then none else some (true, (span (sgn r)).2))
    else some (false, c :: r)
  | [] => some (false, [])

def scan (s : List Nat) : Option (Bool × List Nat × Bool × List Nat) :=
  let ds := (span (sign s).2).1
  if ds = [] then none
  else if 1 < ds.length ∧ ds.head? = some 48 then none
  else
    match frac (span (sign s).2).2 with
    | none => none
    | some (f1, s3) =>
      match expo s3 with
      | none => none
      | some (f2, rest) => some ((sign s).1, ds, f1 || f2, rest)

/-- int_str(n)：负数前面加 - -/
def intText (n : Int) : List Nat := (if n < 0 then [45] else []) ++ dec n.natAbs

-- -120 后面跟着 ,；1.5e-3；数不能以 0 开头；- 后面要有数字；小数点后面要有数字
example : scan (intText (-120) ++ [44]) = some (true, [49, 50, 48], false, [44]) := by decide
example : scan [49, 46, 53, 101, 45, 51, 93] = some (false, [49], true, [93]) := by decide
example : scan [48, 49] = none := by decide
example : scan [45, 93] = none := by decide
example : scan [49, 46, 93] = none := by decide

/-- 数后面紧跟着的不是数字、小数点、e 或 E（format 写出来的后面是 , ] } 或结尾） -/
def Stop : List Nat → Prop
  | [] => True
  | c :: _ => ¬(48 ≤ c ∧ c ≤ 57) ∧ c ≠ 46 ∧ c ≠ 101 ∧ c ≠ 69

theorem span_app : ∀ (ds rest : List Nat), Digits ds → Stop rest → span (ds ++ rest) = (ds, rest)
  | [], [], _, _ => rfl
  | [], c :: t, _, h => by
    obtain ⟨h1, -, -, -⟩ := h
    have hc : ¬ isD c = true := by simp [isD, h1]
    rw [List.nil_append, span, ite_eq_right hc]
  | d :: ds, rest, hd, hr => by
    have h1 : isD d = true := decide_eq_true (hd d (List.mem_cons_self ..))
    have ih := span_app ds rest (fun x hx => hd x (List.mem_cons_of_mem _ hx)) hr
    rw [List.cons_append, span, ite_eq_left h1, ih]

theorem frac_stop : ∀ rest : List Nat, Stop rest → frac rest = some (false, rest)
  | [], _ => rfl
  | c :: t, h => by
    obtain ⟨-, h2, -, -⟩ := h
    rw [frac, ite_eq_right h2]

theorem expo_stop : ∀ rest : List Nat, Stop rest → expo rest = some (false, rest)
  | [], _ => rfl
  | c :: t, h => by
    obtain ⟨-, -, h3, h4⟩ := h
    have : ¬(c = 101 ∨ c = 69) := by omega
    rw [expo, ite_eq_right this]

theorem decF_ne : ∀ (f m : Nat), m < f → decF f m ≠ []
  | 0, _, h => absurd h (Nat.not_lt_zero _)
  | f + 1, m, _ => by
    simp only [decF]
    split <;> simp

theorem decF_len : ∀ (f m : Nat), m < f → 1 < (decF f m).length → 10 ≤ m
  | 0, _, h, _ => absurd h (Nat.not_lt_zero _)
  | f + 1, m, _, hl => by
    by_cases hm : m < 10
    · simp only [decF, ite_eq_left hm] at hl
      simp at hl
    · omega

theorem decF_head : ∀ (f k : Nat), k < f → 1 ≤ k → (decF f k).head? ≠ some 48
  | 0, _, h, _ => absurd h (Nat.not_lt_zero _)
  | f + 1, k, hf, hk => by
    simp only [decF]
    by_cases hm : k < 10
    · rw [ite_eq_left hm]
      simp
      omega
    · rw [ite_eq_right hm]
      have ih := decF_head f (k / 10) (by omega) (by omega)
      obtain ⟨x, xs, hx⟩ := List.exists_cons_of_ne_nil (decF_ne f (k / 10) (by omega))
      rw [hx] at ih ⊢
      simpa using ih

/-- int_str 写出来的整数，read_num 扫描得到负号和 |n| 的数字，不是 Float，停在后面紧跟着的地方 -/
theorem scan_int (n : Int) (rest : List Nat) (hr : Stop rest) :
    scan (intText n ++ rest) = some (decide (n < 0), dec n.natAbs, false, rest) := by
  have hd : Digits (dec n.natAbs) := (dec_ok (n.natAbs + 1) n.natAbs (by omega)).1
  have hne : dec n.natAbs ≠ [] := decF_ne (n.natAbs + 1) n.natAbs (by omega)
  have hlead : ¬(1 < (dec n.natAbs).length ∧ (dec n.natAbs).head? = some 48) := by
    intro ⟨h1, h2⟩
    exact decF_head (n.natAbs + 1) n.natAbs (by omega) (by have := decF_len _ _ (by omega) h1; omega) h2
  have hsign : sign (intText n ++ rest) = (decide (n < 0), dec n.natAbs ++ rest) := by
    unfold intText
    by_cases hn : n < 0
    · rw [ite_eq_left hn]
      simp [sign, hn]
    · rw [ite_eq_right hn, List.nil_append]
      obtain ⟨x, xs, hx⟩ := List.exists_cons_of_ne_nil hne
      have hx45 : x ≠ 45 := by
        have := hd x (by rw [hx]; exact List.mem_cons_self ..)
        omega
      rw [hx]
      simp [sign, hx45, hn]
  have hsp : span (dec n.natAbs ++ rest) = (dec n.natAbs, rest) := span_app _ _ hd hr
  unfold scan
  simp only [hsign, hsp]
  rw [ite_eq_right hne, ite_eq_right hlead]
  simp [frac_stop rest hr, expo_stop rest hr]

/-! ## Float：float_str 写出来的数

float_str 是 C 的 snprintf（runtime 的 lk_fmt_float），Lean 里展开不了，写成前提 `FloatText`：
它写出来的是 -?数字(.数字)?(e[+-]?数字)?，整数部分不以 0 开头（只有一位时除外），而且带小数点或指数
（lk_fmt_float 用 %.*f 或 %.*e，整数值后面补 .0）。在这个前提下，read_num 扫描到的正是整个数、判成 Float。 -/

abbrev FloatText (t : List Nat) : Prop :=
  ∃ (neg : Bool) (ds fr ex : List Nat), t = (if neg then [45] else []) ++ (ds ++ (fr ++ ex)) ∧
    ds ≠ [] ∧ Digits ds ∧ ¬(1 < ds.length ∧ ds.head? = some 48) ∧
    (fr = [] ∨ ∃ f, fr = 46 :: f ∧ f ≠ [] ∧ Digits f) ∧
    (ex = [] ∨ ∃ sg e, ex = 101 :: (sg ++ e) ∧ (sg = [] ∨ sg = [43] ∨ sg = [45]) ∧ e ≠ [] ∧ Digits e) ∧
    (fr ≠ [] ∨ ex ≠ [])

/-- 开头不是数字 -/
def ND : List Nat → Prop
  | [] => True
  | c :: _ => ¬(48 ≤ c ∧ c ≤ 57)

theorem stop_nd : ∀ {r : List Nat}, Stop r → ND r
  | [], _ => trivial
  | _ :: _, h => h.1

theorem span_nd : ∀ (ds rest : List Nat), Digits ds → ND rest → span (ds ++ rest) = (ds, rest)
  | [], [], _, _ => rfl
  | [], c :: t, _, h => by
    have hc : ¬ isD c = true := by simp [isD]; simp [ND] at h; omega
    rw [List.nil_append, span, ite_eq_right hc]
  | d :: ds, rest, hd, hr => by
    have h1 : isD d = true := decide_eq_true (hd d (List.mem_cons_self ..))
    have ih := span_nd ds rest (fun x hx => hd x (List.mem_cons_of_mem _ hx)) hr
    rw [List.cons_append, span, ite_eq_left h1, ih]

theorem nd_46 (T : List Nat) : ND (46 :: T) := by simp [ND]
theorem nd_101 (T : List Nat) : ND (101 :: T) := by simp [ND]

theorem sign_ok (neg : Bool) {ds : List Nat} (X : List Nat) (hd : Digits ds) (hne : ds ≠ []) :
    sign ((if neg then [45] else []) ++ (ds ++ X)) = (neg, ds ++ X) := by
  cases neg
  · obtain ⟨x, xs, hx⟩ := List.exists_cons_of_ne_nil hne
    have := hd x (by rw [hx]; exact List.mem_cons_self ..)
    have h45 : x ≠ 45 := by omega
    subst hx
    simp [sign, h45]
  · simp [sign]

theorem frac_cons {f T : List Nat} (hsp : span (f ++ T) = (f, T)) (hne : f ≠ []) :
    frac (46 :: (f ++ T)) = some (true, T) := by
  simp [frac, hsp, hne]

theorem frac_e (T : List Nat) : frac (101 :: T) = some (false, 101 :: T) := by simp [frac]

theorem expo_e {sg e rest : List Nat} (hsg : sg = [] ∨ sg = [43] ∨ sg = [45]) (hen : e ≠ []) (hed : Digits e)
    (hr : Stop rest) : expo (101 :: (sg ++ (e ++ rest))) = some (true, rest) := by
  have hsp : span (e ++ rest) = (e, rest) := span_nd e rest hed (stop_nd hr)
  have hs : sgn (sg ++ (e ++ rest)) = e ++ rest := by
    obtain ⟨x, xs, hx⟩ := List.exists_cons_of_ne_nil hen
    have hx1 := hed x (by rw [hx]; exact List.mem_cons_self ..)
    have hx43 : ¬(x = 43 ∨ x = 45) := by omega
    rcases hsg with rfl | rfl | rfl
    · rw [hx]
      simp [sgn, hx43]
    · simp [sgn]
    · simp [sgn]
  simp [expo, hs, hsp, hen]

/-- float_str 写出来的数，read_num 扫描到整个数、判成 Float，停在后面紧跟着的地方 -/
theorem scan_float {t rest : List Nat} (h : FloatText t) (hr : Stop rest) :
    ∃ (neg : Bool) (ds : List Nat), scan (t ++ rest) = some (neg, ds, true, rest) := by
  obtain ⟨neg, ds, fr, ex, rfl, hne, hd, hlead, hf, he, hfe⟩ := h
  refine ⟨neg, ds, ?_⟩
  rcases hf with rfl | ⟨f, rfl, hfn, hfd⟩ <;> rcases he with rfl | ⟨sg, e, rfl, hsg, hen, hed⟩
  · simp at hfe
  · simp only [List.append_assoc, List.cons_append, List.nil_append]
    have hsp : span (ds ++ (101 :: (sg ++ (e ++ rest)))) = (ds, 101 :: (sg ++ (e ++ rest))) :=
      span_nd _ _ hd (nd_101 _)
    unfold scan
    simp only [sign_ok neg _ hd hne, hsp]
    rw [ite_eq_right hne, ite_eq_right hlead, frac_e]
    simp [expo_e hsg hen hed hr]
  · simp only [List.append_assoc, List.cons_append, List.append_nil]
    have hsp : span (ds ++ (46 :: (f ++ rest))) = (ds, 46 :: (f ++ rest)) := span_nd _ _ hd (nd_46 _)
    unfold scan
    simp only [sign_ok neg _ hd hne, hsp]
    rw [ite_eq_right hne, ite_eq_right hlead, frac_cons (span_nd f rest hfd (stop_nd hr)) hfn]
    simp [expo_stop rest hr]
  · simp only [List.append_assoc, List.cons_append]
    have hsp : span (ds ++ (46 :: (f ++ (101 :: (sg ++ (e ++ rest)))))) =
        (ds, 46 :: (f ++ (101 :: (sg ++ (e ++ rest))))) := span_nd _ _ hd (nd_46 _)
    unfold scan
    simp only [sign_ok neg _ hd hne, hsp]
    rw [ite_eq_right hne, ite_eq_right hlead, frac_cons (span_nd f _ hfd (nd_101 _)) hfn]
    simp [expo_e hsg hen hed hr]

-- lk_fmt_float 的几种写法都合乎前提：1.0、-0.0、0.1、1e+20、1.5e-07
example : scan ([49, 46, 48] ++ [44]) = some (false, [49], true, [44]) := by decide
example : scan ([45, 48, 46, 48] ++ []) = some (true, [48], true, []) := by decide
example : scan ([49, 101, 43, 50, 48] ++ [93]) = some (false, [49], true, [93]) := by decide
example : scan ([49, 46, 53, 101, 45, 48, 55] ++ [125]) = some (false, [49], true, [125]) := by decide

/-! ## 值：Json、format、read_value

Float 记成它写出来的文字（float_str(x)）：read_num 读到的 Float 是 parse_float(文字)，
parse_float(float_str(x)) = x（C 的 strtod 读回 lk_fmt_float 的最短写法）这一条不在 Lean 里，
所以这里比较的是文字。inf / nan 写成 null 读不回来，不在前提（FloatText）里。
Obj 和 Lark 一样是两个列表：键和值，一样长。 -/

inductive J where
  | null
  | bool (b : Bool)
  | num (n : Int)
  | flt (t : List Nat)
  | str (s : List Nat)
  | arr (items : List J)
  | obj (ks : List (List Nat)) (vs : List J)

mutual
def fmt : J → List Nat
  | .null => [110, 117, 108, 108]
  | .bool b => if b then [116, 114, 117, 101] else [102, 97, 108, 115, 101]
  | .num n => intText n
  | .flt t => t
  | .str s => quote s
  | .arr items => 91 :: fmtA items ++ [93]
  | .obj ks vs => 123 :: fmtO ks vs ++ [125]
/-- 数组的元素，用 , 隔开 -/
def fmtA : List J → List Nat
  | [] => []
  | [x] => fmt x
  | x :: y :: r => fmt x ++ 44 :: fmtA (y :: r)
/-- 对象的 "键":值，用 , 隔开 -/
def fmtO : List (List Nat) → List J → List Nat
  | [], _ => []
  | _, [] => []
  | [k], v :: _ => quote k ++ 58 :: fmt v
  | k :: k2 :: ks, v :: vs => quote k ++ 58 :: fmt v ++ 44 :: fmtO (k2 :: ks) vs
end

/-- skip_ws -/
def skipWs : List Nat → List Nat
  | c :: r => if c = 32 ∨ c = 9 ∨ c = 10 ∨ c = 13 then skipWs r else c :: r
  | [] => []

/-- read_num：Float 记成文字；超出 int 范围的整数也读成 Float -/
def readNum (s : List Nat) : Option (J × List Nat) :=
  match scan s with
  | none => none
  | some (neg, ds, fl, rest) =>
    if fl then some (.flt (s.take (s.length - rest.length)), rest)
    else
      match intOf ds neg with
      | some n => some (.num n, rest)
      | none => some (.flt (s.take (s.length - rest.length)), rest)

mutual
/-- read_value：d 是现在在几层数组 / 对象里面，最多 512 层 -/
def rv : Nat → Nat → List Nat → Option (J × List Nat)
  | 0, _, _ => none
  | n + 1, d, s =>
    match skipWs s with
    | [] => none
    | c :: r =>
      if c = 91 then (if 512 ≤ d then none else ra n (d + 1) r)
      else if c = 123 then (if 512 ≤ d then none else ro n (d + 1) r)
      else if c = 34 then
        (match rsF (r.length + 1) [] r with
         | none => none
         | some (x, r') => some (.str x, r'))
      else if c = 45 ∨ (48 ≤ c ∧ c ≤ 57) then readNum (c :: r)
      else if (c :: r).take 4 = [116, 114, 117, 101] then some (.bool true, (c :: r).drop 4)
      else if (c :: r).take 5 = [102, 97, 108, 115, 101] then some (.bool false, (c :: r).drop 5)
      else if (c :: r).take 4 = [110, 117, 108, 108] then some (.null, (c :: r).drop 4)
      else none
/-- read_arr（[ 已经吃掉） -/
def ra : Nat → Nat → List Nat → Option (J × List Nat)
  | 0, _, _ => none
  | n + 1, d, s =>
    match skipWs s with
    | c :: r => if c = 93 then some (.arr [], r) else raL n d [] s
    | [] => raL n d [] s
def raL : Nat → Nat → List J → List Nat → Option (J × List Nat)
  | 0, _, _, _ => none
  | n + 1, d, acc, s =>
    match rv n d s with
    | none => none
    | some (v, r) =>
      match skipWs r with
      | c :: r2 =>
        if c = 93 then some (.arr (acc ++ [v]), r2) else if c = 44 then raL n d (acc ++ [v]) r2 else none
      | [] => none
/-- read_obj（{ 已经吃掉） -/
def ro : Nat → Nat → List Nat → Option (J × List Nat)
  | 0, _, _ => none
  | n + 1, d, s =>
    match skipWs s with
    | c :: r => if c = 125 then some (.obj [] [], r) else roL n d [] [] s
    | [] => roL n d [] [] s
def roL : Nat → Nat → List (List Nat) → List J → List Nat → Option (J × List Nat)
  | 0, _, _, _, _ => none
  | n + 1, d, ks, vs, s =>
    match skipWs s with
    | c :: r =>
      if c = 34 then
        match rsF (r.length + 1) [] r with
        | none => none
        | some (k, r2) =>
          match skipWs r2 with
          | c2 :: r3 =>
            if c2 = 58 then
              match rv n d r3 with
              | none => none
              | some (v, r4) =>
                match skipWs r4 with
                | c3 :: r5 =>
                  if c3 = 125 then some (.obj (ks ++ [k]) (vs ++ [v]), r5)
                  else if c3 = 44 then roL n d (ks ++ [k]) (vs ++ [v]) r5 else none
                | [] => none
            else none
          | [] => none
      else none
    | [] => none
end

/-- parse：读一个值，后面只能有空白。燃料给 4 * (长度 + 1) -/
def parse (s : List Nat) : Option J :=
  match rv (4 * (s.length + 1)) 0 s with
  | none => none
  | some (v, r) => if skipWs r = [] then some v else none

-- [1,"a",{"k":null},true] 读回来再写出去不变；空白会被跳过；[1,] 和 [1 2] 是错误。
-- 互相递归的定义 Lean 编译成良基递归，decide 展不开，这几个例子用 #guard 跑编译出来的代码（只是检查，不进证明）
#guard (parse [91, 49, 44, 34, 97, 34, 44, 123, 34, 107, 34, 58, 110, 117, 108, 108, 125, 44,
    116, 114, 117, 101, 93]).map fmt ==
    some [91, 49, 44, 34, 97, 34, 44, 123, 34, 107, 34, 58, 110, 117, 108, 108, 125, 44, 116, 114, 117, 101, 93]
#guard (parse [32, 91, 32, 49, 32, 44, 50, 93, 10]).map fmt == some [91, 49, 44, 50, 93]
#guard (parse [91, 49, 44, 93]).isNone
#guard (parse [91, 49, 32, 50, 93]).isNone

/-! ## 一个数：写出来再读回去 -/

theorem skipWs_ne {c : Nat} (r : List Nat) (h : ¬(c = 32 ∨ c = 9 ∨ c = 10 ∨ c = 13)) : skipWs (c :: r) = c :: r := by
  rw [skipWs, ite_eq_right h]

theorem take_app' : ∀ (t rest : List Nat), (t ++ rest).take ((t ++ rest).length - rest.length) = t
  | t, rest => by
    have : (t ++ rest).length - rest.length = t.length := by simp
    rw [this]
    simp

theorem readNum_int (n : Int) (rest : List Nat) (hr : Stop rest) (h1 : -9223372036854775808 ≤ n)
    (h2 : n < 9223372036854775808) : readNum (intText n ++ rest) = some (.num n, rest) := by
  unfold readNum
  rw [scan_int n rest hr]
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [int_roundtrip n h1 h2]

theorem readNum_flt {t rest : List Nat} (ht : FloatText t) (hr : Stop rest) :
    readNum (t ++ rest) = some (.flt t, rest) := by
  obtain ⟨neg, ds, h⟩ := scan_float ht hr
  unfold readNum
  rw [h]
  simp only [↓reduceIte]
  rw [take_app']

/-! ## 单个的值：写出来再读回去 -/

/-- read_value 看第一个字节分派：开头不是空白时展开一步 -/
theorem rv_head {n d c : Nat} {r : List Nat} (hw : ¬(c = 32 ∨ c = 9 ∨ c = 10 ∨ c = 13)) (h91 : ¬ c = 91)
    (h123 : ¬ c = 123) (h34 : ¬ c = 34) :
    rv (n + 1) d (c :: r) =
      if c = 45 ∨ (48 ≤ c ∧ c ≤ 57) then readNum (c :: r)
      else if (c :: r).take 4 = [116, 114, 117, 101] then some (.bool true, (c :: r).drop 4)
      else if (c :: r).take 5 = [102, 97, 108, 115, 101] then some (.bool false, (c :: r).drop 5)
      else if (c :: r).take 4 = [110, 117, 108, 108] then some (.null, (c :: r).drop 4)
      else none := by
  rw [rv, skipWs_ne r hw]
  show (if c = 91 then _ else _) = _
  rw [ite_eq_right h91, ite_eq_right h123, ite_eq_right h34]

theorem rv_q {n d c : Nat} {r : List Nat} (hc : c = 34) :
    rv (n + 1) d (c :: r) =
      match rsF (r.length + 1) [] r with
      | none => none
      | some (x, r') => some (.str x, r') := by
  have hw : ¬(c = 32 ∨ c = 9 ∨ c = 10 ∨ c = 13) := by omega
  rw [rv, skipWs_ne r hw]
  show (if c = 91 then _ else _) = _
  rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left hc]

theorem numlike {n d c : Nat} {r : List Nat} (hc : c = 45 ∨ (48 ≤ c ∧ c ≤ 57)) :
    rv (n + 1) d (c :: r) = readNum (c :: r) := by
  rw [rv_head (by omega) (by omega) (by omega) (by omega), ite_eq_left hc]

theorem intText_head (k : Int) (rest : List Nat) :
    ∃ c r, intText k ++ rest = c :: r ∧ (c = 45 ∨ (48 ≤ c ∧ c ≤ 57)) := by
  unfold intText
  by_cases hn : k < 0
  · rw [ite_eq_left hn]
    exact ⟨45, _, rfl, Or.inl rfl⟩
  · rw [ite_eq_right hn, List.nil_append]
    have hd : Digits (dec k.natAbs) := (dec_ok (k.natAbs + 1) k.natAbs (by omega)).1
    have hne : dec k.natAbs ≠ [] := decF_ne (k.natAbs + 1) k.natAbs (by omega)
    obtain ⟨x, xs, hx⟩ := List.exists_cons_of_ne_nil hne
    refine ⟨x, xs ++ rest, by simp [hx], Or.inr (hd x ?_)⟩
    rw [hx]
    exact List.mem_cons_self ..

theorem floatText_head {t : List Nat} (ht : FloatText t) (rest : List Nat) :
    ∃ c r, t ++ rest = c :: r ∧ (c = 45 ∨ (48 ≤ c ∧ c ≤ 57)) := by
  obtain ⟨neg, ds, fr, ex, rfl, hne, hd, -⟩ := ht
  cases neg
  · obtain ⟨x, xs, hx⟩ := List.exists_cons_of_ne_nil hne
    refine ⟨x, xs ++ (fr ++ ex) ++ rest, by subst hx; simp, Or.inr (hd x ?_)⟩
    rw [hx]
    exact List.mem_cons_self ..
  · exact ⟨45, ds ++ (fr ++ ex) ++ rest, by simp, Or.inl rfl⟩

theorem rv_num (n d : Nat) (k : Int) (rest : List Nat) (hr : Stop rest) (h1 : -9223372036854775808 ≤ k)
    (h2 : k < 9223372036854775808) : rv (n + 1) d (fmt (.num k) ++ rest) = some (.num k, rest) := by
  simp only [fmt]
  obtain ⟨c, r, hcr, hc⟩ := intText_head k rest
  rw [hcr, numlike hc, ← hcr, readNum_int k rest hr h1 h2]

theorem rv_flt (n d : Nat) {t : List Nat} (ht : FloatText t) (rest : List Nat) (hr : Stop rest) :
    rv (n + 1) d (fmt (.flt t) ++ rest) = some (.flt t, rest) := by
  simp only [fmt]
  obtain ⟨c, r, hcr, hc⟩ := floatText_head ht rest
  rw [hcr, numlike hc, ← hcr, readNum_flt ht hr]

theorem escB_len (b : Nat) : 1 ≤ (escB b).length := by
  unfold escB
  (repeat' split) <;> simp

theorem escS_len : ∀ s : List Nat, s.length ≤ (escS s).length
  | [] => Nat.le_refl _
  | b :: s => by
    have h1 := escB_len b
    have h2 := escS_len s
    simp only [escS, List.length_append, List.length_cons]
    omega

theorem rv_str (n d : Nat) (s rest : List Nat) : rv (n + 1) d (fmt (.str s) ++ rest) = some (.str s, rest) := by
  have e : fmt (.str s) ++ rest = 34 :: (escS s ++ 34 :: rest) := by simp [fmt, quote]
  have hl : s.length < (escS s ++ 34 :: rest).length + 1 := by
    have := escS_len s
    simp only [List.length_append, List.length_cons]
    omega
  rw [e, rv_q rfl, rs_quote s [] rest _ hl]
  simp

theorem rv_null (n d : Nat) (rest : List Nat) : rv (n + 1) d (fmt .null ++ rest) = some (.null, rest) := by
  have e : fmt .null ++ rest = 110 :: (117 :: 108 :: 108 :: rest) := by simp [fmt]
  rw [e, rv_head (c := 110) (by decide) (by decide) (by decide) (by decide)]
  simp

theorem rv_bool (n d : Nat) (b : Bool) (rest : List Nat) : rv (n + 1) d (fmt (.bool b) ++ rest) = some (.bool b, rest) := by
  cases b
  · have e : fmt (.bool false) ++ rest = 102 :: (97 :: 108 :: 115 :: 101 :: rest) := by simp [fmt]
    rw [e, rv_head (c := 102) (by decide) (by decide) (by decide) (by decide)]
    simp
  · have e : fmt (.bool true) ++ rest = 116 :: (114 :: 117 :: 101 :: rest) := by simp [fmt]
    rw [e, rv_head (c := 116) (by decide) (by decide) (by decide) (by decide)]
    simp

/-! ## 数组：写出来再读回去

元素读回来这一条（H）先当前提，最后对 format 的长度归纳时再给。燃料：一个值写出来 L 个字节，2L + 2 就够。 -/

/-- format 写出来的值后面紧跟着的：结尾、, ] } -/
abbrev StopC (t : List Nat) : Prop := t = [] ∨ ∃ r, t = 44 :: r ∨ t = 93 :: r ∨ t = 125 :: r

theorem stopC_stop {t : List Nat} (h : StopC t) : Stop t := by
  rcases h with rfl | ⟨r, rfl | rfl | rfl⟩ <;> simp [Stop]

/-- 写出来的值的第一个字节：不是空白，也不是 ] } -/
abbrev Head (j : J) : Prop :=
  ∃ c r, fmt j = c :: r ∧ ¬(c = 32 ∨ c = 9 ∨ c = 10 ∨ c = 13) ∧ c ≠ 93 ∧ c ≠ 125

theorem rv_lb {n d c : Nat} {r : List Nat} (hc : c = 91) :
    rv (n + 1) d (c :: r) = if 512 ≤ d then none else ra n (d + 1) r := by
  have hw : ¬(c = 32 ∨ c = 9 ∨ c = 10 ∨ c = 13) := by omega
  rw [rv, skipWs_ne r hw]
  show (if c = 91 then _ else _) = _
  rw [ite_eq_left hc]

theorem ra_nil (m d : Nat) (rest : List Nat) : ra (m + 1) d (93 :: rest) = some (.arr [], rest) := by
  rw [ra, skipWs_ne (c := 93) rest (by decide)]
  simp

theorem ra_cons {m d c : Nat} {r : List Nat} (hw : ¬(c = 32 ∨ c = 9 ∨ c = 10 ∨ c = 13)) (h93 : c ≠ 93) :
    ra (m + 1) d (c :: r) = raL m d [] (c :: r) := by
  rw [ra, skipWs_ne r hw]
  show (if c = 93 then _ else _) = _
  rw [ite_eq_right h93]

theorem raL_step {m d : Nat} {acc : List J} {s : List Nat} {v : J} {r : List Nat} (h : rv m d s = some (v, r)) :
    raL (m + 1) d acc s =
      match skipWs r with
      | c :: r2 =>
        if c = 93 then some (.arr (acc ++ [v]), r2) else if c = 44 then raL m d (acc ++ [v]) r2 else none
      | [] => none := by
  (rw [raL, h]) <;> rfl

/-- 元素读回来时，read_arr 的循环读完整个数组 -/
theorem raL_fmt (d : Nat) (rest : List Nat) (hr : StopC rest) : ∀ (items acc : List J) (m : Nat), items ≠ [] →
    (∀ x ∈ items, ∀ m' t, StopC t → 2 * (fmt x).length + 2 ≤ m' → rv m' d (fmt x ++ t) = some (x, t)) →
    2 * (fmtA items).length + 3 ≤ m → raL m d acc (fmtA items ++ 93 :: rest) = some (.arr (acc ++ items), rest)
  | [], _, _, h, _, _ => absurd rfl h
  | [x], acc, m, _, H, hm => by
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    have e1 : fmtA [x] = fmt x := by simp [fmtA]
    rw [e1] at hm ⊢
    have hx := H x (List.mem_cons_self ..) m' (93 :: rest) (Or.inr ⟨rest, Or.inr (Or.inl rfl)⟩) (by omega)
    rw [raL_step hx, skipWs_ne (c := 93) rest (by decide)]
    simp
  | x :: y :: r, acc, m, _, H, hm => by
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    have e : fmtA (x :: y :: r) ++ 93 :: rest = fmt x ++ 44 :: (fmtA (y :: r) ++ 93 :: rest) := by simp [fmtA]
    have hl : (fmtA (x :: y :: r)).length = (fmt x).length + 1 + (fmtA (y :: r)).length := by
      simp [fmtA]
      omega
    have hx := H x (List.mem_cons_self ..) m' (44 :: (fmtA (y :: r) ++ 93 :: rest))
      (Or.inr ⟨_, Or.inl rfl⟩) (by omega)
    have hrec := raL_fmt d rest hr (y :: r) (acc ++ [x]) m' (by simp)
      (fun z hz => H z (List.mem_cons_of_mem _ hz)) (by omega)
    rw [e, raL_step hx, skipWs_ne (c := 44) _ (by decide)]
    simp [hrec]

theorem fmtA_head (x : J) (xs : List J) : ∃ u, fmtA (x :: xs) = fmt x ++ u := by
  cases xs with
  | nil => exact ⟨[], by simp [fmtA]⟩
  | cons y r => exact ⟨44 :: fmtA (y :: r), by simp [fmtA]⟩

/-- 元素都能读回来时，整个数组读回来 -/
theorem rv_arr {n d : Nat} (items : List J) (rest : List Nat) (hr : StopC rest) (hd : d < 512)
    (hh : ∀ x ∈ items, Head x)
    (H : ∀ x ∈ items, ∀ m' t, StopC t → 2 * (fmt x).length + 2 ≤ m' → rv m' (d + 1) (fmt x ++ t) = some (x, t))
    (hn : 2 * (fmt (.arr items)).length + 2 ≤ n) : rv n d (fmt (.arr items) ++ rest) = some (.arr items, rest) := by
  have e : fmt (.arr items) ++ rest = 91 :: (fmtA items ++ 93 :: rest) := by simp [fmt]
  have hl : (fmt (.arr items)).length = (fmtA items).length + 2 := by simp [fmt]
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 2 := ⟨n - 2, by omega⟩
  rw [e, rv_lb rfl, ite_eq_right (by omega)]
  cases items with
  | nil =>
    simp only [fmtA, List.nil_append]
    exact ra_nil n' (d + 1) rest
  | cons x xs =>
    obtain ⟨c, r, hcr, hw, h93, -⟩ := hh x (List.mem_cons_self ..)
    obtain ⟨u, hu⟩ := fmtA_head x xs
    have e2 : fmtA (x :: xs) ++ 93 :: rest = c :: (r ++ u ++ 93 :: rest) := by rw [hu, hcr]; simp
    rw [e2, ra_cons hw h93, ← e2, raL_fmt (d + 1) rest hr (x :: xs) [] n' (by simp) H (by omega)]
    simp

/-! ## 对象：写出来再读回去（值读回来这一条同样先当前提） -/

theorem rv_lc {n d c : Nat} {r : List Nat} (hc : c = 123) :
    rv (n + 1) d (c :: r) = if 512 ≤ d then none else ro n (d + 1) r := by
  have hw : ¬(c = 32 ∨ c = 9 ∨ c = 10 ∨ c = 13) := by omega
  rw [rv, skipWs_ne r hw]
  show (if c = 91 then _ else _) = _
  have h91 : ¬c = 91 := by omega
  rw [ite_eq_right h91, ite_eq_left hc]

theorem ro_nil (m d : Nat) (rest : List Nat) : ro (m + 1) d (125 :: rest) = some (.obj [] [], rest) := by
  rw [ro, skipWs_ne (c := 125) rest (by decide)]
  simp

theorem ro_q (m d : Nat) (r : List Nat) : ro (m + 1) d (34 :: r) = roL m d [] [] (34 :: r) := by
  rw [ro, skipWs_ne (c := 34) r (by decide)]
  simp

theorem roL_step {m d : Nat} {ks : List (List Nat)} {vs : List J} {r k r3 r4 : List Nat} {v : J}
    (hk : rsF (r.length + 1) [] r = some (k, 58 :: r3)) (hv : rv m d r3 = some (v, r4)) :
    roL (m + 1) d ks vs (34 :: r) =
      match skipWs r4 with
      | c3 :: r5 =>
        if c3 = 125 then some (.obj (ks ++ [k]) (vs ++ [v]), r5)
        else if c3 = 44 then roL m d (ks ++ [k]) (vs ++ [v]) r5 else none
      | [] => none := by
  rw [roL, skipWs_ne (c := 34) r (by decide)]
  simp only [↓reduceIte, hk, skipWs_ne (c := 58) r3 (by decide), hv]

theorem quote_rs (k X : List Nat) :
    rsF ((escS k ++ 34 :: X).length + 1) [] (escS k ++ 34 :: X) = some (k, X) := by
  have hl : k.length < (escS k ++ 34 :: X).length + 1 := by
    have := escS_len k
    simp only [List.length_append, List.length_cons]
    omega
  rw [rs_quote k [] X _ hl, List.nil_append]

theorem roL_fmt (d : Nat) (rest : List Nat) : ∀ (ks : List (List Nat)) (vs : List J)
    (accK : List (List Nat)) (accV : List J) (m : Nat), ks ≠ [] → ks.length = vs.length →
    (∀ x ∈ vs, ∀ m' t, StopC t → 2 * (fmt x).length + 2 ≤ m' → rv m' d (fmt x ++ t) = some (x, t)) →
    2 * (fmtO ks vs).length + 3 ≤ m →
    roL m d accK accV (fmtO ks vs ++ 125 :: rest) = some (.obj (accK ++ ks) (accV ++ vs), rest)
  | [], _, _, _, _, hne, _, _, _ => absurd rfl hne
  | _ :: _, [], _, _, _, _, hlen, _, _ => by simp only [List.length_cons, List.length_nil] at hlen <;> omega
  | [_], _ :: _ :: _, _, _, _, _, hlen, _, _ => by simp only [List.length_cons, List.length_nil] at hlen <;> omega
  | _ :: _ :: _, [_], _, _, _, _, hlen, _, _ => by simp only [List.length_cons, List.length_nil] at hlen <;> omega
  | [k], [v], accK, accV, m, _, _, H, hm => by
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    have e : fmtO [k] [v] ++ 125 :: rest = 34 :: (escS k ++ 34 :: (58 :: (fmt v ++ 125 :: rest))) := by
      simp [fmtO, quote]
    have hl : (fmtO [k] [v]).length = (escS k).length + 3 + (fmt v).length := by
      simp [fmtO, quote] <;> omega
    have hv := H v (List.mem_cons_self ..) m' (125 :: rest) (Or.inr ⟨rest, Or.inr (Or.inr rfl)⟩) (by omega)
    rw [e, roL_step (quote_rs k _) hv, skipWs_ne (c := 125) rest (by decide)]
    simp
  | k :: k2 :: ks, v :: v2 :: vs, accK, accV, m, _, hlen, H, hm => by
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    have e : fmtO (k :: k2 :: ks) (v :: v2 :: vs) ++ 125 :: rest =
        34 :: (escS k ++ 34 :: (58 :: (fmt v ++ 44 :: (fmtO (k2 :: ks) (v2 :: vs) ++ 125 :: rest)))) := by
      simp [fmtO, quote]
    have hl : (fmtO (k :: k2 :: ks) (v :: v2 :: vs)).length =
        (escS k).length + 3 + (fmt v).length + 1 + (fmtO (k2 :: ks) (v2 :: vs)).length := by
      simp [fmtO, quote] <;> omega
    have hv := H v (List.mem_cons_self ..) m' (44 :: (fmtO (k2 :: ks) (v2 :: vs) ++ 125 :: rest))
      (Or.inr ⟨_, Or.inl rfl⟩) (by omega)
    have hrec := roL_fmt d rest (k2 :: ks) (v2 :: vs) (accK ++ [k]) (accV ++ [v]) m' (by simp)
      (by simpa using hlen) (fun z hz => H z (List.mem_cons_of_mem _ hz)) (by omega)
    rw [e, roL_step (quote_rs k _) hv, skipWs_ne (c := 44) _ (by decide)]
    simp [hrec]

/-- 值都能读回来、键和值一样多时，整个对象读回来 -/
theorem rv_obj {n d : Nat} (ks : List (List Nat)) (vs : List J) (rest : List Nat) (hd : d < 512)
    (hlen : ks.length = vs.length)
    (H : ∀ x ∈ vs, ∀ m' t, StopC t → 2 * (fmt x).length + 2 ≤ m' → rv m' (d + 1) (fmt x ++ t) = some (x, t))
    (hn : 2 * (fmt (.obj ks vs)).length + 2 ≤ n) : rv n d (fmt (.obj ks vs) ++ rest) = some (.obj ks vs, rest) := by
  have e : fmt (.obj ks vs) ++ rest = 123 :: (fmtO ks vs ++ 125 :: rest) := by simp [fmt]
  have hl : (fmt (.obj ks vs)).length = (fmtO ks vs).length + 2 := by simp [fmt]
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 2 := ⟨n - 2, by omega⟩
  rw [e, rv_lc rfl, ite_eq_right (by omega)]
  cases ks with
  | nil =>
    simp only [fmtO, List.nil_append]
    have hv : vs = [] := by cases vs <;> simp_all
    subst hv
    exact ro_nil n' (d + 1) rest
  | cons k ks' =>
    cases vs with
    | nil => simp only [List.length_cons, List.length_nil] at hlen <;> omega
    | cons v vs' =>
      have hq : ∃ r, fmtO (k :: ks') (v :: vs') ++ 125 :: rest = 34 :: r := by
        cases ks' with
        | nil => exact ⟨escS k ++ 34 :: 58 :: (fmt v ++ 125 :: rest), by simp [fmtO, quote]⟩
        | cons k2 ks'' =>
          exact ⟨escS k ++ 34 :: 58 :: (fmt v ++ 44 :: (fmtO (k2 :: ks'') vs' ++ 125 :: rest)), by simp [fmtO, quote]⟩
      obtain ⟨r, hr⟩ := hq
      rw [hr, ro_q, ← hr, roL_fmt (d + 1) rest (k :: ks') (v :: vs') [] [] n' (by simp) hlen H (by omega)]
      all_goals simp

/-! ## 整个值：parse(format(j)) = j -/

/-- format 写出来能读回来的值：Int 在 64 位里，Float 的文字合乎 FloatText（不是 inf / nan），
嵌套不超过 512 层，对象的键和值一样多。d 是这个值在几层数组 / 对象里面 -/
inductive Good : Nat → J → Prop
  | null {d : Nat} : Good d .null
  | bool {d : Nat} (b : Bool) : Good d (.bool b)
  | num {d : Nat} (k : Int) (h1 : -9223372036854775808 ≤ k) (h2 : k < 9223372036854775808) : Good d (.num k)
  | flt {d : Nat} (t : List Nat) (h : FloatText t) : Good d (.flt t)
  | str {d : Nat} (s : List Nat) : Good d (.str s)
  | arr {d : Nat} (items : List J) (hd : d < 512) (h : ∀ x ∈ items, Good (d + 1) x) : Good d (.arr items)
  | obj {d : Nat} (ks : List (List Nat)) (vs : List J) (hd : d < 512) (hl : ks.length = vs.length)
      (h : ∀ x ∈ vs, Good (d + 1) x) : Good d (.obj ks vs)

theorem good_head {d : Nat} {j : J} (hg : Good d j) : Head j := by
  cases hg with
  | null => exact ⟨110, [117, 108, 108], by simp [fmt], by decide, by decide, by decide⟩
  | bool b =>
    cases b
    · exact ⟨102, [97, 108, 115, 101], by simp [fmt], by decide, by decide, by decide⟩
    · exact ⟨116, [114, 117, 101], by simp [fmt], by decide, by decide, by decide⟩
  | num k _ _ =>
    obtain ⟨c, r, h, hc⟩ := intText_head k []
    refine ⟨c, r, by simpa [fmt] using h, ?_, ?_, ?_⟩ <;> omega
  | flt t ht =>
    obtain ⟨c, r, h, hc⟩ := floatText_head ht []
    refine ⟨c, r, by simpa [fmt] using h, ?_, ?_, ?_⟩ <;> omega
  | str s => exact ⟨34, escS s ++ [34], by simp [fmt, quote], by decide, by decide, by decide⟩
  | arr items _ _ => exact ⟨91, fmtA items ++ [93], by simp [fmt], by decide, by decide, by decide⟩
  | obj ks vs _ _ _ => exact ⟨123, fmtO ks vs ++ [125], by simp [fmt], by decide, by decide, by decide⟩

/-- 写出来的值后面跟着结尾或 , ] }，燃料至少 2L + 2 时，read_value 正好读回这个值 -/
theorem rv_fmt {d : Nat} {j : J} (hg : Good d j) : ∀ n t, StopC t → 2 * (fmt j).length + 2 ≤ n →
    rv n d (fmt j ++ t) = some (j, t) := by
  induction hg with
  | null =>
    intro n t _ hn
    obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
    exact rv_null n' _ t
  | bool b =>
    intro n t _ hn
    obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
    exact rv_bool n' _ b t
  | num k h1 h2 =>
    intro n t ht hn
    obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
    exact rv_num n' _ k t (stopC_stop ht) h1 h2
  | flt s hs =>
    intro n t ht hn
    obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
    exact rv_flt n' _ hs t (stopC_stop ht)
  | str s =>
    intro n t _ hn
    obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
    exact rv_str n' _ s t
  | arr items hd h ih =>
    intro n t ht hn
    exact rv_arr items t ht hd (fun x hx => good_head (h x hx)) ih hn
  | obj ks vs hd hl _ ih =>
    intro n t _ hn
    exact rv_obj ks vs t hd hl ih hn

/-- 最后的结论：format 写出来再 parse，得到原来的值 -/
theorem parse_format (j : J) (hg : Good 0 j) : parse (fmt j) = some j := by
  have h := rv_fmt hg (4 * ((fmt j).length + 1)) [] (Or.inl rfl) (by omega)
  rw [List.append_nil] at h
  unfold parse
  simp [h, skipWs]

end Json
end Lark
