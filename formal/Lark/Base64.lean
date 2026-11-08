/-
标准库的证明 · Base64（std/base64.lark）

照着 std/base64.lark 写一份：字节串和字符串都写成 List Nat，字母表写成下标和字符之间的换算（chr / val），
位运算写成算术：v >>> k & 63 是 v / 2^k % 64，(acc << 6) | v（v < 64）是 acc * 64 + v，& 0xFF_FFFF 是 % 2^24。
解码的错误信息不写，失败就是 none。

证明：解码的主循环（decLoop）吃完 enc 的输出（不补 =），一个字节不差地得到原来的数据，
而且剩下没凑够一个字节的位都是 0（`dl_body`）；加上外层的检查以后，`decode_encode`：decode(encode d) = Ok d，
`decode_url_encode_url`：decode_url(encode_url d) = Ok d（d 的每个元素都是字节）。
反方向：`decode_canonical`：decode(s) = Ok d 时 s = encode(d)，每段数据只有一种写法；
`decode_url_canonical`：decode_url(s) = Ok d 时 s 是 encode_url(d) 或者它补上 = 的写法。
-/

namespace Lark
namespace Base64

/-- 字母表：下标 v（< 64）对应的字符。STD 的 62、63 是 + /，URL 的是 - _ -/
def chr (url : Bool) (v : Nat) : Nat :=
  if v < 26 then 65 + v
  else if v < 52 then 71 + v
  else if v < 62 then v - 4
  else if v = 62 then (if url then 45 else 43)
  else if url then 95 else 47

/-- val：字符在字母表里的下标，不在里面时是 none（Lark 里是 -1） -/
def val (url : Bool) (c : Nat) : Option Nat :=
  if 65 ≤ c ∧ c ≤ 90 then some (c - 65)
  else if 97 ≤ c ∧ c ≤ 122 then some (c - 97 + 26)
  else if 48 ≤ c ∧ c ≤ 57 then some (c - 48 + 52)
  else if url then (if c = 45 then some 62 else if c = 95 then some 63 else none)
  else (if c = 43 then some 62 else if c = 47 then some 63 else none)

/-- enc：每 3 个字节出 4 个字符，最后剩 1 或 2 个字节时出 2 或 3 个字符，pad 时补 =（61） -/
def enc (url pad : Bool) : List Nat → List Nat
  | a :: b :: c :: r =>
    let v := a * 65536 + b * 256 + c
    [chr url (v / 262144 % 64), chr url (v / 4096 % 64), chr url (v / 64 % 64), chr url (v % 64)] ++ enc url pad r
  | [a, b] =>
    let v := a * 65536 + b * 256
    [chr url (v / 262144 % 64), chr url (v / 4096 % 64), chr url (v / 64 % 64)] ++ (if pad then [61] else [])
  | [a] =>
    let v := a * 65536
    [chr url (v / 262144 % 64), chr url (v / 4096 % 64)] ++ (if pad then [61, 61] else [])
  | [] => []

/-- acc = ((acc << 6) | v) & 0xFF_FFFF -/
def push (acc v : Nat) : Nat := (acc * 64 + v) % 16777216

/-- dec 里的 for 循环：每个字符放进 acc，凑够 8 位就出一个字节。返回 (acc, bits, out) -/
def decLoop (url : Bool) : List Nat → Nat → Nat → List Nat → Option (Nat × Nat × List Nat)
  | [], acc, bits, out => some (acc, bits, out)
  | c :: cs, acc, bits, out =>
    match val url c with
    | none => none
    | some v =>
      if 8 ≤ bits + 6 then decLoop url cs (push acc v) (bits + 6 - 8) (out ++ [push acc v / 2 ^ (bits + 6 - 8) % 256])
      else decLoop url cs (push acc v) (bits + 6) out

/-- 末尾 = 的个数 -/
def pads (s : List Nat) : Nat := (s.reverse.takeWhile (· == 61)).length

def dec (url : Bool) (s : List Nat) : Option (List Nat) :=
  let p := pads s
  let n := s.length - p
  if p > 2 then none
  else if n % 4 = 1 then none
  else if (!url || p != 0) && s.length % 4 != 0 then none
  else
    match decLoop url (s.take n) 0 0 [] with
    | none => none
    | some (acc, bits, out) => if acc % 2 ^ bits ≠ 0 then none else some out

/-! ## 例子：和 tests/unit/base64.lark 对上（"foo" = 102 111 111，"Zm9v" = 90 109 57 118） -/

example : enc false true [102, 111, 111] = [90, 109, 57, 118] := by decide
example : enc false true [102, 111] = [90, 109, 56, 61] := by decide
example : enc false true [102] = [90, 103, 61, 61] := by decide
example : enc true false [102] = [90, 103] := by decide
example : dec false [90, 109, 56, 61] = some [102, 111] := by decide
-- "Zm9="：最后一个字符多出来的位不是 0
example : dec false [90, 109, 57, 61] = none := by decide
-- 标准写法必须补 =，URL 写法补不补都行
example : dec false [90, 103] = none := by decide
example : dec true [90, 103] = some [102] := by decide
example : dec true [90, 103, 61, 61] = some [102] := by decide
example : dec false [90, 103, 61, 61, 61] = none := by decide

/-! ## 字母表：val 是 chr 的逆 -/

theorem val_chr_all (url : Bool) : ∀ v, v < 64 → val url (chr url v) = some v := by
  cases url <;> decide

theorem val_chr64 (url : Bool) (x : Nat) : val url (chr url (x % 64)) = some (x % 64) :=
  val_chr_all url _ (Nat.mod_lt _ (by decide))

/-! ## 循环的一步：bits 只会是 0、6、4、2 -/

theorem dl0 {url : Bool} {c v acc : Nat} {cs out : List Nat} (h : val url c = some v) :
    decLoop url (c :: cs) acc 0 out = decLoop url cs (push acc v) 6 out := by
  simp [decLoop, h, push]

theorem dl6 {url : Bool} {c v acc : Nat} {cs out : List Nat} (h : val url c = some v) :
    decLoop url (c :: cs) acc 6 out = decLoop url cs (push acc v) 4 (out ++ [push acc v / 16 % 256]) := by
  simp [decLoop, h, push]

theorem dl4 {url : Bool} {c v acc : Nat} {cs out : List Nat} (h : val url c = some v) :
    decLoop url (c :: cs) acc 4 out = decLoop url cs (push acc v) 2 (out ++ [push acc v / 4 % 256]) := by
  simp [decLoop, h, push]

theorem dl2 {url : Bool} {c v acc : Nat} {cs out : List Nat} (h : val url c = some v) :
    decLoop url (c :: cs) acc 2 out = decLoop url cs (push acc v) 0 (out ++ [push acc v % 256]) := by
  simp [decLoop, h, push]

/-! ## 一组 3 个字节、末尾的 2 个和 1 个字节 -/

def push4 (acc v : Nat) : Nat :=
  push (push (push (push acc (v / 262144 % 64)) (v / 4096 % 64)) (v / 64 % 64)) (v % 64)

theorem dl3 (url pad : Bool) {a b c : Nat} (r : List Nat) (acc : Nat) (out : List Nat)
    (ha : a < 256) (hb : b < 256) (hc : c < 256) :
    decLoop url (enc url pad (a :: b :: c :: r)) acc 0 out =
      decLoop url (enc url pad r) (push4 acc (a * 65536 + b * 256 + c)) 0 (out ++ [a, b, c]) := by
  simp only [enc, List.cons_append, List.nil_append]
  generalize hv : a * 65536 + b * 256 + c = v
  rw [dl0 (val_chr64 url _), dl6 (val_chr64 url _), dl4 (val_chr64 url _), dl2 (val_chr64 url _)]
  have e1 : push (push acc (v / 262144 % 64)) (v / 4096 % 64) / 16 % 256 = a := by
    unfold push; omega
  have e2 : push (push (push acc (v / 262144 % 64)) (v / 4096 % 64)) (v / 64 % 64) / 4 % 256 = b := by
    unfold push; omega
  have e3 : push (push (push (push acc (v / 262144 % 64)) (v / 4096 % 64)) (v / 64 % 64)) (v % 64) % 256 = c := by
    unfold push; omega
  rw [e1, e2, e3]
  simp only [push4, List.append_assoc, List.singleton_append]
  rfl

theorem dl_two (url : Bool) {a b : Nat} (acc : Nat) (out : List Nat) (ha : a < 256) (hb : b < 256) :
    ∃ acc', decLoop url (enc url false [a, b]) acc 0 out = some (acc', 2, out ++ [a, b]) ∧ acc' % 4 = 0 := by
  simp only [enc, Bool.false_eq_true, ↓reduceIte, List.append_nil]
  generalize hv : a * 65536 + b * 256 = v
  rw [dl0 (val_chr64 url _), dl6 (val_chr64 url _), dl4 (val_chr64 url _)]
  refine ⟨push (push (push acc (v / 262144 % 64)) (v / 4096 % 64)) (v / 64 % 64), ?_, by unfold push; omega⟩
  have e1 : push (push acc (v / 262144 % 64)) (v / 4096 % 64) / 16 % 256 = a := by
    unfold push; omega
  have e2 : push (push (push acc (v / 262144 % 64)) (v / 4096 % 64)) (v / 64 % 64) / 4 % 256 = b := by
    unfold push; omega
  rw [e1, e2]
  simp [decLoop]

theorem dl_one (url : Bool) {a : Nat} (acc : Nat) (out : List Nat) (ha : a < 256) :
    ∃ acc', decLoop url (enc url false [a]) acc 0 out = some (acc', 4, out ++ [a]) ∧ acc' % 16 = 0 := by
  simp only [enc, Bool.false_eq_true, ↓reduceIte, List.append_nil]
  generalize hv : a * 65536 = v
  rw [dl0 (val_chr64 url _), dl6 (val_chr64 url _)]
  refine ⟨push (push acc (v / 262144 % 64)) (v / 4096 % 64), ?_, by unfold push; omega⟩
  have e1 : push (push acc (v / 262144 % 64)) (v / 4096 % 64) / 16 % 256 = a := by
    unfold push; omega
  rw [e1]
  simp [decLoop]

/-- 主循环：吃完 enc 的输出（不补 =），out 后面正好接上原来的数据，剩下的位都是 0 -/
theorem dl_body (url : Bool) : ∀ (d : List Nat) (acc : Nat) (out : List Nat), (∀ x ∈ d, x < 256) →
    ∃ acc' bits', decLoop url (enc url false d) acc 0 out = some (acc', bits', out ++ d) ∧ acc' % 2 ^ bits' = 0
  | [], acc, out, _ => ⟨acc, 0, by simp [enc, decLoop], by rw [Nat.pow_zero, Nat.mod_one]⟩
  | [a], acc, out, h => by
    obtain ⟨acc', e, z⟩ := dl_one url acc out (h a (by simp))
    exact ⟨acc', 4, e, z⟩
  | [a, b], acc, out, h => by
    obtain ⟨acc', e, z⟩ := dl_two url acc out (h a (by simp)) (h b (by simp))
    exact ⟨acc', 2, e, z⟩
  | a :: b :: c :: r, acc, out, h => by
    obtain ⟨acc', bits', e, z⟩ := dl_body url r (push4 acc (a * 65536 + b * 256 + c)) (out ++ [a, b, c])
      (fun x hx => h x (by simp [hx]))
    refine ⟨acc', bits', ?_, z⟩
    rw [dl3 url false r acc out (h a (by simp)) (h b (by simp)) (h c (by simp)), e]
    simp

/-! ## 外层的检查：末尾的 =、长度、剩下的位 -/

/-- encode 补几个 =：剩 2 个字节补 1 个，剩 1 个补 2 个 -/
def padOf : List Nat → Nat
  | _ :: _ :: _ :: r => padOf r
  | [_, _] => 1
  | [_] => 2
  | [] => 0

theorem enc_pad (url : Bool) : ∀ d, enc url true d = enc url false d ++ List.replicate (padOf d) 61
  | [] => rfl
  | [_] => by simp [enc, padOf, List.replicate]
  | [_, _] => by simp [enc, padOf]
  | _ :: _ :: _ :: r => by simp [enc, padOf, enc_pad url r]

theorem chr_ne (url : Bool) (v : Nat) : chr url v ≠ 61 := by
  unfold chr; (repeat' split) <;> omega

/-- 字母表里没有 =，所以 enc 的输出里也没有 -/
theorem enc_no61 (url : Bool) : ∀ (d : List Nat), ∀ x ∈ enc url false d, x ≠ 61
  | [] => by simp [enc]
  | [_] => by
    intro x hx
    simp [enc] at hx
    rcases hx with rfl | rfl <;> exact chr_ne _ _
  | [_, _] => by
    intro x hx
    simp [enc] at hx
    rcases hx with rfl | rfl | rfl <;> exact chr_ne _ _
  | _ :: _ :: _ :: r => by
    intro x hx
    simp [enc] at hx
    rcases hx with rfl | rfl | rfl | rfl | hx <;> first | exact chr_ne _ _ | exact enc_no61 url r x hx

theorem enc_len (url : Bool) : ∀ d : List Nat,
    (enc url false d).length % 4 ≠ 1 ∧ ((enc url false d).length + padOf d) % 4 = 0 ∧ padOf d ≤ 2
  | [] => by simp [enc, padOf]
  | [_] => by simp [enc, padOf]
  | [_, _] => by simp [enc, padOf]
  | _ :: _ :: _ :: r => by
    have ih := enc_len url r
    simp only [enc, padOf, List.length_append, List.length_cons, List.length_nil]
    omega

theorem tw_rep (p : Nat) (l : List Nat) :
    (List.replicate p 61 ++ l).takeWhile (· == 61) = List.replicate p 61 ++ l.takeWhile (· == 61) := by
  induction p with
  | zero => simp
  | succ p ih => simp [List.replicate_succ, ih]

theorem tw_nil : ∀ (l : List Nat), (∀ x ∈ l, x ≠ 61) → l.takeWhile (· == 61) = []
  | [], _ => rfl
  | x :: _, h => by
    have hx : (x == 61) = false := by simp [h x (by simp)]
    simp [List.takeWhile, hx]

theorem pads_app (e : List Nat) (k : Nat) (h : ∀ x ∈ e, x ≠ 61) : pads (e ++ List.replicate k 61) = k := by
  unfold pads
  rw [List.reverse_append, List.reverse_replicate, tw_rep, tw_nil _ (fun x hx => h x (List.mem_reverse.mp hx))]
  simp

theorem take_app : ∀ (e r : List Nat), (e ++ r).take e.length = e
  | [], _ => rfl
  | x :: e, r => by simp [take_app e r]

/-- enc 的输出后面跟 k 个 =，长度检查通过时就能解回原来的数据 -/
theorem dec_ok (url : Bool) (d : List Nat) (k : Nat) (hd : ∀ x ∈ d, x < 256) (hk : k ≤ 2)
    (hlen : (!url || k != 0) = true → ((enc url false d).length + k) % 4 = 0) :
    dec url (enc url false d ++ List.replicate k 61) = some d := by
  have hp : pads (enc url false d ++ List.replicate k 61) = k := pads_app _ k (enc_no61 url d)
  obtain ⟨c2, _, _⟩ := enc_len url d
  obtain ⟨acc', bits', e, z⟩ := dl_body url d 0 [] hd
  have c1 : ¬ k > 2 := by omega
  have hn : (enc url false d ++ List.replicate k 61).length - k = (enc url false d).length := by simp
  have c3 : ((!url || k != 0) && (enc url false d ++ List.replicate k 61).length % 4 != 0) = false := by
    cases hb : (!url || k != 0)
    · rfl
    · have h4 := hlen hb
      simp [List.length_append, List.length_replicate, h4]
  simp only [dec, hp, hn, take_app, e, z, c1, c2, c3, Bool.false_eq_true, ↓reduceIte, ne_eq,
    not_true_eq_false, List.nil_append]

/-- base64.decode(base64.encode(d)) = Ok(d) -/
theorem decode_encode (d : List Nat) (hd : ∀ x ∈ d, x < 256) : dec false (enc false true d) = some d := by
  rw [enc_pad]
  obtain ⟨_, h2, h3⟩ := enc_len false d
  exact dec_ok false d (padOf d) hd h3 (fun _ => h2)

/-- base64.decode_url(base64.encode_url(d)) = Ok(d) -/
theorem decode_url_encode_url (d : List Nat) (hd : ∀ x ∈ d, x < 256) : dec true (enc true false d) = some d := by
  have h := dec_ok true d 0 hd (by omega) (by intro h; simp at h)
  simpa using h

/-! ## 反方向（一）：decode 接受的字符串只有一种写法。先是字母表和末尾的 = -/

/-- val 认出来的字符，chr 能换回去 -/
theorem chr_val {url : Bool} {c v : Nat} (h : val url c = some v) : v < 64 ∧ chr url v = c := by
  cases url <;> unfold val at h <;> (repeat' split at h) <;>
    first
    | (simp at h; done)
    | (obtain rfl := Option.some.inj h
       refine ⟨by omega, ?_⟩
       unfold chr
       (repeat' split) <;> first | omega | simp_all)

theorem tw_rep_self : ∀ l : List Nat,
    l.takeWhile (· == 61) = List.replicate (l.takeWhile (· == 61)).length 61
  | [] => rfl
  | x :: l => by
    by_cases hx : x = 61
    · subst hx
      have ih := tw_rep_self l
      simp only [List.takeWhile, beq_self_eq_true, List.length_cons, List.replicate_succ]
      rw [← ih]
    · have : (x == 61) = false := by simp [hx]
      simp [List.takeWhile, this]

theorem tw_dw : ∀ l : List Nat, l.takeWhile (· == 61) ++ l.dropWhile (· == 61) = l
  | [] => rfl
  | x :: l => by
    by_cases hx : x = 61
    · subst hx
      simp [List.takeWhile, List.dropWhile, tw_dw l]
    · have : (x == 61) = false := by simp [hx]
      simp [List.takeWhile, List.dropWhile, this]

/-- 去掉末尾的 = 以后，后面正好是 pads 个 = -/
theorem pads_split (s : List Nat) : s = s.take (s.length - pads s) ++ List.replicate (pads s) 61 := by
  have e := tw_dw s.reverse
  rw [tw_rep_self s.reverse] at e
  generalize s.reverse.dropWhile (· == 61) = u at e
  have e2 : s.reverse = List.replicate (pads s) 61 ++ u := e.symm
  have e3 : s = u.reverse ++ List.replicate (pads s) 61 := by
    have := congrArg List.reverse e2
    simpa [List.reverse_append] using this
  have hl : s.length - pads s = u.reverse.length := by
    have := congrArg List.length e3
    simp only [List.length_append, List.length_replicate, List.length_reverse] at this ⊢
    omega
  rw [hl]
  calc s = u.reverse ++ List.replicate (pads s) 61 := e3
    _ = (u.reverse ++ List.replicate (pads s) 61).take u.reverse.length ++ List.replicate (pads s) 61 := by
        rw [take_app]
    _ = s.take u.reverse.length ++ List.replicate (pads s) 61 := by rw [← e3]

/-! ## 反方向（二）：解码的主循环反过来 -/

theorem dl_some {url : Bool} {c acc bits : Nat} {cs out : List Nat} {res : Nat × Nat × List Nat}
    (h : decLoop url (c :: cs) acc bits out = some res) : ∃ v, val url c = some v := by
  cases hv : val url c with
  | none => simp [decLoop, hv] at h
  | some v => exact ⟨v, rfl⟩

/-- 4 个字符解出的 3 个字节，编码回去还是这 4 个字符 -/
theorem enc_c4 {url : Bool} {c1 c2 c3 c4 v1 v2 v3 v4 : Nat}
    (h1 : val url c1 = some v1) (h2 : val url c2 = some v2) (h3 : val url c3 = some v3)
    (h4 : val url c4 = some v4) (d : List Nat) :
    enc url false ((v1 * 4 + v2 / 16) :: (v2 % 16 * 16 + v3 / 4) :: (v3 % 4 * 64 + v4) :: d) =
      c1 :: c2 :: c3 :: c4 :: enc url false d := by
  obtain ⟨l1, e1⟩ := chr_val h1
  obtain ⟨l2, e2⟩ := chr_val h2
  obtain ⟨l3, e3⟩ := chr_val h3
  obtain ⟨l4, e4⟩ := chr_val h4
  simp only [enc, List.cons_append, List.nil_append]
  generalize hv : (v1 * 4 + v2 / 16) * 65536 + (v2 % 16 * 16 + v3 / 4) * 256 + (v3 % 4 * 64 + v4) = v
  have f1 : v / 262144 % 64 = v1 := by omega
  have f2 : v / 4096 % 64 = v2 := by omega
  have f3 : v / 64 % 64 = v3 := by omega
  have f4 : v % 64 = v4 := by omega
  rw [f1, f2, f3, f4, e1, e2, e3, e4]

/-- 末尾 3 个字符：最后一个字符的低 2 位是 0 时，编码回去还是这 3 个字符 -/
theorem enc_c3 {url : Bool} {c1 c2 c3 v1 v2 v3 : Nat}
    (h1 : val url c1 = some v1) (h2 : val url c2 = some v2) (h3 : val url c3 = some v3) (hz : v3 % 4 = 0) :
    enc url false [v1 * 4 + v2 / 16, v2 % 16 * 16 + v3 / 4] = [c1, c2, c3] := by
  obtain ⟨l1, e1⟩ := chr_val h1
  obtain ⟨l2, e2⟩ := chr_val h2
  obtain ⟨l3, e3⟩ := chr_val h3
  simp only [enc, Bool.false_eq_true, ↓reduceIte, List.append_nil]
  generalize hv : (v1 * 4 + v2 / 16) * 65536 + (v2 % 16 * 16 + v3 / 4) * 256 = v
  have f1 : v / 262144 % 64 = v1 := by omega
  have f2 : v / 4096 % 64 = v2 := by omega
  have f3 : v / 64 % 64 = v3 := by omega
  rw [f1, f2, f3, e1, e2, e3]

/-- 末尾 2 个字符：最后一个字符的低 4 位是 0 时，编码回去还是这 2 个字符 -/
theorem enc_c2 {url : Bool} {c1 c2 v1 v2 : Nat}
    (h1 : val url c1 = some v1) (h2 : val url c2 = some v2) (hz : v2 % 16 = 0) :
    enc url false [v1 * 4 + v2 / 16] = [c1, c2] := by
  obtain ⟨l1, e1⟩ := chr_val h1
  obtain ⟨l2, e2⟩ := chr_val h2
  simp only [enc, Bool.false_eq_true, ↓reduceIte, List.append_nil]
  generalize hv : (v1 * 4 + v2 / 16) * 65536 = v
  have f1 : v / 262144 % 64 = v1 := by omega
  have f2 : v / 4096 % 64 = v2 := by omega
  rw [f1, f2, e1, e2]

/-- 主循环吃完 cs、剩下的位是 0（长度除以 4 不余 1）时，cs 就是解出来的数据的编码（不补 =） -/
theorem dl_inv (url : Bool) : ∀ (cs : List Nat) (acc : Nat) (out : List Nat) (acc' bits' : Nat) (out' : List Nat),
    cs.length % 4 ≠ 1 → decLoop url cs acc 0 out = some (acc', bits', out') → acc' % 2 ^ bits' = 0 →
    ∃ d, out' = out ++ d ∧ cs = enc url false d ∧ (cs.length + padOf d) % 4 = 0
  | [], acc, out, acc', bits', out', _, h, _ => by
    simp only [decLoop, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨_, _, e⟩ := h
    exact ⟨[], by rw [← e, List.append_nil], rfl, rfl⟩
  | [_], _, _, _, _, _, hl, _, _ => by simp at hl
  | [c1, c2], acc, out, acc', bits', out', _, h, hz => by
    obtain ⟨v1, h1⟩ := dl_some h
    rw [dl0 h1] at h
    obtain ⟨v2, h2⟩ := dl_some h
    rw [dl6 h2] at h
    simp only [decLoop, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨ea, eb, eo⟩ := h
    subst ea eb eo
    obtain ⟨l1, _⟩ := chr_val h1
    obtain ⟨l2, _⟩ := chr_val h2
    have hz' : v2 % 16 = 0 := by
      have : (2:Nat) ^ 4 = 16 := rfl
      rw [this] at hz; unfold push at hz; omega
    have e1 : push (push acc v1) v2 / 16 % 256 = v1 * 4 + v2 / 16 := by unfold push; omega
    exact ⟨[v1 * 4 + v2 / 16], by rw [e1], (enc_c2 h1 h2 hz').symm, by simp [padOf]⟩
  | [c1, c2, c3], acc, out, acc', bits', out', _, h, hz => by
    obtain ⟨v1, h1⟩ := dl_some h
    rw [dl0 h1] at h
    obtain ⟨v2, h2⟩ := dl_some h
    rw [dl6 h2] at h
    obtain ⟨v3, h3⟩ := dl_some h
    rw [dl4 h3] at h
    simp only [decLoop, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨ea, eb, eo⟩ := h
    subst ea eb eo
    obtain ⟨l1, _⟩ := chr_val h1
    obtain ⟨l2, _⟩ := chr_val h2
    obtain ⟨l3, _⟩ := chr_val h3
    have hz' : v3 % 4 = 0 := by
      have : (2:Nat) ^ 2 = 4 := rfl
      rw [this] at hz; unfold push at hz; omega
    have e1 : push (push acc v1) v2 / 16 % 256 = v1 * 4 + v2 / 16 := by unfold push; omega
    have e2 : push (push (push acc v1) v2) v3 / 4 % 256 = v2 % 16 * 16 + v3 / 4 := by unfold push; omega
    exact ⟨[v1 * 4 + v2 / 16, v2 % 16 * 16 + v3 / 4], by simp [e1, e2], (enc_c3 h1 h2 h3 hz').symm, by simp [padOf]⟩
  | c1 :: c2 :: c3 :: c4 :: r, acc, out, acc', bits', out', hl, h, hz => by
    obtain ⟨v1, h1⟩ := dl_some h
    rw [dl0 h1] at h
    obtain ⟨v2, h2⟩ := dl_some h
    rw [dl6 h2] at h
    obtain ⟨v3, h3⟩ := dl_some h
    rw [dl4 h3] at h
    obtain ⟨v4, h4⟩ := dl_some h
    rw [dl2 h4] at h
    obtain ⟨l1, _⟩ := chr_val h1
    obtain ⟨l2, _⟩ := chr_val h2
    obtain ⟨l3, _⟩ := chr_val h3
    obtain ⟨l4, _⟩ := chr_val h4
    have e1 : push (push acc v1) v2 / 16 % 256 = v1 * 4 + v2 / 16 := by unfold push; omega
    have e2 : push (push (push acc v1) v2) v3 / 4 % 256 = v2 % 16 * 16 + v3 / 4 := by unfold push; omega
    have e3 : push (push (push (push acc v1) v2) v3) v4 % 256 = v3 % 4 * 64 + v4 := by unfold push; omega
    rw [e1, e2, e3] at h
    obtain ⟨d, ed, er, el⟩ := dl_inv url r _ _ acc' bits' out' (by simp at hl ⊢; omega) h hz
    refine ⟨(v1 * 4 + v2 / 16) :: (v2 % 16 * 16 + v3 / 4) :: (v3 % 4 * 64 + v4) :: d, ?_, ?_, ?_⟩
    · rw [ed]; simp
    · rw [enc_c4 h1 h2 h3 h4, ← er]
    · simp only [List.length_cons, padOf]; omega

/-! ## 反方向（三）：decode 接受的字符串就是 encode 的输出 -/

/-- dec 成功时，四项检查都通过了 -/
theorem dec_inv {url : Bool} {s d : List Nat} (h : dec url s = some d) :
    pads s ≤ 2 ∧ (s.length - pads s) % 4 ≠ 1 ∧ ((!url || pads s != 0) = true → s.length % 4 = 0) ∧
    ∃ acc bits, decLoop url (s.take (s.length - pads s)) 0 0 [] = some (acc, bits, d) ∧ acc % 2 ^ bits = 0 := by
  unfold dec at h
  by_cases c1 : pads s > 2
  · simp only [c1, ↓reduceIte, reduceCtorEq] at h
  by_cases c2 : (s.length - pads s) % 4 = 1
  · simp only [c1, c2, ↓reduceIte, reduceCtorEq] at h
  by_cases c3 : ((!url || pads s != 0) && s.length % 4 != 0) = true
  · simp only [c1, c2, c3, ↓reduceIte, reduceCtorEq] at h
  simp only [c1, c2, c3, ↓reduceIte] at h
  refine ⟨by omega, c2, ?_, ?_⟩
  · intro hb
    rw [hb, Bool.true_and] at c3
    simpa using c3
  · cases hd : decLoop url (s.take (s.length - pads s)) 0 0 [] with
    | none => rw [hd] at h; simp at h
    | some res =>
      obtain ⟨acc, bits, out⟩ := res
      rw [hd] at h
      by_cases hz : acc % 2 ^ bits = 0
      · simp [hz] at h
        exact ⟨acc, bits, by rw [h], hz⟩
      · simp [hz] at h

/-- 去掉 = 以后的部分，长度除以 4 不余 1 -/
theorem take_len {s : List Nat} (hn : (s.length - pads s) % 4 ≠ 1) :
    (s.take (s.length - pads s)).length % 4 ≠ 1 := by
  simp only [List.length_take]
  omega

theorem pads_len (s : List Nat) : s.length = (s.take (s.length - pads s)).length + pads s := by
  have hlen := congrArg List.length (pads_split s)
  simp only [List.length_append, List.length_replicate] at hlen
  exact hlen

/-- base64.decode(s) = Ok(d) 时，s 就是 base64.encode(d)：每段数据只有一种写法 -/
theorem decode_canonical {s d : List Nat} (h : dec false s = some d) : s = enc false true d := by
  obtain ⟨hp, hn, hl, acc, bits, e, z⟩ := dec_inv h
  have hl4 : s.length % 4 = 0 := hl (by simp)
  obtain ⟨d', ed, er, el⟩ := dl_inv false _ 0 [] acc bits d (take_len hn) e z
  simp only [List.nil_append] at ed
  rw [ed]
  have hlen := pads_len s
  obtain ⟨_, _, hpd⟩ := enc_len false d'
  have hpad : pads s = padOf d' := by omega
  rw [enc_pad, ← er, ← hpad]
  exact pads_split s

/-- base64.decode_url(s) = Ok(d) 时，s 是 base64.encode_url(d)，或者是它补上 = 的写法 -/
theorem decode_url_canonical {s d : List Nat} (h : dec true s = some d) :
    s = enc true false d ∨ s = enc true true d := by
  obtain ⟨hp, hn, hl, acc, bits, e, z⟩ := dec_inv h
  obtain ⟨d', ed, er, el⟩ := dl_inv true _ 0 [] acc bits d (take_len hn) e z
  simp only [List.nil_append] at ed
  rw [ed]
  by_cases h0 : pads s = 0
  · left
    rw [← er, h0]
    simp
  · right
    have hl4 : s.length % 4 = 0 := hl (by simp [h0])
    have hlen := pads_len s
    obtain ⟨_, _, hpd⟩ := enc_len true d'
    have hpad : pads s = padOf d' := by omega
    rw [enc_pad, ← er, ← hpad]
    exact pads_split s

end Base64
end Lark
