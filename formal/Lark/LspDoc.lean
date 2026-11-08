/-
apps/llsp 的证明 · 阶段 3：打开的文档（LSP 规范的 “Document Synchronization”）
先证明，再写 apps/llsp/lsp/docs.lark。

模型：服务器记着编辑器打开的文档：uri → (版本, 内容)。三种通知：
- didOpen uri v t：记下（已经有时换掉）；
- didChange uri v cs：cs 是一串修改，按顺序作用（整个替换，或者把一个范围换成新文字，用阶段 1 的 Lsp.change）；
  版本必须比记着的大，否则丢掉（重复的、乱序的通知）；没打开的文档也丢掉；
- didClose uri：忘掉。
服务器在 initialize 的回复里说 textDocumentSync = { openClose: true, change: 2 }（增量），见 server.lark。

证明了：
- `open_get`、`close_get`：打开以后读到的就是打开时的内容，关掉以后读不到；
- `change_get`：版本更大时，内容是按顺序作用所有修改的结果；`change_stale`、`change_unknown`：别的情况什么都不变；
- `change_mono`：didChange 以后版本不会变小；
- `change_split`：一次通知里的一串修改 = 拆成两次通知（版本递增）发，内容一样（`applyAll_app`）；
- `step_other`、`run_other`：一个文档只被它自己的通知改变，别的文档不受影响；
- `applyAll_whole`：最后一处修改是整个替换时，内容就是新文字。
没证：JSON 里读出 uri、版本和修改（用 std/json）。
-/
import Lark.Lsp

namespace Lark
namespace LspDoc

/-- 打开的文档：(uri, 版本, 内容)。同一个 uri 只看第一个（put 会先删掉旧的） -/
abbrev Store := List (String × Nat × List Nat)

def get : Store → String → Option (Nat × List Nat)
  | [], _ => none
  | (k, v, t) :: s, u => if k = u then some (v, t) else get s u

def del : Store → String → Store
  | [], _ => []
  | (k, v, t) :: s, u => if k = u then del s u else (k, v, t) :: del s u

def put (s : Store) (u : String) (v : Nat) (t : List Nat) : Store := (u, v, t) :: del s u

theorem get_del_self (s : Store) (u : String) : get (del s u) u = none := by
  induction s with
  | nil => rfl
  | cons x s ih =>
    obtain ⟨k, v, t⟩ := x
    by_cases hk : k = u
    · simp [del, hk, ih]
    · simp [del, get, hk, ih]

theorem get_del_other (s : Store) (u u' : String) (h : u' ≠ u) : get (del s u) u' = get s u' := by
  induction s with
  | nil => rfl
  | cons x s ih =>
    obtain ⟨k, v, t⟩ := x
    by_cases hk : k = u
    · subst hk
      simp [del, get, Ne.symm h, ih]
    · simp [del, get, hk, ih]

theorem get_put_self (s : Store) (u : String) (v : Nat) (t : List Nat) : get (put s u v t) u = some (v, t) := by
  simp [put, get]

theorem get_put_other (s : Store) (u u' : String) (v : Nat) (t : List Nat) (h : u' ≠ u) :
    get (put s u v t) u' = get s u' := by
  simp only [put, get]
  rw [Lsp.iteF (Ne.symm h)]
  exact get_del_other s u u' h

/-! ## 修改：整个替换，或者把范围 [a, b) 换成 t（阶段 1 的 Lsp.change） -/

inductive Change
  | whole (t : List Nat)
  | range (a b : Nat × Nat) (t : List Nat)

def apply1 (un : List Nat → Nat) (d : List Nat) : Change → List Nat
  | .whole t => t
  | .range a b t => Lsp.change un d a b t

/-- 一次通知里的修改按顺序作用：后一处的位置是相对前一处改完以后的文档说的 -/
def applyAll (un : List Nat → Nat) : List Nat → List Change → List Nat
  | d, [] => d
  | d, c :: cs => applyAll un (apply1 un d c) cs

theorem applyAll_app (un : List Nat → Nat) : ∀ (d : List Nat) (cs ds : List Change),
    applyAll un d (cs ++ ds) = applyAll un (applyAll un d cs) ds
  | _, [], _ => rfl
  | d, c :: cs, ds => by
    simp only [List.cons_append, applyAll]
    exact applyAll_app un (apply1 un d c) cs ds

theorem applyAll_whole (un : List Nat → Nat) (d t : List Nat) (cs : List Change) :
    applyAll un d (cs ++ [.whole t]) = t := by
  rw [applyAll_app]
  rfl

/-! ## 通知 -/

inductive Ev
  | opn (uri : String) (v : Nat) (t : List Nat)
  | chg (uri : String) (v : Nat) (cs : List Change)
  | cls (uri : String)

def Ev.uri : Ev → String
  | .opn u _ _ => u
  | .chg u _ _ => u
  | .cls u => u

def step (un : List Nat → Nat) (s : Store) : Ev → Store
  | .opn uri v t => put s uri v t
  | .chg uri v cs =>
    match get s uri with
    | some (v0, d) => if v0 < v then put s uri v (applyAll un d cs) else s
    | none => s
  | .cls uri => del s uri

def run (un : List Nat → Nat) : Store → List Ev → Store
  | s, [] => s
  | s, e :: es => run un (step un s e) es

theorem open_get (un : List Nat → Nat) (s : Store) (uri : String) (v : Nat) (t : List Nat) :
    get (step un s (.opn uri v t)) uri = some (v, t) := by
  simp only [step, get_put_self]

theorem close_get (un : List Nat → Nat) (s : Store) (uri : String) : get (step un s (.cls uri)) uri = none := by
  simp only [step, get_del_self]

theorem change_get (un : List Nat → Nat) (s : Store) (uri : String) (v v0 : Nat) (d : List Nat) (cs : List Change)
    (h : get s uri = some (v0, d)) (hv : v0 < v) :
    get (step un s (.chg uri v cs)) uri = some (v, applyAll un d cs) := by
  simp only [step, h, hv, ↓reduceIte, get_put_self]

theorem change_stale (un : List Nat → Nat) (s : Store) (uri : String) (v v0 : Nat) (d : List Nat) (cs : List Change)
    (h : get s uri = some (v0, d)) (hv : ¬ v0 < v) : step un s (.chg uri v cs) = s := by
  simp only [step, h, hv, ↓reduceIte]

theorem change_unknown (un : List Nat → Nat) (s : Store) (uri : String) (v : Nat) (cs : List Change)
    (h : get s uri = none) : step un s (.chg uri v cs) = s := by
  simp only [step, h]

theorem change_mono (un : List Nat → Nat) (s : Store) (uri : String) (v v0 v1 : Nat) (d d' : List Nat)
    (cs : List Change) (h : get s uri = some (v0, d)) (h' : get (step un s (.chg uri v cs)) uri = some (v1, d')) :
    v0 ≤ v1 := by
  by_cases hv : v0 < v
  · rw [change_get un s uri v v0 d cs h hv] at h'
    cases h'
    omega
  · rw [change_stale un s uri v v0 d cs h hv, h] at h'
    cases h'
    omega

theorem change_split (un : List Nat → Nat) (s : Store) (uri : String) (v0 v1 v2 : Nat) (d : List Nat)
    (cs ds : List Change) (h : get s uri = some (v0, d)) (h1 : v0 < v1) (h2 : v1 < v2) :
    get (step un (step un s (.chg uri v1 cs)) (.chg uri v2 ds)) uri = get (step un s (.chg uri v2 (cs ++ ds))) uri := by
  have hm := change_get un s uri v1 v0 d cs h h1
  rw [change_get un _ uri v2 v1 _ ds hm h2, change_get un s uri v2 v0 d (cs ++ ds) h (by omega), applyAll_app]

theorem step_other (un : List Nat → Nat) (s : Store) (e : Ev) (uri' : String) (hne : uri' ≠ e.uri) :
    get (step un s e) uri' = get s uri' := by
  cases e with
  | opn uri v t =>
    simp only [step]
    exact get_put_other s uri uri' v t hne
  | cls uri =>
    simp only [step]
    exact get_del_other s uri uri' hne
  | chg uri v cs =>
    have hne' : uri' ≠ uri := hne
    simp only [step]
    cases hg : get s uri with
    | none => rfl
    | some p =>
      obtain ⟨v0, d⟩ := p
      by_cases hv : v0 < v
      · simp only [hv, ↓reduceIte]
        exact get_put_other s uri uri' v _ hne'
      · simp only [hv, ↓reduceIte]

theorem run_other (un : List Nat → Nat) (uri' : String) : ∀ (s : Store) (es : List Ev),
    (∀ e ∈ es, e.uri ≠ uri') → get (run un s es) uri' = get s uri'
  | _, [], _ => rfl
  | s, e :: es, h => by
    simp only [run]
    rw [run_other un uri' (step un s e) es (fun x hx => h x (by simp [hx]))]
    exact step_other un s e uri' (fun hh => h e (by simp) hh.symm)

/-! ## 例子 -/

def evs : List Ev :=
  [.opn "file:///a" 1 (Lsp.bs "ab"),
   .chg "file:///a" 2 [.range (0, 1) (0, 1) (Lsp.bs "x")],        -- axb
   .chg "file:///a" 2 [.whole (Lsp.bs "zzz")],                     -- 版本没变大：丢掉
   .chg "file:///b" 5 [.whole (Lsp.bs "q")],                       -- 没打开：丢掉
   .chg "file:///a" 3 [.range (0, 2) (0, 2) (Lsp.bs "y")],        -- axyb
   .opn "file:///b" 1 (Lsp.bs "c"),
   .cls "file:///b"]

#guard get (run Lsp.u16 [] evs) "file:///a" == some (3, Lsp.bs "axyb")
#guard get (run Lsp.u16 [] evs) "file:///b" == none
-- 一次通知里的两处修改：第二处的位置是相对第一处改完以后的文档
#guard applyAll Lsp.u16 (Lsp.bs "ab") [.whole (Lsp.bs "hello"), .range (0, 5) (0, 5) (Lsp.bs "!")] == Lsp.bs "hello!"
#guard applyAll Lsp.u16 (Lsp.bs "a\r\nb") [.range (0, 1) (1, 0) [], .range (0, 0) (0, 0) (Lsp.bs ">")] == Lsp.bs ">ab"

end LspDoc
end Lark
