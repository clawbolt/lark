/-
apps/llsp 的证明 · 阶段 2：JSON-RPC 的请求和回复、服务器的生命周期（LSP 规范的 “Lifecycle Messages”）
先证明，再写 apps/llsp/lsp/server.lark。

模型：客户端的消息（JSON 已经解析过）是请求（带 id 和 method，要回复）、通知（只有 method，不回复）、
客户端的回复（有 id、没有 method：服务器还没发过请求，丢掉）、不是请求的 JSON（回复 -32600，带上它的 id，没有时是 null），
或者读不出来的 JSON（回复 -32700，id 是 null）。
服务器的状态：还没 initialize、运行中、已 shutdown、已退出。规则（LSP 3.17）：
- initialize 之前：别的请求回复错误 -32002（ServerNotInitialized），通知丢掉（exit 除外）；
- 第二次 initialize：错误 -32600（InvalidRequest）；不认识的方法：-32601（MethodNotFound）；
- shutdown 之后：请求都回复 -32600，通知丢掉；
- exit：shutdown 过退出码 0，否则 1；退出以后什么都不处理；

证明了：
- `step_req`：没退出时，每个请求正好得到一条回复，id 对得上，并且这一步不会退出；
- `note_quiet`：通知从不得到回复；`exit_code`：退出码；`exited_stuck`：退出以后什么都不做；
- `uninit_guard`：initialize 之前别的请求都不处理；`shutdown_stays`：shutdown 以后不会再回到运行中；
- `run_replies`：一串消息处理下来，回复的 id 正好是 exit 之前各个请求（以及带 id 的不是请求的 JSON）的 id，按顺序、一个不多一个不少。
没证：JSON 本身的解析（用 std/json）、各个功能（悬停、诊断……）的内容。
-/

namespace Lark
namespace LspRpc

inductive St
  | uninit
  | running
  | shutdown
  | exited
deriving DecidableEq, Repr

/-- 客户端发来的消息。JSON-RPC 的 id 可以是数字或字符串，这里抽象成 Nat -/
inductive Msg
  | req (id : Nat) (m : String)
  | note (m : String)
  | bad
  | resp
  | invalid (id : Option Nat)
deriving DecidableEq, Repr

/-- 服务器发出的：成功的回复、错误的回复（id 可以是 null）、退出 -/
inductive Out
  | ok (id : Nat)
  | err (id : Option Nat) (code : Int)
  | exit (code : Nat)
deriving DecidableEq, Repr

def parseError : Int := -32700
def invalidRequest : Int := -32600
def methodNotFound : Int := -32601
def notInit : Int := -32002

/-- 一条输出是回复哪个请求的 -/
def replyTo : Out → Option Nat
  | .ok id => some id
  | .err id _ => id
  | .exit _ => none

/-- 处理一条消息。known：运行中认识的方法（悬停、补全……），它们一定成功回复 -/
def step (known : String → Bool) (s : St) (msg : Msg) : St × List Out :=
  if s = .exited then (.exited, []) else
  match msg with
  | .bad => (s, [.err none parseError])
  | .resp => (s, [])
  | .invalid id => (s, [.err id invalidRequest])
  | .note m => if m = "exit" then (.exited, [.exit (if s = .shutdown then 0 else 1)]) else (s, [])
  | .req id m =>
    match s with
    | .uninit => if m = "initialize" then (.running, [.ok id]) else (.uninit, [.err (some id) notInit])
    | .running =>
      if m = "initialize" then (.running, [.err (some id) invalidRequest])
      else if m = "shutdown" then (.shutdown, [.ok id])
      else if known m = true then (.running, [.ok id])
      else (.running, [.err (some id) methodNotFound])
    | .shutdown => (.shutdown, [.err (some id) invalidRequest])
    | .exited => (.exited, [])

def run (known : String → Bool) : St → List Msg → St × List Out
  | s, [] => (s, [])
  | s, m :: ms => ((run known (step known s m).1 ms).1, (step known s m).2 ++ (run known (step known s m).1 ms).2)

theorem step_req (k : String → Bool) (s : St) (id : Nat) (m : String) (h : s ≠ .exited) :
    (step k s (.req id m)).1 ≠ .exited ∧ (step k s (.req id m)).2.filterMap replyTo = [id] ∧
    (step k s (.req id m)).2.length = 1 := by
  cases s with
  | exited => exact absurd rfl h
  | uninit =>
    by_cases h1 : m = "initialize"
    · simp [step, h1, replyTo]
    · simp [step, h1, replyTo]
  | running =>
    by_cases h1 : m = "initialize"
    · simp [step, h1, replyTo]
    · by_cases h2 : m = "shutdown"
      · simp [step, h2, replyTo]
      · cases hk : k m
        · simp [step, h1, h2, hk, replyTo]
        · simp [step, h1, h2, hk, replyTo]
  | shutdown => simp [step, replyTo]

theorem note_quiet (k : String → Bool) (s : St) (m : String) : ∀ o ∈ (step k s (.note m)).2, replyTo o = none := by
  by_cases hs : s = .exited
  · simp [step, hs]
  · by_cases hm : m = "exit"
    · simp [step, hs, hm, replyTo]
    · simp [step, hs, hm]

theorem note_other (k : String → Bool) (s : St) (m : String) (h : s ≠ .exited) (hm : m ≠ "exit") :
    step k s (.note m) = (s, []) := by
  simp [step, h, hm]

theorem exit_code (k : String → Bool) (s : St) (h : s ≠ .exited) :
    step k s (.note "exit") = (.exited, [.exit (if s = .shutdown then 0 else 1)]) := by
  simp [step, h]

theorem bad_reply (k : String → Bool) (s : St) (h : s ≠ .exited) :
    step k s .bad = (s, [.err none parseError]) := by
  simp [step, h]

theorem resp_quiet (k : String → Bool) (s : St) (h : s ≠ .exited) : step k s .resp = (s, []) := by
  simp [step, h]

theorem invalid_reply (k : String → Bool) (s : St) (id : Option Nat) (h : s ≠ .exited) :
    step k s (.invalid id) = (s, [.err id invalidRequest]) := by
  simp [step, h]

theorem exited_stuck (k : String → Bool) (msg : Msg) : step k .exited msg = (.exited, []) := by
  simp [step]

theorem uninit_guard (k : String → Bool) (id : Nat) (m : String) (h : m ≠ "initialize") :
    step k .uninit (.req id m) = (.uninit, [.err (some id) notInit]) := by
  simp [step, h]

theorem shutdown_stays (k : String → Bool) (msg : Msg) :
    (step k .shutdown msg).1 = .shutdown ∨ (step k .shutdown msg).1 = .exited := by
  cases msg with
  | req id m => simp [step]
  | note m =>
    by_cases hm : m = "exit"
    · simp [step, hm]
    · simp [step, hm]
  | bad => simp [step]
  | resp => simp [step]
  | invalid id => simp [step]

theorem run_exited (k : String → Bool) : ∀ ms : List Msg, (run k .exited ms).2 = []
  | [] => rfl
  | m :: ms => by
    simp only [run, exited_stuck, List.nil_append]
    exact run_exited k ms

/-- exit 之前各个请求的 id（exit 以后的都不处理） -/
def before : List Msg → List Nat
  | [] => []
  | .req id _ :: ms => id :: before ms
  | .note m :: ms => if m = "exit" then [] else before ms
  | .bad :: ms => before ms
  | .resp :: ms => before ms
  | .invalid id :: ms => id.toList ++ before ms

theorem run_replies (k : String → Bool) : ∀ (ms : List Msg) (s : St), s ≠ .exited →
    (run k s ms).2.filterMap replyTo = before ms
  | [], _, _ => rfl
  | .req id m :: ms, s, h => by
    obtain ⟨h1, h2, _⟩ := step_req k s id m h
    simp only [run, List.filterMap_append, h2, run_replies k ms (step k s (.req id m)).1 h1, before,
      List.singleton_append]
  | .note m :: ms, s, h => by
    by_cases hm : m = "exit"
    · subst hm
      simp only [run, exit_code k s h, run_exited, before]
      simp [replyTo]
    · simp only [run, note_other k s m h hm, before, hm, ↓reduceIte, List.nil_append]
      exact run_replies k ms s h
  | .bad :: ms, s, h => by
    simp only [run, bad_reply k s h, before, List.filterMap_append]
    rw [run_replies k ms s h]
    simp [replyTo]
  | .resp :: ms, s, h => by
    simp only [run, resp_quiet k s h, before, List.nil_append]
    exact run_replies k ms s h
  | .invalid id :: ms, s, h => by
    simp only [run, invalid_reply k s id h, before, List.filterMap_append]
    rw [run_replies k ms s h]
    cases id <;> simp [replyTo]

/-! ## 例子：一次完整的会话 -/

def known (m : String) : Bool := m == "textDocument/hover"

def session : List Msg :=
  [.req 1 "textDocument/hover", .req 2 "initialize", .note "initialized", .req 3 "textDocument/hover",
   .req 4 "foo", .req 5 "initialize", .bad, .invalid (some 9), .resp, .req 6 "shutdown", .req 7 "textDocument/hover",
   .note "exit", .req 8 "textDocument/hover"]

#guard run known .uninit session ==
  (.exited, [.err (some 1) notInit, .ok 2, .ok 3, .err (some 4) methodNotFound, .err (some 5) invalidRequest,
    .err none parseError, .err (some 9) invalidRequest, .ok 6, .err (some 7) invalidRequest, .exit 0])
#guard before session == [1, 2, 3, 4, 5, 9, 6, 7]
-- 没有 shutdown 就 exit：退出码 1；initialize 之前的通知丢掉
#guard run known .uninit [.note "initialized", .note "exit"] == (.exited, [.exit 1])
#guard run known .uninit [.req 1 "initialize", .note "exit", .note "exit"] == (.exited, [.ok 1, .exit 1])

end LspRpc
end Lark
