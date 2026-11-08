/-
对拍：随机生成小程序，Lean 的检查和真编译器（build/lark1）各判一次，比较是否一致。用法见 difftest.sh。

loop、call 两套都是三个 [int] 变量 v0、v1、v2（开始时都有值），赋值右边是移走（v1）或新列表（[整数]），
整数是常数、len(v)（借来读）和加法，语句有赋值、if、for { }、break、continue：
- loop：只有这些，Lean 那边用 Loop.lean 的 chkL（证过的检查）。
- call：再加上两个参数的调用（每个参数是只读、inout 或 take）和借用的 for e in v { }。
  Lean 那边用下面的 chkC：Loop.lean 的 chkL，加上 Call.lean 的排他性（Excl）、Drop.lean 的冻结（chkD 的 bor）。
  chkC 本身是这几块拼起来的，没有单独证。
- clo：借来的闭包（times(k, |i| …)）和 Fn 闭包（f0: Fn(int) -> int = |n| …），闭包体读或者移走捕获的变量，
  Lean 那边直接用 Clo.lean 证过的 chk。
- defer：块里的声明、defer { 读 v }、赋值、读、if、for { }、break、continue、return，
  Lean 那边直接用 Exit.lean 证过的 chk（声明和 defer 在块里往后都有效，所以生成时写成嵌套）。
每个程序写成一个文件，第一行是 Lean 的判断：// lean: ok 或 // lean: err。
-/
import Lark.Loop
import Lark.Call
import Lark.Exit
import Lark.Clo

open Lark

/-- 线性同余的伪随机数：返回 [0, k) 里的一个数和新的种子 -/
def rnd (s k : Nat) : Nat × Nat :=
  let s' := (s * 1103515245 + 12345) % 2147483648
  ((s' / 65536) % k, s')

def genI0 (s : Nat) : Expr × Nat :=
  let (c, s) := rnd s 2
  if c = 0 then
    let (k, s) := rnd s 4
    (.num (Int.ofNat k), s)
  else
    let (x, s) := rnd s 3
    (.peek x, s)

def genI : Nat → Nat → Expr × Nat
  | 0, s => genI0 s
  | d + 1, s =>
    let (c, s) := rnd s 3
    if c = 2 then
      let (a, s) := genI d s
      let (b, s) := genI d s
      (.add a b, s)
    else genI0 s

def genB (s : Nat) : Expr × Nat :=
  let (c, s) := rnd s 2
  if c = 0 then
    let (x, s) := rnd s 3
    (.move x, s)
  else
    let (e, s) := genI 1 s
    (.mk e, s)

def genLeaf (inLoop : Bool) (s : Nat) : LStmt × Nat :=
  let (c, s) := rnd s (if inLoop then 6 else 4)
  if c < 3 then
    let (x, s) := rnd s 3
    let (e, s) := genB s
    (.assign x e, s)
  else if c = 3 then (.skip, s)
  else if c = 4 then (.brk, s)
  else (.cont, s)

def genS : Nat → Bool → Nat → LStmt × Nat
  | 0, inLoop, s => genLeaf inLoop s
  | d + 1, inLoop, s =>
    let (c, s) := rnd s 8
    if c < 3 then genLeaf inLoop s
    else if c < 5 then
      let (a, s) := genS d inLoop s
      let (b, s) := genS d inLoop s
      (.seq a b, s)
    else if c = 5 then
      let (e, s) := genI 1 s
      let (a, s) := genS d inLoop s
      let (b, s) := genS d inLoop s
      (.ite e a b, s)
    else if c = 6 then
      let (b, s) := genS d true s
      (.loop b, s)
    else
      let (a, s) := genS d inLoop s
      let (b, s) := genS d inLoop s
      (.seq a b, s)

def genProg (s : Nat) : LStmt × Nat :=
  let (a, s) := genS 3 false s
  let (b, s) := genS 3 false s
  let (c, s) := genS 3 false s
  (.seq a (.seq b c), s)

def showI : Expr → String
  | .num n => toString n
  | .peek x => "len(v" ++ toString x ++ ")"
  | .add a b => "(" ++ showI a ++ " + " ++ showI b ++ ")"
  | _ => "0"

def showB : Expr → String
  | .move x => "v" ++ toString x
  | .mk e => "[" ++ showI e ++ "]"
  | _ => "[]"

def showS (ind : String) : LStmt → String
  | .skip => ""
  | .assign x e => ind ++ "v" ++ toString x ++ " = " ++ showB e ++ "\n"
  | .seq a b => showS ind a ++ showS ind b
  | .ite c a b =>
    ind ++ "if " ++ showI c ++ " != 0 {\n" ++ showS (ind ++ "    ") a ++
      ind ++ "} else {\n" ++ showS (ind ++ "    ") b ++ ind ++ "}\n"
  | .brk => ind ++ "break\n"
  | .cont => ind ++ "continue\n"
  | .loop b => ind ++ "for {\n" ++ showS (ind ++ "    ") b ++ ind ++ "}\n"

def render (p : LStmt) (ok : Bool) : String :=
  "// lean: " ++ (if ok then "ok" else "err") ++ "\n" ++
  "fn main() {\n    v0 = [0]\n    v1 = [1]\n    v2 = [2]\n" ++ showS "    " p ++ "}\n"

def pad (i : Nat) : String :=
  let t := toString i
  String.ofList (List.replicate (5 - t.length) '0') ++ t

/-! ## call 这一套：调用和借用的 for -/

inductive CS where
  | skip
  | assign (x : Var) (e : Expr)
  | seq (a b : CS)
  | ite (c : Expr) (a b : CS)
  | brk
  | cont
  | loop (b : CS)
  | forIn (x : Var) (b : CS)
  | call (m1 : Mode) (x1 : Var) (m2 : Mode) (x2 : Var)
  deriving Repr

/-- 表达式：f 是冻结的变量（借用的 for 正在遍历），不能移走 -/
def chkX (f m : List Var) : Expr → Option (List Var)
  | .num _ => some m
  | .peek x => if x ∈ m then none else some m
  | .move x => if x ∈ m ∨ x ∈ f then none else some (x :: m)
  | .mk e => chkX f m e
  | .add a b =>
    match chkX f m a with
    | none => none
    | some m1 => chkX f m1 b
  | _ => none

/-- 一个实参：要有值；inout、take 的不能是冻结的 -/
def argOk (f m : List Var) (md : Mode) (x : Var) : Bool :=
  decide (x ∉ m) && (decide (md = .read) || decide (x ∉ f))

def loopOut (m : List Var) : Option Out → Option Out
  | none => none
  | some o =>
    if subF o.fall m && o.conts.all (fun c => sub c m) then
      some ⟨some (m ++ o.fall.getD [] ++ unionAll o.brks), [], []⟩
    else none

def chkC (f : List Var) : CS → List Var → Option Out
  | .skip, m => some ⟨some m, [], []⟩
  | .assign x e, m =>
    match chkX f m e with
    | none => none
    | some m1 => if x ∈ f then none else some ⟨some (m1.filter (fun y => y != x)), [], []⟩
  | .seq a b, m =>
    match chkC f a m with
    | none => none
    | some o1 =>
      match o1.fall with
      | none => some o1
      | some m1 =>
        match chkC f b m1 with
        | none => none
        | some o2 => some ⟨o2.fall, o1.brks ++ o2.brks, o1.conts ++ o2.conts⟩
  | .ite c a b, m =>
    match chkX f m c with
    | none => none
    | some m0 =>
      match chkC f a m0, chkC f b m0 with
      | some oa, some ob => some ⟨joinF oa.fall ob.fall, oa.brks ++ ob.brks, oa.conts ++ ob.conts⟩
      | _, _ => none
  | .brk, m => some ⟨none, [m], []⟩
  | .cont, m => some ⟨none, [], [m]⟩
  | .loop b, m => loopOut m (chkC f b m)
  -- 借用的 for：x 要有值，循环体里 x 冻结；循环体可能一次都不执行，规则和 loop 一样
  | .forIn x b, m => if x ∈ m then none else loopOut m (chkC (x :: f) b m)
  -- 排他性：两个实参是同一个变量时，两个都得是只读的
  | .call m1 x1 m2 x2, m =>
    if argOk f m m1 x1 && argOk f m m2 x2 && !(decide (x1 = x2) && !(decide (m1 = .read) && decide (m2 = .read))) then
      some ⟨some (m ++ (if m1 = .take then [x1] else []) ++ (if m2 = .take then [x2] else [])), [], []⟩
    else none

/-- 只读多一些（6/10），inout 3/10，take 1/10：take 一多，后面几乎全是“已经被移走”，判通过的程序太少 -/
def genMode (s : Nat) : Mode × Nat :=
  let (c, s) := rnd s 10
  (if c < 6 then .read else if c < 9 then .inout else .take, s)

def genCLeaf (inLoop : Bool) (s : Nat) : CS × Nat :=
  let (c, s) := rnd s (if inLoop then 8 else 6)
  if c < 3 then
    let (x, s) := rnd s 3
    let (e, s) := genB s
    (.assign x e, s)
  else if c < 5 then
    let (m1, s) := genMode s
    let (x1, s) := rnd s 3
    let (m2, s) := genMode s
    let (x2, s) := rnd s 3
    (.call m1 x1 m2 x2, s)
  else if c = 5 then (.skip, s)
  else if c = 6 then (.brk, s)
  else (.cont, s)

def genC : Nat → Bool → Nat → CS × Nat
  | 0, inLoop, s => genCLeaf inLoop s
  | d + 1, inLoop, s =>
    let (c, s) := rnd s 9
    if c < 3 then genCLeaf inLoop s
    else if c < 5 then
      let (a, s) := genC d inLoop s
      let (b, s) := genC d inLoop s
      (.seq a b, s)
    else if c = 5 then
      let (e, s) := genI 1 s
      let (a, s) := genC d inLoop s
      let (b, s) := genC d inLoop s
      (.ite e a b, s)
    else if c = 6 then
      let (b, s) := genC d true s
      (.loop b, s)
    else
      let (x, s) := rnd s 3
      let (b, s) := genC d true s
      (.forIn x b, s)

def genCProg (s : Nat) : CS × Nat :=
  let (a, s) := genC 3 false s
  let (b, s) := genC 3 false s
  let (c, s) := genC 3 false s
  (.seq a (.seq b c), s)

def modeCh : Mode → String
  | .read => "r"
  | .inout => "i"
  | .take => "t"

def showArg (md : Mode) (x : Var) : String :=
  (if md = .inout then "&v" else "v") ++ toString x

def showC (ind : String) (d : Nat) : CS → String
  | .skip => ""
  | .assign x e => ind ++ "v" ++ toString x ++ " = " ++ showB e ++ "\n"
  | .seq a b => showC ind d a ++ showC ind d b
  | .ite c a b =>
    ind ++ "if " ++ showI c ++ " != 0 {\n" ++ showC (ind ++ "    ") d a ++
      ind ++ "} else {\n" ++ showC (ind ++ "    ") d b ++ ind ++ "}\n"
  | .brk => ind ++ "break\n"
  | .cont => ind ++ "continue\n"
  | .loop b => ind ++ "for {\n" ++ showC (ind ++ "    ") d b ++ ind ++ "}\n"
  | .forIn x b =>
    ind ++ "for e" ++ toString d ++ " in v" ++ toString x ++ " {\n" ++ showC (ind ++ "    ") (d + 1) b ++ ind ++ "}\n"
  | .call m1 x1 m2 x2 =>
    ind ++ "f_" ++ modeCh m1 ++ modeCh m2 ++ "(" ++ showArg m1 x1 ++ ", " ++ showArg m2 x2 ++ ")\n"

def param (md : Mode) (nm : String) : String :=
  (if md = .inout then "inout " else if md = .take then "take " else "") ++ nm ++ ": [int]"

def useParam (md : Mode) (nm : String) : String :=
  if md = .inout then "    " ++ nm ++ ".push(1)\n" else "    print(\"#{len(" ++ nm ++ ")}\")\n"

def modes : List Mode := [.read, .inout, .take]

/-- 九个两参数的函数 f_rr、f_ri、……、f_tt -/
def prelude : String :=
  String.join (modes.flatMap fun m1 => modes.map fun m2 =>
    "fn f_" ++ modeCh m1 ++ modeCh m2 ++ "(" ++ param m1 "a" ++ ", " ++ param m2 "b" ++ ") {\n" ++
      useParam m1 "a" ++ useParam m2 "b" ++ "}\n\n")

def renderC (p : CS) (ok : Bool) : String :=
  "// lean: " ++ (if ok then "ok" else "err") ++ "\n" ++ prelude ++
  "fn main() {\n    v0 = [0]\n    v1 = [1]\n    v2 = [2]\n" ++ showC "    " 1 p ++ "}\n"

/-! ## defer 这一套：直接用 Exit.lean 的 chk -/

def pick (l : List Var) (s : Nat) : Var × Nat :=
  let (i, s) := rnd s l.length
  (l.getD i 0, s)

/-- 声明用一个现在不在作用域里的名字（不遮蔽外层的变量） -/
def fresh (sc : List Var) : Option Var :=
  [0, 1, 2, 3, 4, 5].find? (fun x => !decide (x ∈ sc))

def genO (sc : List Var) (s : Nat) : Exit.OE × Nat :=
  let (c, s) := rnd s 2
  if c = 0 ∧ sc ≠ [] then
    let (y, s) := pick sc s
    (.move y, s)
  else (.mk, s)

/-- 一个块剩下的 k 条：f 是燃料（保证终止），d 是还能嵌套几层，sc 是作用域里的变量 -/
def genE : Nat → Nat → List Var → Bool → Nat → Nat → Exit.St × Nat
  | 0, _, _, _, _, s => (.skip, s)
  | _ + 1, _, _, _, 0, s => (.skip, s)
  | f + 1, d, sc, inLoop, k + 1, s =>
    let (c, s) := rnd s 12
    if c < 2 then
      match fresh sc with
      | some x =>
        let (o, s) := genO sc s
        let (r, s) := genE f d (x :: sc) inLoop k s
        (.decl x o r, s)
      | none => genE f d sc inLoop k s
    else if c < 4 ∧ sc ≠ [] then
      let (x, s) := pick sc s
      let (r, s) := genE f d sc inLoop k s
      (.defer x r, s)
    else
      let (c2, s) := rnd s 10
      let (it, s) :=
        if c2 < 2 ∧ sc ≠ [] then
          let (x, s) := pick sc s
          (Exit.St.use x, s)
        else if c2 < 4 ∧ sc ≠ [] then
          let (x, s) := pick sc s
          let (o, s) := genO sc s
          (Exit.St.assign x o, s)
        else if c2 = 4 ∧ d > 0 then
          let (b, s) := rnd s 2
          let (n1, s) := rnd s 3
          let (a, s) := genE f (d - 1) sc inLoop (n1 + 1) s
          let (n2, s) := rnd s 3
          let (e, s) := genE f (d - 1) sc inLoop (n2 + 1) s
          (Exit.St.ite (b == 0) a e, s)
        else if c2 = 5 ∧ d > 0 then
          let (n1, s) := rnd s 4
          let (a, s) := genE f (d - 1) sc true (n1 + 1) s
          (Exit.St.loop a, s)
        else if c2 = 6 ∧ inLoop then (Exit.St.brk, s)
        else if c2 = 7 ∧ inLoop then (Exit.St.cont, s)
        else if c2 = 8 then (Exit.St.ret, s)
        else (Exit.St.skip, s)
      let (r, s) := genE f d sc inLoop k s
      (.seq it r, s)

def showO : Exit.OE → String
  | .move y => "v" ++ toString y
  | .mk => "[1]"

def showE (ind : String) : Exit.St → String
  | .skip => ""
  | .use x => ind ++ "print(\"#{len(v" ++ toString x ++ ")}\")\n"
  | .assign x o => ind ++ "v" ++ toString x ++ " = " ++ showO o ++ "\n"
  | .seq a b => showE ind a ++ showE ind b
  | .ite b a c =>
    ind ++ "if " ++ (if b then "true" else "false") ++ " {\n" ++ showE (ind ++ "    ") a ++
      ind ++ "} else {\n" ++ showE (ind ++ "    ") c ++ ind ++ "}\n"
  | .brk => ind ++ "break\n"
  | .cont => ind ++ "continue\n"
  | .ret => ind ++ "return\n"
  | .loop b => ind ++ "for {\n" ++ showE (ind ++ "    ") b ++ ind ++ "}\n"
  | .decl x o r => ind ++ "v" ++ toString x ++ " = " ++ showO o ++ "\n" ++ showE ind r
  | .defer x r => ind ++ "defer { print(\"#{len(v" ++ toString x ++ ")}\") }\n" ++ showE ind r

def renderE (p : Exit.St) (ok : Bool) : String :=
  "// lean: " ++ (if ok then "ok" else "err") ++ "\n" ++ "fn main() {\n" ++ showE "    " p ++ "}\n"

/-! ## clo 这一套：直接用 Clo.lean 的 chk

Lark 在作用域结束时自动释放，Clo.lean 的程序要显式写 drop、dropFn。所以生成时跟着记一份状态（GS），
Lean 判断的是“生成的指令 + 最后把还活着的变量和闭包都释放掉”；释放那几条不写进 Lark 源码。
只在 Lark 里写得出来、而且不会因为别的原因出错的地方生成指令：变量先声明再用，
new 只给现在没有值的变量（Lark 里给有值的变量赋值也可以，但 Clo.lean 没有这种指令），闭包编号不重复。 -/

structure GS where
  F : List Var
  G : List Nat
  seen : List Var

def stepGS (g : GS) : Clo.Ins → GS
  | .new x => { g with F := x :: g.F, seen := if x ∈ g.seen then g.seen else x :: g.seen }
  | .mov y x => { g with F := y :: g.F.filter (fun z => z != x), seen := if y ∈ g.seen then g.seen else y :: g.seen }
  | .mkFn c _ _ => { g with G := c :: g.G }
  | _ => g

def genBody (s : Nat) : List Clo.BI × Nat :=
  let (c, s) := rnd s 4
  (if c = 0 then [.mv] else [.rd], s)

def genCI (g : GS) (s : Nat) : Clo.Ins × Nat :=
  let free := [0, 1, 2].filter (fun x => !decide (x ∈ g.F))
  let (c, s) := rnd s 10
  if (c < 2 ∨ g.seen = []) ∧ free ≠ [] then
    let (x, s) := pick free s
    (.new x, s)
  else if c < 4 then
    let (x, s) := pick g.seen s
    (.use x, s)
  else if c < 6 then
    let (x, s) := pick g.seen s
    let (y, s) := pick free s
    if free ≠ [] ∧ y ≠ x then (.mov y x, s) else (.use x, s)
  else if c < 8 then
    let (x, s) := pick g.seen s
    let (b, s) := genBody s
    (.mkFn g.G.length x b, s)
  else if c = 8 ∧ g.G ≠ [] then
    let (k, s) := pick g.G s
    (.call k, s)
  else
    let (x, s) := pick g.seen s
    let (b, s) := genBody s
    let (k, s) := rnd s 3
    (.apply x b k, s)

def genClo : Nat → GS → Nat → List Clo.Ins × GS × Nat
  | 0, g, s => ([], g, s)
  | n + 1, g, s =>
    let (i, s) := genCI g s
    let (rest, g', s) := genClo n (stepGS g i) s
    (i :: rest, g', s)

def vn (x : Var) : String := "v" ++ toString x

def showCI (ind : String) : Clo.Ins → String
  | .new x => ind ++ vn x ++ " = [1]\n"
  | .use x => ind ++ "print(\"#{len(" ++ vn x ++ ")}\")\n"
  | .mov y x => ind ++ vn y ++ " = " ++ vn x ++ "\n"
  | .mkFn c x b =>
    if b.any (fun i => match i with | .mv => true | _ => false) then
      ind ++ "f" ++ toString c ++ ": Fn(int) -> int = |n| {\n" ++ ind ++ "    w = " ++ vn x ++ "\n" ++
        ind ++ "    n + len(w)\n" ++ ind ++ "}\n"
    else ind ++ "f" ++ toString c ++ ": Fn(int) -> int = |n| n + len(" ++ vn x ++ ")\n"
  | .call c => ind ++ "print(\"#{f" ++ toString c ++ "(1)}\")\n"
  | .apply x b k =>
    if b.any (fun i => match i with | .mv => true | _ => false) then
      ind ++ "times(" ++ toString k ++ ", |i| {\n" ++ ind ++ "    w = " ++ vn x ++ "\n" ++
        ind ++ "    print(\"#{i + len(w)}\")\n" ++ ind ++ "})\n"
    else ind ++ "times(" ++ toString k ++ ", |i| print(\"#{i + len(" ++ vn x ++ ")}\"))\n"
  | _ => ""

def renderClo (p : List Clo.Ins) (ok : Bool) : String :=
  "// lean: " ++ (if ok then "ok" else "err") ++ "\n" ++
  "fn times(n: int, f: fn(int)) {\n    for i in 0..n { f(i) }\n}\n\n" ++
  "fn main() {\n" ++ String.join (p.map (showCI "    ")) ++ "}\n"

/-- lake env lean --run DiffGen.lean 个数 种子 目录 [loop|call|defer|clo] -/
def main (args : List String) : IO UInt32 := do
  let n := (args.getD 0 "300").toNat!
  let seed := (args.getD 1 "1").toNat!
  let dir := args.getD 2 "out"
  let kind := args.getD 3 "loop"
  IO.FS.createDirAll dir
  let mut s := seed
  let mut oks := 0
  for i in [0:n] do
    let (txt, ok, s') :=
      if kind = "clo" then
        let (len, s1) := rnd s 10
        let (p, g, s') := genClo (len + 6) ⟨[], [], []⟩ s1
        let cleanup := g.F.map Clo.Ins.drop ++ g.G.map Clo.Ins.dropFn
        let ok := Clo.chk [] [] (p ++ cleanup)
        (renderClo p ok, ok, s')
      else if kind = "defer" then
        let (p, s') := genE 60 3 [] false 8 s
        let ok := (Exit.chk [] [] p []).isSome
        (renderE p ok, ok, s')
      else if kind = "call" then
        let (p, s') := genCProg s
        let ok := (chkC [] p []).isSome
        (renderC p ok, ok, s')
      else
        let (p, s') := genProg s
        let ok := (chkL p []).isSome
        (render p ok, ok, s')
    s := s'
    if ok then oks := oks + 1
    IO.FS.writeFile (dir ++ "/c" ++ pad i ++ ".lark") txt
  IO.println s!"生成 {n} 个程序（{kind}），Lean 判定通过 {oks} 个"
  return 0
