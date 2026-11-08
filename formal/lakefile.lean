import Lake
open Lake DSL

-- Lark 语言规则的形式化证明（见 ../design/soundness.md）。只用 Lean 4 自带的库，不依赖 Mathlib
package lark_formal

@[default_target]
lean_lib Lark

-- 对拍用的程序生成器（见 difftest.sh）
lean_exe difftest where
  root := `DiffGen
