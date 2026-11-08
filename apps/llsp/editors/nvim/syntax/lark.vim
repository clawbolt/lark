" Lark 的语法高亮（Vim / Neovim）。复制到 ~/.config/nvim/syntax/lark.vim（Vim 是 ~/.vim/syntax/lark.vim）。
" 规则和 compiler/lex.lark 一样：// 注释、"..." 字符串（#{...} 插值、\n \t \r \0 \e \xHH \\ \" \' \# 转义）、'a' 字符、
" 0x / 0o / 0b 整数、带 _ 分隔的数字。
if exists("b:current_syntax")
  finish
endif

syn keyword larkKeyword if else match for in return break continue select scope
syn keyword larkStorage pub take inout
syn keyword larkDecl fn type enum interface const nextgroup=larkDeclName skipwhite
syn keyword larkImport import
syn keyword larkBool true false
syn keyword larkVariant Some None Ok Err
syn keyword larkType int float u8 bool str Self
syn match larkType "\<Fn\ze\s*("
syn match larkKeyword "\<\(defer\|lock\)\ze\s*{"
syn match larkKeyword "\<\(after\|done\)\ze\s*("
syn match larkStorage "\<\(shared\|dyn\)\ze\s\+\h"
syn match larkStorage "^\s*\zsextern\>"
syn match larkTest "^\s*\zstest\ze\s\+\""

syn match larkDeclName "\h\w*" contained
syn match larkTypeName "\<\u\w*\>"
syn match larkConst "\<\u[A-Z0-9_]*[A-Z0-9]\>"
syn match larkCall "\<\l\w*\ze\s*("
syn match larkCall "\<_\w*\ze\s*("

syn match larkNumber "\<\d[0-9_]*\(\.\d[0-9_]*\)\=\([eE][+-]\=[0-9_]\+\)\=\>"
syn match larkNumber "\<0x[0-9a-fA-F_]\+\>"
syn match larkNumber "\<0o[0-7_]\+\>"
syn match larkNumber "\<0b[01_]\+\>"

syn match larkEscape "\\\([ntr0e\\\"'#]\|x\x\x\)" contained
syn region larkInterp matchgroup=larkInterpDelim start="#{" end="}" contained contains=TOP,larkInterpBraces
syn region larkInterpBraces start="{" end="}" contained transparent contains=TOP,larkInterpBraces
syn region larkString start=+"+ skip=+\\\\\|\\"+ end=+"+ contains=larkEscape,larkInterp
syn match larkChar "'\(\\\([ntr0e\\\"'#]\|x\x\x\)\|[^\\']\)'"

syn match larkComment "//.*$" contains=@Spell

hi def link larkKeyword Statement
hi def link larkStorage StorageClass
hi def link larkDecl Keyword
hi def link larkImport Include
hi def link larkTest Keyword
hi def link larkDeclName Function
hi def link larkBool Boolean
hi def link larkVariant Constant
hi def link larkType Type
hi def link larkTypeName Type
hi def link larkConst Constant
hi def link larkCall Function
hi def link larkNumber Number
hi def link larkString String
hi def link larkChar Character
hi def link larkEscape SpecialChar
hi def link larkInterpDelim Delimiter
hi def link larkComment Comment

let b:current_syntax = "lark"
