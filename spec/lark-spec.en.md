# The Lark Programming Language

<!-- txt
left: The Lark Project
left: Specification: LARK-0
left: Category: Experimental
right: Lark Contributors
right: November 2026
running: LARK-0|Lark Language|November 2026
footer: Lark Contributors|Experimental
-->

## Abstract

This document specifies Lark, a statically typed programming language with value semantics, ownership checking, and structured concurrency, which is compiled to C. It defines the lexical structure, the grammar, the type system, the ownership rules, the run-time behavior that programs can observe, and the safety guarantee that the static rules are intended to provide. Where a rule has been formally verified, the document names the Lean 4 theorem that covers it.

## Status of This Document

This document is not an Internet Standards Track specification and has not been reviewed by the IETF or by any other standards body. It is published by the Lark project for the information of people who write Lark programs or implement Lark tools. It uses the conventions of the RFC series [RFC7322] because they suit a precise, reviewable specification.

This is version 0 of the specification. It describes the language accepted by the reference compiler `lark1` (the files `compiler/*.lark` in the Lark repository) as of November 2026. Later versions will be published as new documents; this one will not be changed except to correct errors.

The language is experimental. The ownership rules have machine-checked soundness proofs for a core calculus (Section 24), but the compiler itself is not verified.

This document is published in English and in Chinese with the same content. Where the two versions differ, the English version prevails.

## Table of Contents

- [1. Introduction](#1-introduction)
- [2. Notation](#2-notation)
- [3. Lexical Structure](#3-lexical-structure)
- [4. Program Structure](#4-program-structure)
- [5. Types](#5-types)
- [6. Statements](#6-statements)
- [7. Expressions](#7-expressions)
- [8. Functions](#8-functions)
- [9. Ownership](#9-ownership)
- [10. Pattern Matching](#10-pattern-matching)
- [11. Loops](#11-loops)
- [12. Generics and Interfaces](#12-generics-and-interfaces)
- [13. Protocol Functions](#13-protocol-functions)
- [14. Closures](#14-closures)
- [15. Error Handling](#15-error-handling)
- [16. Modules and Visibility](#16-modules-and-visibility)
- [17. Concurrency](#17-concurrency)
- [18. Constants](#18-constants)
- [19. Tests](#19-tests)
- [20. Diagnostics](#20-diagnostics)
- [21. Built-in Functions](#21-built-in-functions)
- [22. Foreign Function Interface](#22-foreign-function-interface)
- [23. Implementation Requirements](#23-implementation-requirements)
- [24. Soundness and Formal Verification](#24-soundness-and-formal-verification)
- [25. Security Considerations](#25-security-considerations)
- [26. IANA Considerations](#26-iana-considerations)
- [27. References](#27-references)
- [Appendix A. Collected Grammar](#appendix-a-collected-grammar)
- [Appendix B. Known Deviations and Open Issues](#appendix-b-known-deviations-and-open-issues)

## 1. Introduction

### 1.1. Scope

This document defines which source texts are Lark programs and what those programs do when they run. It covers the language and the built-in functions that the compiler knows about. The standard library (`std/*.lark`) is written in Lark and is described in its own documentation; it is outside the scope of this document except where the language refers to it (for example, the `hash` protocol used by `std/map`).

The command-line interface of the reference tools is described only where it changes the meaning of a program (test builds, release builds, and package mapping).

### 1.2. Requirements Language

The key words "MUST", "MUST NOT", "REQUIRED", "SHALL", "SHALL NOT", "SHOULD", "SHOULD NOT", "RECOMMENDED", "NOT RECOMMENDED", "MAY", and "OPTIONAL" in this document are to be interpreted as described in BCP 14 [RFC2119] [RFC8174] when, and only when, they appear in all capitals, as shown here.

Requirements on programs ("a program MUST NOT ...") define which source texts are valid. Requirements on implementations ("an implementation MUST report an error") define how a conforming compiler treats valid and invalid programs.

### 1.3. Terminology

- **Program**: the set of source files given to the compiler, together with every file they import, directly or indirectly.
- **Implementation**: a compiler, together with its run-time support, that translates programs into executables.
- **Compile-time error**: a violation of a rule of this document that an implementation MUST detect before the program runs. An implementation MUST NOT produce an executable for a program that has a compile-time error.
- **Panic**: an unrecoverable run-time error. A panic prints a message and a call trace to standard error and ends the process with exit status 101 (Section 15).
- **Copy type**: a type whose values are duplicated implicitly when used (Section 5.4). All other types are **move types**.
- **Place**: a variable, a field of a place (`p.f`), or an element of a place (`p[i]`). The **root** of a place is the variable it starts from.
- **Borrow**: a reference to a place that exists for the duration of one call, one `match`, one `for` loop, or one `lock` block. A borrow cannot be stored.
- **Diverging**: an expression that does not produce a value because control leaves it (`return`, `break`, `continue`, `panic`, `exit`).

### 1.4. Design Principles

This section is informative. The rules of Lark are chosen against three principles:

1. Efficiency comes first. The default way of writing something is expected to be fast: a program does not pay for features it does not use, and costs are visible in the source (a copy is written `.copy()`; allocation and atomic operations are not hidden on common paths). Safety checks are done at compile time where possible.
2. Simplicity. There is one way to write each thing. A rule that follows from existing rules is not added.
3. Simple but complete. Common tasks (processing a string by character, reporting all errors, common arithmetic) do not require workarounds.

### 1.5. Relationship to the Reference Implementation

The reference implementation is `lark1`, which compiles itself. Its type checker is `compiler/check.lark`, its ownership checker is `compiler/own.lark`, and the code that releases values when control leaves a scope is `drop_jump` in `compiler/cg_expr.lark`.

Where this document and `lark1` disagree, the disagreement is a defect in one of them. Known disagreements are listed in Appendix B. A program whose meaning depends on such a defect is not portable.

## 2. Notation

The grammar is written in ABNF [RFC5234]. All quoted strings in the grammar are case-sensitive, as if written with the `%s` prefix of [RFC7405].

The lexical grammar (Section 3) describes sequences of bytes. The syntactic grammar (Sections 4 to 19 and Appendix A) describes sequences of tokens; between tokens, whitespace and comments are ignored, except that a line break can produce the token `NL` (Section 3.9). In the syntactic grammar, `ident`, `int-lit`, `float-lit`, and `str-lit` refer to tokens.

A rule of the form `x *("," x) [","]` describes a comma-separated list that MAY end with a comma. The rule `sep` is used for lists that are separated by line breaks, semicolons, or commas:

```
sep = NL / ";" / ","
```

Examples are written in fixed-width text. They are informative.

## 3. Lexical Structure

### 3.1. Source Text

A source file is a sequence of bytes, which SHOULD be UTF-8 [RFC3629]. If a file starts with the UTF-8 byte order mark (EF BB BF), the implementation MUST ignore those three bytes. Column numbers in diagnostics still start at 1 after the mark.

Non-ASCII bytes MAY appear only inside comments, string literals, and character literals. Each source file is followed by an implicit line break, so the last line of one file cannot run into the first line of the next.

### 3.2. Comments and Whitespace

A comment starts with `//` and ends at the end of the line. There are no block comments. Space, horizontal tab, and carriage return are whitespace. A line feed is whitespace except where it ends a statement (Section 3.9).

### 3.3. Identifiers and Keywords

```
ident       = ident-start *(ident-start / DIGIT)
ident-start = ALPHA / "_"
```

Identifiers are ASCII only. The following identifiers are reserved keywords and MUST NOT be used as names:

```
fn type enum interface const pub import if else match for in
return break continue true false take inout scope select
```

The following words have a special meaning only in the positions described in the cited sections. Everywhere else they are ordinary identifiers: `test` (Section 19), `extern` (Section 22), `shared` and `dyn` (Section 5.1), `Fn` (Section 5.1), `defer` (Section 6.7), `lock` and `as` (Section 17.3), `after` and `done` (Section 17.2).

The name `_` is the discard name (Section 6.2). The words `while` and `loop` are ordinary identifiers, but the reference implementation reports an error with a suggestion when they are used as a loop statement, because Lark has no such statements.

### 3.4. Integer Literals

```
dec-lit = DIGIT *(DIGIT / "_")
hex-lit = "0x" *"_" HEXDIG *(HEXDIG / "_")
oct-lit = "0o" *"_" ODIGIT *(ODIGIT / "_")
bin-lit = "0b" *"_" BIT *(BIT / "_")
ODIGIT  = %x30-37
```

Underscores separate digits and have no value. `HEXDIG` here accepts both lower-case and upper-case letters.

A decimal literal MUST be at most 9223372036854775807 (the largest `int`); the most negative `int` is written `-9223372036854775807 - 1`. A hexadecimal, octal, or binary literal MUST NOT need more than 64 bits. If it needs exactly 64 bits, it denotes the `int` with that two's-complement bit pattern, so `0xFFFF_FFFF_FFFF_FFFF` is -1. A letter or digit that is not valid in the base is a compile-time error.

### 3.5. Floating-Point Literals

```
float-lit = dec-lit "." DIGIT *(DIGIT / "_") [exponent]
          / dec-lit exponent
exponent  = ("e" / "E") ["+" / "-"] DIGIT *(DIGIT / "_")
```

A decimal literal followed by `.` and a digit is a floating-point literal, except when the literal itself directly follows a `.` token: in `t.0.1` the digits are tuple indices (Section 7.6). In `1..5` the `..` is the range operator.

### 3.6. Character Literals

```
char-lit = "'" (char-byte / escape) "'"
```

`char-byte` is any single byte other than `\`. A character literal denotes one byte and has type `int`, or `u8` where `u8` is expected (Section 5.6). A literal that contains more than one byte (for example a multi-byte UTF-8 character) is a compile-time error.

### 3.7. String Literals and Interpolation

```
str-lit = DQUOTE *(str-byte / escape / interp) DQUOTE
escape  = "\" ("n" / "t" / "r" / "0" / "e" / "\" / DQUOTE
              / "'" / "#" / "x" 2HEXDIG)
interp  = "#{" expression "}"
```

`str-byte` is any byte other than `"` and `\`, and other than a `#` that is directly followed by `{`. A string literal MAY span several lines; the line breaks are part of its value.

The escapes denote: `\n` line feed (10), `\t` tab (9), `\r` carriage return (13), `\0` zero byte, `\e` escape (27), `\xHH` the byte with hexadecimal value HH, and `\\`, `\"`, `\'`, `\#` the character itself. Any other escape is a compile-time error. `\#` is how `#{` is written without starting an interpolation.

The meaning of interpolation is given in Section 7.8. The end of an interpolation is found by counting `{` and `}` bytes; see Appendix B for the consequence.

### 3.8. Operators and Punctuation

```
+   -   *   /   %   +%  -%  *%
==  !=  <   <=  >   >=  &&  ||  !
&   |   ^   <<  >>  >>>
=   +=  -=  *=  /=  %=  &=  |=  ^=  <<=  >>=  >>>=
??  ?   .   ..  ->  =>  ,   :   ;
(   )   [   ]   {   }
```

Tokens are formed by taking the longest operator that matches. There is no compound assignment for the wrapping operators (no `+%=`). A closing bracket without a matching opening bracket is a compile-time error.

### 3.9. Statement Termination

A line break ends a statement and produces the token `NL`, except in these cases:

1. The innermost open bracket is `(` or `[`. Line breaks are significant only at the top level and directly inside `{`.
2. The last token before the line break is one of: `+ - * / % +% -% *% == != < <= > >= && || ! & | ^ << >> >>> = += -= *= /= %= &= |= ^= <<= >>= >>>= ?? , . .. -> => : ( [ {`.
3. The next non-blank character after the line break is `.` and it is not followed by another `.`. This allows method chains to start each line with `.name`.

Several consecutive line breaks produce one `NL`. A semicolon also separates statements. Because of rule 2, a binary operator that continues an expression onto the next line MUST be written at the end of the first line.

## 4. Program Structure

### 4.1. Top-Level Items

```
program  = *NL *(item *NL)
item     = import / ["pub"] decl / test-decl / extern-decl
decl     = fn-decl / type-decl / enum-decl / iface-decl
         / const-decl
import   = "import" str-lit
```

The top level of a file consists only of the items above. The order of items has no meaning: an item MAY be used before it is declared. `pub` (Section 16) applies to `fn`, `type`, `enum`, `interface`, and `const`; inside an `extern` block it is written on each declaration.

An `import` MUST start in column 1 of its line. Its path is written without the `.lark` extension.

### 4.2. Root Module and Package Mapping

All files given on the command line form the **root module** and share one namespace. Each file loaded by `import` is a separate module (Section 16).

An import path is resolved as follows. If the implementation was given a package mapping `name=dir` (in `lark1`, the option `-p name=dir`) and the first segment of the path is `name`, then `import "name"` loads `dir/name.lark` and `import "name/x"` loads `dir/x.lark`. Otherwise the path is tried first relative to the directory of the importing file and then relative to the root directory of the package that contains the importing file. Each file is loaded at most once.

### 4.3. Entry Point

Execution starts at `fn main()`, which takes no parameters and returns `()`. A program built for testing (Section 19) starts at a generated test driver instead, and does not need `main`.

## 5. Types

### 5.1. Type Syntax

```
type      = base-type *("?" / "!" [base-type])
base-type = "shared" base-type
          / "dyn" ident
          / ("fn" / "Fn") "(" [type *("," type) [","]] ")"
            ["->" type]
          / "[" type "]"
          / "(" ")"
          / "(" type *("," type) [","] ")"
          / qual-ident ["[" type *("," type) [","] "]"]
```

In `T!E`, the error type `E` is parsed only when an identifier directly follows `!`. Suffixes apply from left to right: `int?!` is `(int?)!`. `shared` applies only to the base type that follows it: `shared Node?` is `(shared Node)?`. `(A)` is the same type as `A`; a tuple type has at least two elements. `dyn` is a type former only when an identifier follows it, and `Fn` only when `(` follows it.

### 5.2. Built-in Types

| Type | Meaning |
|---|---|
| `int` | 64-bit signed integer. `+ - *` are checked for overflow; `+% -% *%` wrap. |
| `float` | 64-bit binary floating point [IEEE754]. |
| `u8` | A byte (0 to 255). Supports comparison and `& \| ^ !`, but not arithmetic. `[u8]` is a byte buffer. |
| `bool` | `true` or `false`. |
| `str` | Immutable byte string, reference counted. |
| `()` | The unit type. A function with no result returns `()`. |
| `[T]` | A list (growable array) of `T`. |
| `(A, B, ...)` | A tuple of two or more elements. |
| `T?` | An optional value: `Some(x)` or `None`. |
| `T!E`, `T!` | A result: `Ok(x)` or `Err(e)`. `T!` means `T!str`. |
| `S`, `S[A, ...]` | A struct (Section 5.3), stored by value. |
| `E`, `E[A, ...]` | An enum (sum type), stored by value; MAY be recursive. |
| `fn(A, ...) -> R` | A borrowed function. Allowed only as a parameter type. |
| `Fn(A, ...) -> R` | An owned closure, which can be stored. |
| `dyn I` | A boxed value of any type that implements interface `I`. |
| `shared T` | A read-only, reference-counted shared value. |
| `Chan[T]` | An unbounded queue between tasks. |
| `Mutex[T]` | A value shared between tasks and modified only inside `lock`. |

### 5.3. Structs and Enums

```
type-decl = "type" ident [tparams] "{" *sep *(field *sep) "}"
field     = ["pub"] ident ":" type
enum-decl = "enum" ident [tparams] "{" *sep *(variant *sep) "}"
variant   = ident ["(" [vfield *("," vfield) [","]] ")"]
vfield    = [ident ":"] type
```

Struct fields and enum variants are separated by line breaks, commas, or semicolons. The name of a variant MUST start with an upper-case letter. A variant field MAY be named (`V(name: T)`) or unnamed (`V(T)`). Type parameters of generic structs and enums MUST NOT have bounds (Section 12.2).

### 5.4. Copy Types and Move Types

The copy types are exactly `int`, `float`, `u8`, `bool`, `()`, and `str`. Copying a `str` only increments its reference count. Every other type is a move type: assigning, passing, or returning a value of a move type moves it (Section 9), and a duplicate MUST be requested explicitly with `.copy()`.

`.copy()` of `Fn`, `shared T`, `Chan[T]`, and `Mutex[T]` increments a reference count and yields a handle to the same object. A type that has a user-defined `drop` (Section 13), and every type that contains one, MUST NOT be copied.

### 5.5. Conversions

There are no implicit conversions between types, with two exceptions. Both apply only where an expected type exists: a variable annotation, a function result, an argument, a field, or a list element.

1. Where `T?` or `T!E` is expected and a `T` is given, the value is wrapped in `Some` or `Ok`.
2. Where `dyn I` is expected and a value of a type implementing `I` is given, the value is boxed.

### 5.6. Integer Literal Typing

An integer literal, including a character literal, has type `u8` where `u8` is expected, and MUST then be in the range 0 to 255; otherwise it has type `int`. Conversions between `u8` and `int` are explicit: `b.to_int()`, `n.to_u8()` (panics when out of range), `n.wrap_u8()` (keeps the low 8 bits), and `n.try_u8()` (returns `u8?`). `s.to_bytes()` and `from_bytes(bs)` copy bytes between `str` and `[u8]` unchanged.

### 5.7. Equality

Values of every type except function types can be compared with `==` and `!=`. Comparison is by value, element by element. Two `Fn` values are equal when they are the same closure. If a type has a user-defined `eq` (Section 13), that function is used instead.

## 6. Statements

```
block = "{" *NL [stmt *(1*(NL / ";") stmt) *(NL / ";")] "}"
stmt  = defer-stmt / for-stmt / ident ":" for-stmt
      / ident ":" type "=" expression
      / ident 1*("," postfix) "=" expression
      / expression [assign-op expression]
assign-op = "=" / "+=" / "-=" / "*=" / "/=" / "%=" / "&="
          / "|=" / "^=" / "<<=" / ">>=" / ">>>="
```

### 6.1. Declaration and Assignment

`x = v` declares a new variable `x` if no variable `x` is in scope, with the type of `v`; otherwise it assigns to the existing variable. `x: T = v` declares a variable with an explicit type; writing an annotation for a variable that already exists is a compile-time error. `p = v`, where `p` is a field or element, assigns to that place.

### 6.2. Shadowing and Discard

A declaration in an inner scope MUST NOT reuse the name of a variable of an enclosing scope. The name `_` is exempt: it can be declared any number of times, and it MUST NOT be read. `_ = e` evaluates `e` and discards the result.

### 6.3. Tuple Destructuring

`a, b = t` destructures a tuple into new variables (or `_`). Destructuring into existing variables is a compile-time error.

### 6.4. Compound Assignment

`x op= v` means `x = x op v`. The target MAY be a variable, a field, or a list element. If the target has a user-defined type, the operator is resolved through the protocol functions (Section 13): `s += v` is `s = add(s, v)`.

For `str`, `s += x` and `s = s + x` append in place when no other reference to the string exists, so building a string piece by piece in a loop takes linear time.

### 6.5. Blocks

A block is an expression. If its last statement is an expression, the block's value is that expression's value; otherwise the block's value is `()`. `if`, `match`, `select`, `scope`, and `lock` are expressions too. An `if` without `else` has the value `()`.

### 6.6. Diverging Expressions

`return`, `break`, `continue`, `panic(...)`, and `exit(...)` do not return. They MAY appear wherever a value is required and are compatible with a branch of any type.

### 6.7. Deferred Blocks

```
defer-stmt = "defer" block
```

`defer` is a statement only when `{` follows it. A deferred block runs when control leaves the block that contains the `defer` statement: at its end, or by `return`, `?`, `break`, or `continue`. A `defer` inside a loop body runs once per iteration.

Deferred blocks run in reverse order, interleaved with destruction: values declared after a `defer` are destroyed first, then the deferred block runs, then values declared before it are destroyed, so the deferred block can still use them. The value of `return x` is computed before deferred blocks run.

A variable of an enclosing block that is used in a deferred block MUST NOT be moved before that block ends; it MAY be reassigned or passed with `&`, and the deferred block sees its value at the time of leaving (Rule R21, Section 9). A deferred block MUST NOT contain `return` or `?`; `break` and `continue` inside it MUST refer to loops inside it, and those loops MUST NOT be labeled. A closure MUST NOT contain `defer`.

`exit` and `panic` do not run deferred blocks or destructors. While a deferred block is active, a self-call `return f(...)` is not turned into a jump (Section 8.4).

## 7. Expressions

### 7.1. Precedence

From lowest to highest:

| Level | Operators | Associativity |
|---|---|---|
| 1 | `??` | right |
| 2 | `\|\|` | left |
| 3 | `&&` | left |
| 4 | `== != < <= > >=` | none (MUST NOT be chained) |
| 5 | `\|` (bitwise or) | left |
| 6 | `^` | left |
| 7 | `&` (bitwise and) | left |
| 8 | `<< >> >>>` | left |
| 9 | `+ - +% -%` | left |
| 10 | `* / % *%` | left |
| 11 | unary `-` and `!` | prefix |
| 12 | `.name`, `.name(...)`, `[index]`, `?` | postfix |

The bitwise operators bind more tightly than comparison, as in Rust, so `x & 1 == 0` is `(x & 1) == 0`.

### 7.2. Arithmetic

Both operands of an arithmetic operator MUST have the same type. `+` also concatenates `str` values. `< <= > >=` apply to `int`, `float`, `str`, and types with a user-defined `cmp`. `&&` and `||` apply to `bool` and evaluate the right operand only when needed.

For `int`, `+`, `-`, `*`, and unary `-` panic on overflow. `/` and `%` round toward zero; division by zero panics; `MIN / -1` panics; `x % -1` is 0. `float` arithmetic follows [IEEE754] and does not panic.

### 7.3. Bitwise Operations

`&`, `|`, and `^` apply to `int` (and `u8`). Unary `!x` is bitwise complement for `int` and logical negation for `bool`. `<<` discards bits shifted out; `>>` fills with the sign bit; `>>>` fills with zero. A shift count outside 0 to 63 panics. `+%`, `-%`, and `*%` compute the 64-bit two's-complement result without checking. There is no unsigned integer type: `int` is treated as 64 bits by these operators, and `>>>` and the wrapping operators cover unsigned arithmetic.

### 7.4. Coalescing

In `a ?? b`, `a` has type `T?` or `T!E`; `b` is evaluated only when `a` is `None` or `Err`. If `T` is `int`, `bool`, `str`, or `float`, `a` MAY be a variable, and the contained value is copied out. For any other `T`, `a` MUST be a temporary value (such as a call result), whose contained value is moved out; if `a` is a variable or field, it is a compile-time error, and the program has to write `x.copy() ?? b` or use `match take`.

### 7.5. Method Call Syntax

`x.f(a, ...)` means `f(x, a, ...)`. If the first parameter of `f` is `inout`, `&x` is passed automatically. The function is found by the type of `x` (Section 12.5).

### 7.6. Field, Element and Index Access

`s.f` reads a field. `t.0`, `t.1`, ... read tuple elements. `x[i]` reads a list element (an out-of-range index panics); for a user-defined type it calls `index`, and `x[i] = v` calls `set_index` (Section 13).

### 7.7. Construction and Literals

- `S(f: v, ...)` constructs a struct. The field values are evaluated in the order the fields are declared.
- `V(a, b)` or `V(name: a)` constructs an enum variant. A variant or struct with no fields MAY be written without parentheses (`Nil`).
- An upper-case name without parentheses denotes a field-less variant or struct; a lower-case name denotes a variable.
- For a generic type, the type arguments are inferred from the expected type or from the fields.
- `[a, b]` is a list literal and `(a, b)` a tuple. The empty list `[]` requires an expected type.
- A call MAY label its arguments (`f(x: 1)`); labels are allowed only for struct and variant construction.

### 7.8. String Interpolation

In `"...#{x}..."`, a value of type `int`, `float`, `bool`, or `str` is converted directly. A value of any other type is converted with `fn show(x: T) -> str` (Section 13). A list, `T?`, or tuple without a user-defined `show` is formatted element by element, with strings inside containers in quotes. A struct or enum MUST have a `show` to be interpolated.

## 8. Functions

### 8.1. Declaration

```
fn-decl = "fn" ident [tparams] params ["->" type] block
params  = "(" [param *("," param) [","]] ")"
param   = ["inout" / "take"] ident ":" type
```

If `-> R` is omitted, the result type is `()`. The value of the body block is the result; `return` MAY return early.

### 8.2. Parameter Modes

| Mode | Meaning | Argument |
|---|---|---|
| `x: T` | Read-only borrow. The function MUST NOT modify or move `x`, or pass it on with `&`. | `f(v)` |
| `inout x: T` | Mutable borrow. Modifications are visible to the caller. | `f(&v)` |
| `take x: T` | Ownership transfer. After the call, `v` MUST NOT be used (unless it is a copy type). | `f(v)` |

### 8.3. Overloading

Functions with the same name are distinguished by the type of their **first** parameter. Two functions with the same name and the same first-parameter type, or both without parameters, are a duplicate definition. A non-generic function is preferred over a generic one.

### 8.4. Tail Calls

When a function calls itself in tail position and every parameter is `take`, `int`, or `bool`, the call MUST be compiled as a jump to the start of the function, without growing the stack. Tail position is the value of the body, of each branch of an `if` or `match` in tail position, of a block in tail position, and `return f(...)`. The transformation is not applied inside `scope`, inside closures, or while a deferred block is active.

## 9. Ownership

The ownership rules are checked after type checking. They are stated here as rules on programs; the numbers R1 to R24 are the ones used by the soundness proofs (Section 24). Both the bootstrap compiler and `lark1` enforce the same core rules.

- **R1, R2 (move)**: A value of a move type is moved when it is assigned to a variable, passed as a `take` argument, placed in a constructed value or a list, or returned. A moved variable MUST NOT be used until it is assigned again. Only a variable the function owns can be moved: not a parameter, not an `inout` parameter, not a name bound by a borrowing `match`, and not a variable captured by a closure.
- **R3 (no moving out of places)**: A field, list element, or tuple element MUST NOT be moved out on its own. Programs use `.copy()`, `pop`, `replace(&x, new)`, `match take`, or destructuring instead. An overloaded `index` is exempt, because it returns a new value.
- **R4, R5 (evaluation modes)**: Tuple, list, and constructor elements, `take` arguments, `return` values, and right-hand sides of assignments are used by ownership. Operands, conditions, indices, and interpolated values are read. The branches of an `if`, `match`, or block whose value is read are checked as owning, because their value is new.
- **R6 (inout arguments)**: The argument of `&p` MUST be a place that does not pass through `shared`. Its root MUST NOT be read-only, captured, or frozen. Outside its module, `&p` MUST NOT pass through a field of a struct that has private fields.
- **R7 (exclusivity)**: When `&p` is passed, the root of `p` MUST NOT appear in another argument of the same call, including through a closure that captures it. An argument of a copy type that is not a place (a call result or a constructed value) is exempt, and so is a `str` passed by `take`, which is copied first.
- **R8 (moves inside arguments)**: A variable moved by one argument, directly or inside a block, `if`, or `match` in that argument, MUST NOT appear in another argument.
- **R9 (argument order)**: Arguments are evaluated and checked in the order written. Code after a call that does not return is unreachable.
- **R10 (branch merge)**: After an `if` or `match`, a variable moved in any branch counts as moved. Branches that end by diverging do not take part.
- **R11 (freezing)**: During a borrowing `match e`, a `for x in e`, or a `lock` block, the root of `e` is frozen: it MUST NOT be assigned, moved, or passed with `&`. `match take e` moves `e` and does not freeze it.
- **R12, R13 (loops)**: A loop body MAY move a variable declared outside the loop, but it MUST assign it again before the end of the iteration and before every `continue`. The state after a loop is the union of the states at entry, at the end of an iteration, and at each `break`; `break L` and `continue L` count for the loop labeled `L`.
- **R14 (return)**: `return` moves its value; code after it is unreachable.
- **R15 (loop conditions)**: The condition of `for cond { ... }` is evaluated on every iteration and belongs to that loop.
- **R16 (assignment)**: In `x = e`, `e` is checked first; `x` MUST NOT be read-only, captured, or frozen. Afterwards `x` has a value again.
- **R17 (assignment to places)**: In `p = e` with `p` a field or element, the root of `p` satisfies R6 and MUST NOT be moved, because part of an empty slot cannot be written.
- **R18 to R20 (closures)**: See Section 14.
- **R21 (defer)**: See Section 6.7.
- **R22 to R24 (concurrency)**: See Section 17.

Values are destroyed when they leave scope, when they are overwritten, or when the container holding them is destroyed. `return`, `break`, and `continue` destroy the values of the scopes they leave. A moved-from slot is empty and is not destroyed again.

## 10. Pattern Matching

```
match-expr = "match" ["take"] expression "{" *sep
             [arm *(1*sep arm) *sep] "}"
arm        = pattern "=>" expression
pattern    = pat1 *("|" pat1)
pat1       = ident ":" type
           / qual-ident ["(" [pattern *("," pattern) [","]] ")"]
           / "(" pattern 1*("," pattern) [","] ")"
           / str-lit / ["-"] int-lit / "true" / "false"
```

Arms are tried from top to bottom and the first that matches is taken. All arms MUST have the same type, except arms that diverge.

Patterns are: `_` (matches anything); a lower-case name (binds the value); an integer (optionally negative), `true`, `false`, or a string literal; a variant `V` or `V(p, ...)`, optionally qualified with a module name; a tuple `(p, q, ...)`; and an or-pattern `p | q | ...`, which matches if any alternative matches and MUST NOT bind names. Patterns nest arbitrarily (`Some(1 | 2)`). A type pattern `name: T` is described in Section 12.4.

Enums, `T?`, `T!E`, `int`, `bool`, `str`, and tuples can be matched; `float` cannot. Exhaustiveness is checked column by column over the pattern matrix; a match on integers or strings MUST have a catch-all arm.

A **borrowing match** (the default) binds names as read-only references into the matched value, at any depth, and the matched value is frozen during the match. An **owning match** `match take x` moves `x` and gives ownership of its fields to the bound names. It destructures one level only, so its field patterns MUST be names or `_`. An enum with a user-defined `drop` MUST NOT be matched with `match take`.

## 11. Loops

### 11.1. Forms

```
for-stmt = "for" block
         / "for" for-bind "in" expression [".." expression] block
         / "for" expression block
for-bind = [ident ","] (ident / "(" ident *("," ident) [","] ")")
```

`for { ... }` loops forever. `for cond { ... }` loops while `cond` is true. `for i in lo..hi` iterates over the integers from `lo` up to but excluding `hi`. A `for` is parsed as `for x in` when the token after `for` is an identifier followed by `in` or `,`, or `(` followed by an identifier and `,`.

### 11.2. Iteration Sources

`for x in source { ... }` accepts three kinds of source:

1. A list. `x` is a read-only borrow of each element, and the list is frozen during the loop.
2. An iterator: a type with `fn next(inout it: T) -> E?`. The iterator is moved into the loop. Each `Some(v)` gives ownership of `v` to `x`; `None` ends the loop. The iterator is destroyed when the loop ends.
3. A borrowed traversal: a type without `next` that has `fn iter_len(x: T) -> int` and `fn iter_at(x: T, i: int) -> E`, both read-only. `iter_len` is called once; on each iteration `x` owns the value returned by `iter_at(v, i)`. `v` is frozen during the loop and usable afterwards.

The list and range of `for x in list` and `for i in a..b` are evaluated once, before the loop, and belong to the enclosing code.

### 11.3. Indexed and Tuple Iteration

`for i, x in source` also provides an index that starts at 0; `i` is a new `int` variable. An integer range MUST NOT have an index. `for (a, b) in source` and `for i, (a, _) in source` destructure tuple elements; each item is a name or `_`, and their number MUST equal the tuple's arity. The bound names are read-only borrows into the element, as in `for _e in xs { match _e { (a, b) => { ... } } }`. The index variable and the element variables MUST have different names.

### 11.4. Labeled Loops

`name: for ...` labels a loop. `break name` and `continue name` leave or continue that loop; an unlabeled `break` or `continue` refers to the innermost loop. A label MUST NOT repeat the label of an enclosing loop, and a `break` or `continue` MUST name an enclosing label. Labels are not visible inside closures. Leaving loops this way destroys values and runs deferred blocks as usual.

## 12. Generics and Interfaces

### 12.1. Generic Functions

```
tparams = "[" tparam *("," tparam) [","] "]"
tparam  = ident [":" bound *("+" bound)]
bound   = ident ["[" ident "]"]
```

Type arguments are never written at a call. They are inferred from the argument types; parameters that cannot be inferred from the arguments are taken from the expected result type; otherwise the call is a compile-time error. Arguments are checked without an expected type first, so an argument in a generic position is not wrapped in `Some`, and `[]` or `None` cannot be passed directly.

Generic functions are monomorphized: one copy of the code is generated for each combination of type arguments. The template is not checked by itself; each instance is checked after substitution, and errors point into the template. Generic functions MAY be overloaded by their first parameter: a non-generic function with exactly that type is tried first, then a generic function whose first-parameter pattern matches.

### 12.2. Generic Types

`type Pair[A, B] { ... }` and `enum List[T] { ... }` declare generic types. Each combination of type arguments is instantiated as an ordinary type and shown in diagnostics as `List[int]`. Their type parameters MUST NOT have bounds.

### 12.3. Interfaces and Bounds

```
iface-decl = "interface" ident "{" *sep
             *("fn" ident params ["->" type] *sep) "}"
```

An interface lists methods with `Self` as the implementing type. Interfaces are satisfied structurally: a type implements an interface when, for every method, after replacing `Self` with that type, a function exists with the same parameter modes, parameter types, and result type. There is no `impl` declaration. Bounds are checked at the call, and an error names the missing function.

The built-in bounds are: `Eq` (comparable with `==`, satisfied by every type except function types); `Ord` (`int`, `str`, `float`, and types with `cmp`); `Iter[T]` (a list, iterator, or borrowed traversal with elements `T`); and `Next[T]` (an iterator with `next` only).

### 12.4. Dynamic Interface Values

An interface can be used as `dyn I` only if the first parameter of every method is a read-only `Self` and `Self` appears nowhere else. A `dyn` value owns its boxed value; copying it copies the boxed value. `x.m()` is dispatched through a table of functions.

The concrete type can be recovered with a type pattern `r: Rect =>` in a `match` over a `dyn` value (`r` borrows the boxed value read-only; it MAY be `_`), or with `d.downcast()`, whose type comes from an expected `T?` and which yields `Some(copy)` if the boxed value is a `T` and `None` otherwise. Because `dyn` is open, such a `match` MUST have a `_` arm. The type in a type pattern or downcast MUST implement the interface.

Two `dyn` values are unequal if their concrete types differ; otherwise the concrete type's `==` is used. If the concrete type cannot be compared, the comparison panics at run time. `match take` on a `dyn` value and boxing a value with a user-defined `drop` are not supported.

### 12.5. Method Resolution

For `x.f(...)`, the function `f` is looked up in this order:

1. the module that defines the type of `x`;
2. the current module;
3. the root module;
4. if none of these has `f` and `f` is not built in: the "extension methods" of imported modules, which are `pub` generic functions whose first parameter is a type parameter bounded by `Iter` or `Next`, or a list `[T]`. If two modules provide one, the call is a compile-time error.

## 13. Protocol Functions

The compiler calls the following functions implicitly at certain syntax. They are overloaded by the type of the first parameter, and their signatures are checked where they are defined. Parameters are read-only unless marked otherwise.

| Function | Called for |
|---|---|
| `add sub mul div rem(a, b)`, `neg(a)` | `+ - * / %` and unary `-` when the left operand has a user-defined type. The second parameter MAY have another type. |
| `cmp(a: T, b: T) -> int` | `< <= > >=`; makes `T` satisfy `Ord`. |
| `eq(a: T, b: T) -> bool` | `==` and `!=`, and comparisons inside lists, `T?`, and map keys. |
| `index(x: T, i: K) -> V` | `x[i]`. The result is a new value, not a place. |
| `set_index(inout x: T, i: K, take v: V)` | `x[i] = v`; `x[i] op= v` reads, then writes. |
| `show(x: T) -> str` | String interpolation. |
| `hash(x: T) -> int` | Keys of `std/map` and `std/set`. |
| `next(inout it: T) -> E?` | `for x in it`. |
| `iter_len(x: T) -> int`, `iter_at(x: T, i: int) -> E` | Borrowed traversal. |
| `drop(inout x: T)` | Destruction of a value. MUST NOT be called directly. |
| `from(take e: E1) -> E2` | `?` when the two error types differ. |

The names `drop`, `from`, `main`, `eq`, `cmp`, `next`, and all interface method names are not prefixed with the module name in generated code, so generic code in a module can find implementations written in the root module.

A type MUST have at most one `drop`. A type with `drop`, and every type containing one, MUST NOT be copied, and `drop` MUST NOT assign `x` as a whole. A function with one of these names is treated as a protocol function wherever it is defined, and its signature is checked as such. A function that is not meant to implement a protocol SHOULD NOT use one of these names.

## 14. Closures

```
closure = "|" [ident *("," ident) [","]] "|" expression
        / "||" expression
```

Parameter types come from the expected function type, and the result type is inferred from the body.

- **R18**: A closure body is checked separately, because it may run any number of times, including zero; it does not change the ownership state outside. Captured variables are read-only in the body and MUST NOT be moved.
- **R19**: A closure MUST NOT contain `return`, `break`, `continue`, `?`, `defer`, `scope`, or `lock`.
- **R20**: An `Fn` closure MUST NOT capture an `fn` parameter, nor a value with a user-defined `drop`.

A **borrowed closure** is passed to an `fn(...) -> R` parameter. It captures variables by read-only reference; its environment is on the stack and it does not allocate. It counts as using every variable it captures for the exclusivity rule R7.

An **owned closure** has type `Fn(...) -> R` and can be stored in variables, fields, and lists, returned, or sent to another task. When it is created, the captured variables are copied into a read-only, reference-counted environment on the heap. An `Fn` value MAY be passed to an `fn(...)` parameter. A call MUST go through a variable or parameter; an `Fn` stored in a field is first read into a variable.

Where a function type is expected, the name of a function `f` MAY be written as a value. It means `|a, b| f(a, b)` and creates a closure that captures nothing. `f` MUST NOT be generic, its parameters MUST all be read-only, and its parameter and result types MUST equal the expected ones; for overloaded names, the expected first parameter type selects the function. When passed to a generic function, a function name is checked after the other arguments; if it is neither overloaded nor generic, its signature takes part in inferring type parameters.

## 15. Error Handling

Recoverable errors use `T!E`, where `E` MAY be any type except `()` and function types. Optional values use `T?`.

`e?` has type `T` and works as follows. If `e` has type `T?`, the enclosing function MUST return some `U?`, and `None` returns `None`. If `e` has type `T!E1`, the enclosing function MUST return some `U!E2`, and `Err` returns the error, converted with `from` when `E1` and `E2` differ. `?` MUST NOT be used inside `scope` blocks or closures.

A function returning `()!` MAY `return` without a value, and reaching its end means success. Where `()!` is expected, an `if` whose one branch has type `()!` and whose other branch has no value treats the latter as `Ok()`. A successful `()!` result MAY be matched as `Ok` or `Ok(_)`.

A value of type `T!E` MUST NOT be discarded: using it as a statement, as the end of a `()` function, of a loop body, or of a branch is a compile-time error. Programs handle it with `?` or `match`, or discard it explicitly with `_ = ...`. Values that were wrapped in `Ok` automatically are exempt. An `if` without `else` whose branch ends with a `T!E` value is a compile-time error, because the result would be lost silently.

Unrecoverable errors use `panic(message)`. Index out of range, integer overflow, division by zero, and a failed `assert` also panic. A panic flushes standard output, prints the message and the call trace, and exits with status 101. `exit(n)` ends the process with status `n` without a trace.

## 16. Modules and Visibility

- The name of a module is its file name without the extension. Two modules MUST NOT have the same name.
- A qualified name `m.x` refers to item `x` of module `m` only in a file that imports `m`; in such a file `m` MUST NOT be used as a variable name. In other files `m` is an ordinary name. Every file that uses a module MUST import it itself.
- Outside a module, its items are written `module.name` (`geo.Vec2`, `map.new()`); inside it, the plain name is used. A name is looked up in the current module first, then in the root module.
- **Items**: only `pub` items (`fn`, `type`, `enum`, `interface`, `const`) of a module can be used from other modules. Files of the root module see each other's items.
- **Fields** of structs defined in a module are private by default and visible only in that module. A `pub` field can be read outside the module.
- For a struct that has at least one private field, a `pub` field MUST NOT be assigned, compound-assigned, or passed as `inout` outside the module (including the implicit `&` of a method call), and the struct MUST NOT be constructed outside the module. A struct whose fields are all `pub` can be modified anywhere. Assigning and passing the whole value is not restricted. Fields of enum variants are always public.
- Variants are looked up in the module of their enum; a module qualifier in a pattern is optional.
- There is no `import ... as` and no import of individual names.

```
qual-ident = ident ["." ident]
```

The two-part form applies only when the first identifier names a module imported by the current file.

## 17. Concurrency

### 17.1. Scopes and Tasks

`scope { ... }` is the boundary of structured concurrency. Inside it, `spawn(f, x)` creates a task that runs `f(x)`; the block does not end until every task it spawned has ended.

- **R22**: `spawn` MUST appear directly in a `scope` block. `f` MUST be an ordinary function (not a closure) with exactly one `take` parameter and no result; `x` is moved into the task.
- A `scope` block MAY be left with `return`, `?`, `break`, or `continue`. Leaving destroys values on the way, then waits for the block's tasks, then jumps.
- Values pass between tasks in only three ways: they are moved, they are shared read-only with `shared`, or they are placed in a `Mutex`.
- **R24**: The contents of a `shared` value are read-only (they MUST NOT be assigned or passed with `&` through it), and a `shared` value MUST NOT contain a `Mutex` or `Chan`.

### 17.2. Channels and Select

`chan()` creates a `Chan[T]`. `send(v)` moves `v` into the queue. `recv()` returns `T?`: it waits while the queue is empty, until a value arrives or every other holder of the channel has released it, in which case it returns `None`. There is no `close`.

```
select-expr = "select" "{" *sep [sel-arm *(1*sep sel-arm) *sep]
              "}"
sel-arm     = ident "<" "-" expression "=>" expression
            / "after" expression "=>" expression
            / "done" "=>" expression
```

`select` waits for the first of several channels that has a value. There MAY be at most one `after` arm (a timeout in milliseconds) and at most one `done` arm, which runs when all channels have ended. With a `done` arm, `select` MAY have a value; otherwise every arm has type `()`.

### 17.3. Mutexes

```
lock-expr = "lock" expression "as" ident block
```

`lock` starts a lock block only when an identifier follows it. `mutex(v)` creates a `Mutex[T]`; `.copy()` yields a handle to the same mutex. The contained value can be used only in `lock m as x { ... }`.

- **R23**: `m` MUST be a place, and its root is frozen during the block. Inside the block, `x` behaves like an `inout` parameter: it can be modified and passed on with `&x`, but not moved. The mutex is unlocked at the end of the block. The block's value is the value of the `lock` expression and MUST be a copy.
- A lock block MAY be left with `return`, `?`, `break`, or `continue`; the mutex is unlocked before the jump. Closures MUST NOT contain `lock`.
- A task MAY wait while holding a lock. Locking a mutex that the same task already holds ends the process with an error. Two tasks that lock two mutexes in opposite order deadlock; deadlock is not detected.

### 17.4. Scheduling

Tasks are coroutines with their own stacks, run by the run-time system on a number of operating-system threads (in `lark1`, `LARK_PROCS`, defaulting to the number of processor cores). The scheduler starts at the first `spawn`; a program that does not spawn pays nothing for concurrency.

Tasks are not preempted. A task yields only where it waits: `recv`, `select`, the end of a `scope`, `sleep_ms`, waiting for a `lock`, and reads, writes, and accepts of `std/net`. Blocking file, pipe, and terminal I/O, `os.shell`, `net.connect`, and `extern "c"` functions occupy an operating-system thread while they wait.

When concurrency is used, sockets SHOULD be closed with `close` from `std/net` (or by leaving scope). A socket closed directly through `extern "c"` is not known to the run-time system, and later waits on that descriptor number can hang.

## 18. Constants

```
const-decl = "const" ident "=" expression
```

The value of a constant is computed at compile time and has type `int`, `bool`, `str`, or `float`. The expression MAY contain only literals, other constants, arithmetic, comparison, logical operators, and string `+`; it MUST NOT call functions. `float` constants support only `+ - * / %`. A cyclic definition, division by zero, or overflow is a compile-time error.

A constant MUST NOT be assigned or passed as `inout`. A local variable takes precedence over a constant of the same name. Constants share a namespace with types, functions, and variants.

## 19. Tests

```
test-decl = "test" str-lit block
```

`test "name" { ... }` declares a test without parameters. In a normal build, tests are checked but not run. In a test build (`lark1 --test`), the implementation generates an entry point that runs all tests. Only tests in the files given on the command line are collected; their names MUST be unique.

Each test runs in a separate child process, so a failure (panic, exit, or crash) affects only that test. Output of a test is shown only if it fails. The first command-line argument of the test executable filters tests by name.

`assert(cond)` panics if `cond` is false. `assert_eq(a, b)` requires both sides to have the same type, which MUST be comparable and interpolatable; on failure it shows both values.

## 20. Diagnostics

The wording of messages is not specified; `lark1` reports in Chinese. The following behavior is required of a conforming implementation:

- An error MUST identify the file, line, and column. `lark1` prints `file:line:col: error: message`, followed by the source line and a `^` under the column.
- Within a function body, an implementation SHOULD report more than one error: `lark1` skips the failing statement, checks the body again from the start, and reports up to 10 errors, so that one error does not cause follow-on errors. Ownership checking is skipped for functions with type errors. Syntax errors and errors in type declarations and signatures are reported one at a time.
- For an undefined name, type, field, or variant, an implementation SHOULD suggest the closest available name by edit distance.
- Warnings do not affect compilation (`-w` turns them off in `lark1`). An implementation SHOULD warn about unused variables, unreachable code, unused imports, and unused non-`pub` functions and types. Names starting with `_` are not warned about, and warnings inside the standard library are not shown.
- An implementation MAY limit nesting depth. `lark1` rejects more than 256 levels of nested brackets and blocks and syntax trees deeper than 1000 levels, and asks for long operator chains to be split.

## 21. Built-in Functions

The following functions are known to the compiler. Most are called with method syntax (`xs.len()`, `n.to_u8()`).

| Group | Functions |
|---|---|
| Output, process | `print eprint args exit panic system sleep_ms` |
| Strings, integers | `len byte_at slice from_byte int_str parse_int try_parse_int join` |
| Lists, values | `len push pop reserve copy replace` (`xs.reserve(n)`: the next `n` pushes do not reallocate) |
| Files | `read_file try_read_file write_file` |
| Floating point | `to_float to_int float_str parse_float try_parse_float sqrt floor ceil round trunc exp ln log10 sin cos tan asin acos atan atan2 float_pow` |
| Bytes | `to_u8 wrap_u8 try_u8 to_bytes from_bytes` (`b.to_int()` converts `u8` to `int`) |
| System (used by `std/os`) | `try_write_file try_append_file try_list_dir try_remove try_mkdir try_rename try_cwd try_getenv try_capture file_kind run_cmd now_ms now_ns mono_ns try_open try_fd_read try_fd_write try_fd_close try_tcp_connect try_tcp_listen try_tcp_accept try_sock_port try_sock_write try_sock_timeout` |
| Sharing, concurrency | `share spawn chan send recv mutex`, and `lock m as x { ... }` |
| Tests | `assert assert_eq` |
| Constructors | `Some None Ok Err` |

## 22. Foreign Function Interface

```
extern-decl = "extern" str-lit "{" *sep
              *(["pub"] "fn" ident params ["->" type] *sep) "}"
```

The string after `extern` MUST be `"c"`. An `extern "c"` block declares functions of a C library by signature only; a body is a compile-time error. A call looks like any other call and calls the C symbol of the same name.

- The types allowed in a signature are `int` (C `int64_t`), `c_int`, `c_uint`, `c_long`, `c_ulong`, `usize`, `isize`, `float` (C `double`), `bool`, `u8`, `str` (C `const char*`), and `[u8]` (only as a parameter; passes a pointer to the data). The result type MAY also be `()`.
- C integer types exist only in `extern` blocks; on the Lark side they are `int`. Values passed to C are range-checked and panic when out of range; an unsigned result from C that does not fit in `int` also panics.
- A `str` is passed as zero-terminated bytes; a zero byte inside the string ends it early on the C side. A string returned by C is copied into a new `str`; `NULL` becomes the empty string. Memory owned by C is not managed by Lark.
- Parameters are read-only; only `[u8]` MAY be `inout`, which lets C write into the buffer. C MUST NOT write more bytes than the length of the list; the caller is responsible for this.
- Variadic functions, callbacks, struct and pointer parameters, and macros or inline functions from headers are not supported. Only the C standard library is linked by default.

Code that uses `extern "c"` is outside the safety guarantee of Section 24.

## 23. Implementation Requirements

### 23.1. Evaluation and Release Conventions

The soundness proofs of Section 24 assume the following properties of generated code. A conforming implementation MUST provide them:

| No. | Requirement |
|---|---|
| A1 | Arguments and constructor fields are evaluated in the order they are written. |
| A2 | Moving a value leaves its source slot empty, and destroying an empty slot does nothing. |
| A3 | Temporaries (call results, the matched value of a borrowing `match`) live until the end of their statement or `match`. |
| A4 | When control leaves scopes, it works from the innermost outward: it destroys each scope's values, runs that scope's deferred blocks in reverse order, and unlocks `lock` blocks; when leaving a `scope` block it waits for its tasks last. |
| A5 | A `str` is copied before modification when its reference count is not 1. |
| A6 | While tasks are running, reference counts are updated atomically. |

### 23.2. Representation (Informative)

This section describes `lark1`, which generates GNU C11 [C11] that depends only on `runtime/lark_rt.h`.

- Structs and tuples are stored by value. Enums are stored by value with a tag starting at 1; tag 0 means moved. `T?` is stored as `{ some, v }`. An enum or `T?` that contains itself through value fields is stored on the heap. Lists are `{ data, len, cap }`.
- Moving is a bitwise copy followed by clearing the source, so no run-time "moved" flags are needed. A struct with `drop` carries a hidden liveness flag.
- `T!E` is stored by value as `{ set, ok, val, err }`, so returning a result does not allocate. `fn(...)` is `{ function pointer, environment pointer }`; `dyn I` is `{ heap value, table }`.
- Generics are monomorphized; there is no boxing and no run-time type information.
- A panic prints a call trace with one frame per function (name, file, current line). `--release`, or compiling the C code with `-DLK_NOTRACE`, turns traces off. Compiling with `-DLK_UNCHECKED` turns off overflow and shift-count checks; shift counts then use only their low 6 bits. A program compiled with `-DLK_UNCHECKED` does not conform to Section 7.2.
- Task stacks are 1 MiB (pages are committed when used) with a guard page below.

## 24. Soundness and Formal Verification

### 24.1. The Guarantee

The static rules are designed to give the following guarantee. Suppose a program passes type checking and ownership checking, does not use `extern "c"`, and is not compiled with `-DLK_UNCHECKED`. Then a run of the program ends in one of these ways: it terminates normally, it panics or calls `exit`, it runs forever (including deadlock), or it overflows the stack. Throughout the run:

1. **No reads of empty slots**: every variable, field, and element that is read holds a value.
2. **Each value is released exactly once**, when it leaves scope, is overwritten, or its container is released. (Reference-counted cycles are not counted.)
3. **Borrows are stable**: a value under a read-only borrow is not modified, moved, or released during the borrow.
4. **Exclusivity**: while an `inout` borrow exists, the same value is not read or written through any other path.
5. **No data races**: two tasks do not access the same value at the same time unless both only read it (`shared`) or both are inside `lock` blocks of the same mutex.

Not covered: C code called through `extern "c"`, `-DLK_UNCHECKED`, deadlock, stack overflow, and external programs run through functions such as `os.shell`. The correctness of the compiler itself (whether the generated C implements these rules) is not proved; the requirements A1 to A6 of Section 23.1 are assumed by the proofs and checked by differential testing.

### 24.2. Machine-Checked Proofs

The proofs are in the directory `formal/` of the Lark repository and are checked with Lean 4 [LEAN4], version 4.35, without Mathlib (`lake build`). Each model includes, for the rule it covers, a counterexample showing that the theorem fails when the rule is not checked.

| File | Model | Theorem |
|---|---|---|
| `Lark/Core.lean` | Variables, moves, reads, branches, assignment (R1, R2, R10, R16) | `no_use_after_move` |
| `Lark/Loop.lean` | Loops with `break` and `continue`, fuel-based semantics (R12, R13) | `loop_never_stuck` |
| `Lark/Call.lean` | The three parameter modes, by pointer and by copy-in/copy-out; exclusivity (R6 to R8) | `call_agree` |
| `Lark/Drop.lean` | Heap boxes, release on overwrite, freezing, release at end (R2, R11, R16; A2, A4) | `drop_exactly_once` |
| `Lark/Task.lean` | Fork-join concurrency, `shared`, `Mutex` and `lock` | `race_free` |
| `Lark/Chan.lean` | Interleaved execution with channels | `chan_race_free` |
| `Lark/Exit.lean` | Nested scopes, `defer`, every way of leaving a scope (R12 to R14, R21; A2, A4) | `exit_sound` |
| `Lark/Clo.lean` | Borrowed closures and `Fn` closures (R18 to R20) | `clo_sound` |
| `Lark/Full.lean` | The combination of the above with borrowing `for` and `match` and two-argument calls | `full_sound` |

All theorems in this table were proved in November 2026. Further files in `formal/` prove properties of standard library modules and of the experimental TLS implementation; they are not part of the language definition.

### 24.3. Limits of the Proofs

The proofs cover a core calculus, Lark-core, which keeps only the features that affect ownership. Generics, interfaces, `dyn`, modules and visibility, overloading, protocol functions, and constants are resolved during type checking and are not modeled. Rules R7 and R11 are checked on root variables only, which is conservative: `f(&a.x, &a.y)` is rejected although the two fields do not overlap.

## 25. Security Considerations

The guarantee of Section 24.1 removes several classes of memory errors from programs that satisfy its conditions. It does not make programs secure, and its conditions are easy to leave:

- **`extern "c"`**: C code can violate every property in Section 24.1. A `str` passed to C ends at the first zero byte, which can change the meaning of file names or commands built from untrusted input. Writing past the end of an `inout [u8]` buffer is undefined behavior.
- **Unchecked builds**: `-DLK_UNCHECKED` makes integer overflow wrap silently. Code that relies on overflow panics for correctness (for example, size calculations) loses that protection.
- **Denial of service**: integer overflow, out-of-range indices, and failed assertions panic and end the whole process. Programs that handle untrusted input SHOULD validate it rather than relying on panics. Deadlock is not detected, and the stack depth of tasks is limited to 1 MiB; running out ends the process with a segmentation fault and no diagnostic.
- **Timing**: the language makes no guarantee that any operation takes time independent of the data. Cryptographic code written in Lark cannot rely on the compiler to preserve constant-time behavior.
- **Exit paths**: `exit` and `panic` do not run deferred blocks or destructors. Cleanup that has to happen in all cases (for example, removing temporary files or restoring a terminal) needs `os.at_exit` from the standard library.
- **External programs**: functions such as `os.shell` run other programs, which are outside the language. String interpolation does no escaping of any kind.
- **Compiler limits**: the nesting limits of Section 20 protect the compiler from stack exhaustion on hostile source code. The compiler is not verified (Section 24.1).

## 26. IANA Considerations

This document has no IANA actions. Lark source files use the extension `.lark`; no media type is registered.

## 27. References

### 27.1. Normative References

- [C11] International Organization for Standardization, "Information technology -- Programming languages -- C", ISO/IEC 9899:2011, December 2011.
- [IEEE754] Institute of Electrical and Electronics Engineers, "IEEE Standard for Floating-Point Arithmetic", IEEE Std 754-2019, July 2019.
- [RFC2119] Bradner, S., "Key words for use in RFCs to Indicate Requirement Levels", BCP 14, RFC 2119, March 1997.
- [RFC3629] Yergeau, F., "UTF-8, a transformation format of ISO 10646", STD 63, RFC 3629, November 2003.
- [RFC5234] Crocker, D., Ed. and P. Overell, "Augmented BNF for Syntax Specifications: ABNF", STD 68, RFC 5234, January 2008.
- [RFC7405] Kyzivat, P., "Case-Sensitive String Support in ABNF", RFC 7405, December 2014.
- [RFC8174] Leiba, B., "Ambiguity of Uppercase vs Lowercase in RFC 2119 Key Words", BCP 14, RFC 8174, May 2017.

### 27.2. Informative References

- [LEAN4] de Moura, L. and S. Ullrich, "The Lean 4 Theorem Prover and Programming Language", Automated Deduction - CADE 28, Lecture Notes in Computer Science, vol. 12699, 2021.
- [RFC7322] Flanagan, H. and S. Ginoza, "RFC Style Guide", RFC 7322, September 2014.
- [DESIGN] The Lark Project, "Lark 设计（已实现部分）" (Lark design, implemented part), file `DESIGN.md` in the Lark repository.
- [SOUNDNESS] The Lark Project, "Lark 的可靠性：核心演算和要证的定理" (Soundness of Lark: core calculus and theorems), file `design/soundness.md` in the Lark repository.

## Appendix A. Collected Grammar

This appendix collects the syntactic grammar of Sections 4 to 19. Lexical rules are in Section 3. Where the grammar is ambiguous, the notes in the cited sections decide.

```
program    = *NL *(item *NL)
item       = import / ["pub"] decl / test-decl / extern-decl
decl       = fn-decl / type-decl / enum-decl / iface-decl
           / const-decl
import     = "import" str-lit
sep        = NL / ";" / ","

fn-decl    = "fn" ident [tparams] params ["->" type] block
tparams    = "[" tparam *("," tparam) [","] "]"
tparam     = ident [":" bound *("+" bound)]
bound      = ident ["[" ident "]"]
params     = "(" [param *("," param) [","]] ")"
param      = ["inout" / "take"] ident ":" type
type-decl  = "type" ident [tparams] "{" *sep *(field *sep) "}"
field      = ["pub"] ident ":" type
enum-decl  = "enum" ident [tparams] "{" *sep *(variant *sep) "}"
variant    = ident ["(" [vfield *("," vfield) [","]] ")"]
vfield     = [ident ":"] type
iface-decl = "interface" ident "{" *sep
             *("fn" ident params ["->" type] *sep) "}"
const-decl = "const" ident "=" expression
test-decl  = "test" str-lit block
extern-decl = "extern" str-lit "{" *sep
             *(["pub"] "fn" ident params ["->" type] *sep) "}"

type       = base-type *("?" / "!" [base-type])
base-type  = "shared" base-type / "dyn" ident
           / ("fn" / "Fn") "(" [type *("," type) [","]] ")"
             ["->" type]
           / "[" type "]" / "(" ")"
           / "(" type *("," type) [","] ")"
           / qual-ident ["[" type *("," type) [","] "]"]
qual-ident = ident ["." ident]

block      = "{" *NL [stmt *(1*(NL / ";") stmt) *(NL / ";")] "}"
stmt       = defer-stmt / for-stmt / ident ":" for-stmt
           / ident ":" type "=" expression
           / ident 1*("," postfix) "=" expression
           / expression [assign-op expression]
assign-op  = "=" / "+=" / "-=" / "*=" / "/=" / "%=" / "&="
           / "|=" / "^=" / "<<=" / ">>=" / ">>>="
defer-stmt = "defer" block
for-stmt   = "for" block
           / "for" for-bind "in" expression [".." expression]
             block
           / "for" expression block
for-bind   = [ident ","]
             (ident / "(" ident *("," ident) [","] ")")

expression = or-expr ["??" expression]
or-expr    = and-expr *("||" and-expr)
and-expr   = cmp-expr *("&&" cmp-expr)
cmp-expr   = bor-expr [cmp-op bor-expr]
cmp-op     = "==" / "!=" / "<" / "<=" / ">" / ">="
bor-expr   = xor-expr *("|" xor-expr)
xor-expr   = band-expr *("^" band-expr)
band-expr  = shift-expr *("&" shift-expr)
shift-expr = add-expr *(("<<" / ">>" / ">>>") add-expr)
add-expr   = mul-expr *(("+" / "-" / "+%" / "-%") mul-expr)
mul-expr   = unary *(("*" / "/" / "%" / "*%") unary)
unary      = ("-" / "!") unary / postfix
postfix    = primary *("." (ident / int-lit) [args]
           / "[" expression "]" / "?")
args       = "(" [arg *("," arg) [","]] ")"
arg        = [ident ":"] ["&"] expression
primary    = closure / int-lit / float-lit / str-lit
           / "true" / "false" / lock-expr
           / qual-ident [args]
           / "(" expression ")"
           / "(" expression 1*("," expression) [","] ")"
           / "[" [expression *("," expression) [","]] "]"
           / block / "scope" block / if-expr / select-expr
           / match-expr / "return" [expression]
           / "break" [ident] / "continue" [ident]
closure    = "|" [ident *("," ident) [","]] "|" expression
           / "||" expression
if-expr    = "if" expression block ["else" (if-expr / block)]
lock-expr  = "lock" expression "as" ident block
match-expr = "match" ["take"] expression "{" *sep
             [arm *(1*sep arm) *sep] "}"
arm        = pattern "=>" expression
pattern    = pat1 *("|" pat1)
pat1       = ident ":" type
           / qual-ident ["(" [pattern *("," pattern) [","]] ")"]
           / "(" pattern 1*("," pattern) [","] ")"
           / str-lit / ["-"] int-lit / "true" / "false"
select-expr = "select" "{" *sep [sel-arm *(1*sep sel-arm) *sep]
             "}"
sel-arm    = ident "<" "-" expression "=>" expression
           / "after" expression "=>" expression
           / "done" "=>" expression
```

Notes on the grammar:

- `return` has an operand unless the next token is `NL`, `;`, `}`, `,`, or `)`. `break` and `continue` take a label when an identifier follows on the same line.
- `lock` is a lock expression only when an identifier follows it; `defer` is a statement only when `{` follows it; a statement `ident ":" for-stmt` is a labeled loop only when `for` follows the colon.
- In a destructuring statement, the first target MUST be a variable.
- A primary that is an upper-case name without arguments is a field-less variant or struct.
- The reference parser does not require separators between struct fields, enum variants, or interface methods; programs SHOULD write one.

## Appendix B. Known Deviations and Open Issues

This appendix lists known differences between this document and `lark1`, and limitations that are not yet resolved.

1. **Internal error on fields of temporaries**: passing a field of a call result as an argument, as in `f(g(x).field)`, makes `lark1` stop with an internal error ("从字段或下标移出", in `owned_place` of `compiler/cg_expr.lark`) instead of compiling the program or reporting a normal error. Binding the result to a variable first (`k = g(x)` and then `f(k.field)`) avoids it.
2. **Interpolation and braces**: the end of `#{ ... }` is found by counting `{` and `}` bytes, including those inside string or character literals in the interpolated expression. An expression such as `"#{f("}")}"` is therefore split in the wrong place. Programs SHOULD NOT put unbalanced braces inside interpolations.
3. **Conservative aliasing**: rules R7 and R11 consider only the root variable of a place (Section 24.3).
4. **Stack overflow**: running out of stack, in a task or in the main thread, ends the process with a segmentation fault and no specific diagnostic.
5. **Earlier descriptions**: the informal description [DESIGN] does not mention octal literals (`0o`), the escapes `\e` and `\xHH`, or the byte order mark. This document follows `lark1`, which accepts all of them.
