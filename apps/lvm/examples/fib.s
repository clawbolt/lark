; 函数调用：开 20 个线程，第 i 个递归算 fib(i)，主线程 join 它们加起来
; fib(0) + fib(1) + … + fib(19) = fib(21) - 1 = 10945
.locals 4
        push 20
        store 0             ; loc0 = 还要开几个
s_loop:
        load 0
        jz s_done
        load 0
        push 1
        sub
        dup
        store 0
        spawn worker        ; 参数是 i（19..0），线程编号是 1..20
        pop
        jmp s_loop
s_done:
        push 1
        store 0             ; loc0 = 下一个要 join 的
        push 0
        store 1             ; loc1 = 总和
j_loop:
        load 0
        push 21
        eq
        jz j_one
        load 1
        halt
j_one:
        load 0
        join
        load 1
        add
        store 1
        load 0
        push 1
        add
        store 0
        jmp j_loop

worker:
        call fib            ; 栈上是 i，回来时是 fib(i)
        halt

; fib(n)：栈上是 n，返回时栈上是 fib(n)（每次调用有一份新的局部变量）
fib:
        store 0             ; loc0 = n
        load 0
        push 2
        lt
        jz f_rec
        load 0              ; n < 2：fib(n) = n
        ret
f_rec:
        load 0
        push 1
        sub
        call fib
        load 0
        push 2
        sub
        call fib
        add
        ret
