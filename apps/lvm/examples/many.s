; 开 N 个线程，第 i 个算 1 + 2 + … + i，主线程 join 它们，把结果加起来
; N = 1000 时结果是 Σ i(i+1)/2 = N(N+1)(N+2)/6 = 167167000（大约 550 万条指令）
.locals 4
        push 1000
        store 0             ; loc0 = 还要开几个
        push 0
        store 1             ; loc1 = 已经开了几个（线程编号从 1 开始）
spawn_loop:
        load 0
        jz join_start
        load 0
        spawn worker        ; 参数是 loc0，栈上留下新线程的编号（丢掉：编号就是 1..N）
        pop
        load 0
        push 1
        sub
        store 0
        jmp spawn_loop
join_start:
        push 1
        store 0             ; loc0 = 下一个要 join 的
        push 0
        store 2             ; loc2 = 总和
join_loop:
        load 0
        push 1001
        eq
        jz join_one
        load 2
        halt
join_one:
        load 0
        join
        load 2
        add
        store 2
        load 0
        push 1
        add
        store 0
        jmp join_loop

; 线程：栈上是 i，算 1 + … + i（故意一条一条加，让时间片用完被抢占）
worker:
        store 0             ; loc0 = i
        push 0
        store 1             ; loc1 = 和
w_loop:
        load 0
        jz w_done
        load 1
        load 0
        add
        store 1
        load 0
        push 1
        sub
        store 0
        jmp w_loop
w_done:
        load 1
        halt
