; 带超时的 select：工人每 3 毫秒交一个结果，一共交 5 个；主线程每次最多等 10 毫秒，
; 收到就加起来，超时一次就不等了。工人第 5 个以后不再交，所以第 6 次一定超时。
; 打印每次收到的值，超时打印 -1，结果是收到的和（1 + 2 + 3 + 4 + 5 = 15）
.locals 4
        newch
        store 0             ; loc0 = 通道
        load 0
        spawn worker
        pop
        push 0
        store 1             ; loc1 = 和
loop:
        load 0
        push 10
        tselect 1           ; 栈上：值、第几个通道（超时是 0、-1）
        dup
        push -1
        eq
        jz got
        print               ; 超时：打印 -1
        pop
        load 1
        halt
got:
        pop                 ; 只有一个通道，丢掉"第 0 个"
        dup
        print
        load 1
        add
        store 1
        jmp loop

worker:
        store 0
        push 1
        store 1             ; loc1 = 下一个要交的
w_loop:
        load 1
        push 6
        eq
        jz w_send
        push 0
        halt
w_send:
        push 3
        sleep
        load 0
        load 1
        send
        load 1
        push 1
        add
        store 1
        jmp w_loop
