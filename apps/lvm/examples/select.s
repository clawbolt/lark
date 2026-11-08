; select：两个生产者往两个通道里各放 3 个（1、2、3 和 100、200、300，第二个每放一个睡 1 毫秒），
; 主线程同时等两个通道收 6 次，每次打印是第几个通道、收到什么，最后的结果是收到的和（606）
.locals 6
        newch
        store 0             ; loc0 = 第一个通道
        newch
        store 1             ; loc1 = 第二个通道
        load 0
        spawn fast
        pop
        load 1
        spawn slow
        pop
        push 0
        store 2             ; loc2 = 和
        push 6
        store 3             ; loc3 = 还要收几次
loop:
        load 3
        jz end
        load 0
        load 1
        select 2            ; 栈上：值、第几个通道
        print               ; 打印第几个通道
        dup
        print               ; 打印值
        load 2
        add
        store 2
        load 3
        push 1
        sub
        store 3
        jmp loop
end:
        load 2
        halt

fast:
        store 0
        load 0
        push 1
        send
        load 0
        push 2
        send
        load 0
        push 3
        send
        push 0
        halt

slow:
        store 0
        push 1
        sleep
        load 0
        push 100
        send
        push 1
        sleep
        load 0
        push 200
        send
        push 1
        sleep
        load 0
        push 300
        send
        push 0
        halt
