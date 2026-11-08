; 生产者和消费者：生产者往通道里放 1..100，最后放 0；消费者收到 0 之前一直加，打印总和（5050）
; 通道的容量是 4：缓冲满了生产者就等着，消费者收走一个再叫醒它
.locals 4
        newch 4
        store 0             ; loc0 = 通道
        load 0
        spawn consumer      ; 参数是通道
        store 1             ; loc1 = 消费者的编号
        push 1
        store 2             ; loc2 = 下一个要放的
p_loop:
        load 2
        push 101
        eq
        jz p_send
        load 0
        push 0
        send                ; 结束的记号
        load 1
        join                ; 等消费者，结果是总和
        halt
p_send:
        load 0
        load 2
        send
        load 2
        push 1
        add
        store 2
        jmp p_loop

consumer:
        store 0             ; loc0 = 通道
        push 0
        store 1             ; loc1 = 和
c_loop:
        load 0
        recv
        dup
        jz c_done
        load 1
        add
        store 1
        jmp c_loop
c_done:
        pop
        load 1
        print
        load 1
        halt
