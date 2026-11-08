# 从 macOS 的 sample 输出里找出：落在某几个系统函数上的样本，是从哪些 Lark 运行时或程序里的函数调过去的。
# 用法：awk -f tools/sample-callers.awk /tmp/x.sample.txt | sort -rn | head -30
# 每行：样本数  目标函数  <- 最近的 3 层 lk_ / f_ 函数（从里到外）
# 要看别的目标函数：awk -v targets="malloc,free" -f …
BEGIN {
  if (targets == "") targets = "__psynch_mutexwait,__psynch_mutexdrop,__psynch_cvsignal,kevent"
  n = split(targets, ts, ",")
  for (i = 1; i <= n; i++) want[ts[i]] = 1
}
/^Call graph:/ { on = 1; next }
/^Total number in stack/ { on = 0 }
on && match($0, /[0-9]+ [A-Za-z_$]/) {
  d = RSTART
  split(substr($0, RSTART), a, " ")
  cnt = a[1]
  name = a[2]
  for (k in stack) if (k + 0 >= d) delete stack[k]
  stack[d] = name
  if (name in want) {
    chain = ""
    m = 0
    for (j = d - 1; j > 0 && m < 3; j--) {
      if ((j in stack) && stack[j] ~ /^(lk_|f_)/) { chain = chain " <- " stack[j]; m++ }
    }
    tot[name chain] += cnt
  }
}
END { for (c in tot) print tot[c], c }
