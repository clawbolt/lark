-- 函数调用：fib(30) 大约 135 万次调用
local function fib(n)
  if n < 2 then return n end
  return fib(n - 1) + fib(n - 2)
end
print(fib(30))
