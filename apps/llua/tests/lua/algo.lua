-- llua 的端到端测试：几个小算法

-- 筛法求素数
local function primes(n)
  local is = {}
  for i = 2, n do is[i] = true end
  for i = 2, n do
    if is[i] then
      for j = i * i, n, i do is[j] = false end
    end
  end
  local out = {}
  for i = 2, n do
    if is[i] then out[#out + 1] = i end
  end
  return out
end
local ps = primes(100)
print(#ps, table.concat(ps, " ", 1, 10), ps[#ps])

-- 快速排序（多重赋值交换元素）
local function qsort(t, lo, hi)
  lo, hi = lo or 1, hi or #t
  if lo >= hi then return t end
  local p, i = t[hi], lo - 1
  for j = lo, hi - 1 do
    if t[j] <= p then
      i = i + 1
      t[i], t[j] = t[j], t[i]
    end
  end
  t[i + 1], t[hi] = t[hi], t[i + 1]
  qsort(t, lo, i)
  qsort(t, i + 2, hi)
  return t
end
print(table.concat(qsort({5, 3, 8, 1, 9, 2, 7}), ","))

-- 词频：按次数从多到少，次数相同按字母
local text = "the quick brown fox jumps over the lazy dog the fox"
local freq = {}
local start = 1
while true do
  local s = text:find(" ", start, true)
  local w = text:sub(start, (s or 0) - 1)
  freq[w] = (freq[w] or 0) + 1
  if not s then break end
  start = s + 1
end
local ws = {}
for w in pairs(freq) do ws[#ws + 1] = w end
table.sort(ws, function(x, y)
  if freq[x] ~= freq[y] then return freq[x] > freq[y] end
  return x < y
end)
for i = 1, 3 do io.write(ws[i], "=", freq[ws[i]], " ") end
print()

-- 递归
local function fib(n)
  if n < 2 then return n end
  return fib(n - 1) + fib(n - 2)
end
print(fib(25))

-- 拼接和数字的写法
local parts = {}
for i = 1, 5 do parts[#parts + 1] = i * i end
print(table.concat(parts, "+") .. " = " .. (1 + 4 + 9 + 16 + 25))
print(100 / 3, 1e100, 2^53, 123456789012345678)

-- 用 repeat 和 goto 以外的办法提前结束
local n, steps = 27, 0
repeat
  if n % 2 == 0 then n = n // 2 else n = 3 * n + 1 end
  steps = steps + 1
until n == 1
print("collatz(27) 用了 " .. steps .. " 步")
