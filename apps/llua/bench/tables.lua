-- 表和循环：筛法、字符串键的表、排序
local n = 2000000
local is = {}
for i = 1, n do is[i] = true end
for i = 2, n do
  if is[i] then
    for j = i * i, n, i do is[j] = false end
  end
end
local c = 0
for i = 2, n do if is[i] then c = c + 1 end end
print(c)

local t = {}
for i = 1, 200000 do t["k" .. (i % 5000)] = (t["k" .. (i % 5000)] or 0) + i end
local s = 0
for _, v in pairs(t) do s = s + v end
print(s)

local xs = {}
local x = 42
for i = 1, 100000 do
  x = (x * 1103515245 + 12345) % 2147483648
  xs[i] = x
end
table.sort(xs)
print(xs[1], xs[#xs])
