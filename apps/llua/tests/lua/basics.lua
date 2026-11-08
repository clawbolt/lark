-- llua 的端到端测试：输出要和真 Lua 5.4 一样（tests/compat.sh 会逐字比较）

-- 用元表写的“类”
local Account = {}
Account.__index = Account

function Account.new(owner, balance)
  return setmetatable({owner = owner, balance = balance or 0}, Account)
end

function Account:deposit(n)
  self.balance = self.balance + n
  return self
end

function Account:withdraw(n)
  if n > self.balance then error("余额不足：" .. self.owner) end
  self.balance = self.balance - n
end

Account.__tostring = function(a)
  return string.format("%s: %.2f", a.owner, a.balance)
end

local a = Account.new("alice", 100)
a:deposit(50):deposit(25.5)
print(a)
local ok, err = pcall(a.withdraw, a, 1000)
print(ok, err)

-- 可变参数和多返回值
local function stats(...)
  local n = select("#", ...)
  local sum, min, max = 0, math.huge, -math.huge
  for i = 1, n do
    local x = select(i, ...)
    sum = sum + x
    if x < min then min = x end
    if x > max then max = x end
  end
  return sum, sum / n, min, max
end
print(stats(3, 1, 4, 1, 5, 9, 2, 6))

-- 闭包：每轮循环是一个新的 i
local adders = {}
for i = 1, 3 do
  adders[i] = function(x) return x + i * 10 end
end
print(adders[1](1), adders[2](2), adders[3](3))

-- 字符串
local words = {}
for _, w in ipairs({"lark", "lua", "c", "ocaml"}) do
  words[#words + 1] = string.format("%-6s|%3d", w, #w)
end
print(table.concat(words, "\n"))
print(("%5.1f%%"):format(99.44), ("x"):rep(0) == "", ("abc"):byte(1, -1))

-- 整数和浮点数
print(10 // 3, 10.0 // 3, 10 % -3, -10 % 3, 2^0.5, 1e300 * 1e10, math.tointeger(3.0))
print(math.maxinteger * 2, math.mininteger // -1, 7 // 0.0, -7 % math.huge)
