CC      ?= cc
# 生成的 C 里常有没用到的函数、变量、参数（运行时辅助、模式匹配的临时值），这几类关掉；其余 -Wall -Wextra 都开着，
# make strict 再加 -Werror 把零警告固定下来
CFLAGS  ?= -std=gnu11 -O2 -Wall -Wextra -Wno-unused-function -Wno-unused-variable -Wno-unused-parameter \
           -Wno-unused-but-set-variable -Wno-missing-braces -pthread
LARK0   := stage0/_build/default/src/main.exe
BUILD   := build

.PHONY: stage0 hello asan tsan leaks test-err stage1 bootstrap seed seed-check test-tool test1 expect fmt-tool fmt fmt-check unit unit-compiler bench lark-tool check strict perms formal apps bench-grep bench-http profile profile-grep apicov clean

stage0:
	cd stage0 && dune build

$(BUILD):
	mkdir -p $(BUILD)

# 编译并运行示例
hello: stage0 | $(BUILD)
	$(LARK0) examples/hello.lark -o $(BUILD)/hello.c
	$(CC) $(CFLAGS) -Iruntime $(BUILD)/hello.c -o $(BUILD)/hello
	./$(BUILD)/hello

# 用 AddressSanitizer 检查越界、重复释放和释放后使用。
# macOS 的 ASan 不支持泄漏检测，泄漏请用 make leaks。
ifeq ($(shell uname),Darwin)
ASAN_LEAKS := 0
else
ASAN_LEAKS := 1
endif

asan: stage0 | $(BUILD)
	$(LARK0) examples/hello.lark -o $(BUILD)/hello.c
	$(CC) -std=gnu11 -g -O1 -fsanitize=address,undefined -fno-omit-frame-pointer \
	  -Iruntime $(BUILD)/hello.c -o $(BUILD)/hello_asan
	ASAN_OPTIONS=detect_leaks=$(ASAN_LEAKS) ./$(BUILD)/hello_asan

# 用 ThreadSanitizer 检查数据竞争：用到任务、通道、Mutex 的示例，各跑一遍，有报告就停（运行时给每次栈切换加了 fiber 注解）
TSAN_EX := strthreads scope select
tsan: stage1
	@for e in $(TSAN_EX); do \
	  ./$(BUILD)/lark1 -w examples/$$e.lark -o $(BUILD)/tsan_$$e.c && \
	  $(CC) -std=gnu11 -g -O1 -fsanitize=thread -fno-omit-frame-pointer -pthread -Iruntime $(BUILD)/tsan_$$e.c -o $(BUILD)/tsan_$$e && \
	  TSAN_OPTIONS=halt_on_error=1 ./$(BUILD)/tsan_$$e > /dev/null && echo "$$e：ThreadSanitizer 没有报告" || exit 1; \
	done

# macOS 自带的 leaks 工具：程序退出时报告未释放的内存
leaks: hello
	MallocStackLogging=1 leaks --atExit -- ./$(BUILD)/hello

# tests/err 下的每个文件都必须编译失败
test-err: stage0 | $(BUILD)
	@for f in tests/err/*.lark; do \
	  if $(LARK0) $$f -o /dev/null 2>$(BUILD)/err.txt; then echo "没有报错：$$f"; exit 1; \
	  else printf "%-30s %s\n" "$$f" "$$(cat $(BUILD)/err.txt)"; fi; \
	done

# ---------- 自举 ----------
# 编译器源码。lark0 和旧种子只接受单个输入文件，所以第一步先拼成一个文件；
# 从 lark1 开始直接编译多个文件，报错会带上文件名
SRC1 := compiler/ast.lark compiler/lex.lark compiler/parse.lark compiler/types.lark \
        compiler/check.lark compiler/own.lark compiler/cg_types.lark compiler/cg_expr.lark \
        compiler/cg_stmt.lark compiler/main.lark

$(BUILD)/lark1.lark: $(SRC1) | $(BUILD)
	cat $(SRC1) > $@

# 第一步：得到 lark1。
# 有种子 seed/lark_seed.c 时，用种子编译出的编译器来编译 compiler/*.lark（不再需要 OCaml）；
# 没有种子时退回 OCaml 写的 lark0。
SEED := seed/lark_seed.c

ifneq ($(wildcard $(SEED)),)
stage1: $(BUILD)/lark1.lark
	$(CC) $(CFLAGS) -Iruntime $(SEED) -o $(BUILD)/lark_seed
	./$(BUILD)/lark_seed $(BUILD)/lark1.lark -o $(BUILD)/lark1.c
	$(CC) $(CFLAGS) -Iruntime $(BUILD)/lark1.c -o $(BUILD)/lark1
else
stage1: stage0 $(BUILD)/lark1.lark
	$(LARK0) $(BUILD)/lark1.lark -o $(BUILD)/lark1.c
	$(CC) $(CFLAGS) -Iruntime $(BUILD)/lark1.c -o $(BUILD)/lark1
endif

# 第二步：lark1 直接编译 compiler/ 下的多个文件得到 lark2，lark2 再编译自己；两次生成的 C 完全一致即自举成功
bootstrap: stage1
	./$(BUILD)/lark1 $(SRC1) -o $(BUILD)/lark2.c
	$(CC) $(CFLAGS) -Iruntime $(BUILD)/lark2.c -o $(BUILD)/lark2
	./$(BUILD)/lark2 $(SRC1) -o $(BUILD)/lark3.c
	cmp $(BUILD)/lark2.c $(BUILD)/lark3.c && echo "自举成功：lark2 与 lark3 生成的 C 完全一致"

# 自举成功后把 lark2.c 存为种子；之后编译器源码就可以使用种子支持的所有特性
# 种子必须是当前编译器自己生成的 C：bootstrap 只比较 lark2 和 lark3，两个都由新编译器生成，种子过期了也看不出来
# （旧种子编出的 lark1 可能慢得多，比如字符串拼接还没有原地追加的优化时，词法器是平方复杂度）
seed-check: bootstrap
	@cmp -s $(SEED) $(BUILD)/lark2.c || { echo "种子过期：$(SEED) 和当前源码自举得到的 lark2.c 不一样，请运行 make seed"; exit 1; }
	@echo "种子是最新的"

seed: bootstrap
	mkdir -p seed
	cp $(BUILD)/lark2.c $(SEED)
	@echo "已更新种子 $(SEED)"

# lark1 跑全部示例和用例，并和记下的预期结果逐字比较（示例：tests/expected/名字.out；
# 其它用例：同目录的 名字.expected）。测试运行器本身是 tools/test.lark，细节见它开头的说明
test-tool: stage1
	./$(BUILD)/lark1 -w tools/test.lark -o $(BUILD)/lark-test.c
	$(CC) $(CFLAGS) -Iruntime $(BUILD)/lark-test.c -o $(BUILD)/lark-test

test1: test-tool
	@CC="$(CC)" CFLAGS="$(CFLAGS)" ./$(BUILD)/lark-test

# 用这次的实际结果重写预期结果，并列出改了哪些：新增示例或用例后、或确认输出的变化是对的之后运行
expect: test-tool
	@CC="$(CC)" CFLAGS="$(CFLAGS)" ./$(BUILD)/lark-test update

# 基准测试（tools/bench.lark）：bench/*.lark 和“lark1 编译自己”，每个按几组 C 编译选项各跑几次，打印最短时间。
# 运行次数用环境变量改：BENCH_RUNS=5 make bench
bench: stage1
	./$(BUILD)/lark1 -w tools/bench.lark -o $(BUILD)/lark-bench.c
	$(CC) $(CFLAGS) -Iruntime $(BUILD)/lark-bench.c -o $(BUILD)/lark-bench
	@CC="$(CC)" CFLAGS="$(CFLAGS)" ./$(BUILD)/lark-bench

# 格式化工具 lark-fmt（tools/fmt.lark）：make fmt 就地格式化编译器、标准库和示例，make fmt-check 只检查
FMT_SRC := compiler/*.lark std/*.lark tools/*.lark examples/*.lark examples/*/*.lark apps/*/*.lark apps/*/*/*.lark

fmt-tool: stage1
	./$(BUILD)/lark1 tools/fmt.lark -o $(BUILD)/lark-fmt.c
	$(CC) $(CFLAGS) -Iruntime $(BUILD)/lark-fmt.c -o $(BUILD)/lark-fmt

fmt: fmt-tool
	./$(BUILD)/lark-fmt $(FMT_SRC)

fmt-check: fmt-tool
	./$(BUILD)/lark-fmt --check $(FMT_SRC)

# 构建工具 lark（tools/lark.lark）：lark new / build / run / test / fetch，见 README“项目与依赖”。
# 得到 build/lark；它按自己所在的位置找到 build/lark1、runtime/ 和 std/，可以把 build/ 加进 PATH 或者设置 LARK_HOME
lark-tool: stage1
	./$(BUILD)/lark1 -w tools/lark.lark -o $(BUILD)/lark-tool.c
	$(CC) $(CFLAGS) -Iruntime $(BUILD)/lark-tool.c -o $(BUILD)/lark

# 运行一个文件里的 test 块：make unit F=文件.lark [T=名字里的一段]（只运行名字里含有 T 的测试）
unit: stage1
	./$(BUILD)/lark1 --test $(F) -o $(BUILD)/unit.c
	$(CC) $(CFLAGS) -Iruntime $(BUILD)/unit.c -o $(BUILD)/unit -lm
	./$(BUILD)/unit "$(T)"

# 编译器自己的单元测试（compiler/*.lark 里的 test 块）：make unit-compiler [T=名字里的一段]
unit-compiler: stage1
	./$(BUILD)/lark1 -w --test $(SRC1) -o $(BUILD)/compiler_unit.c
	$(CC) $(CFLAGS) -Iruntime $(BUILD)/compiler_unit.c -o $(BUILD)/compiler_unit -lm
	./$(BUILD)/compiler_unit "$(T)"

# ---------- 日常开发（脚本在 tools/dev/，每个开头都有说明） ----------

# 标准库公开函数的测试覆盖（tools/apicov.lark）：每个 pub fn 至少要在一个测试里调用过；make apicov A=1 按模块列出比例，
# make apicov U=1 列出只有测试和示例在用的函数（给人审，见 docs/std.md 的“函数的取舍”）
apicov: stage1
	./$(BUILD)/lark1 -w tools/apicov.lark -o $(BUILD)/lark-apicov.c
	$(CC) $(CFLAGS) -Iruntime $(BUILD)/lark-apicov.c -o $(BUILD)/lark-apicov
	@./$(BUILD)/lark-apicov $(if $(U),--unused,$(if $(A),--all,))

# 改完编译器或运行时以后的一整套检查：自举、重建 build/lark、跑全部测试、检查标准库的测试覆盖，最后补上执行权限
check: bootstrap seed-check lark-tool test1 apicov perms

# 和 check 一样，但从头全部重建，并且任何 C 警告都算错误（测试里编译的程序也一样）
strict:
	$(MAKE) -B CFLAGS="$(CFLAGS) -Werror" check

# 补上 build/ 和 apps/*/build/ 里程序的执行权限（文件被复制或下载过以后会丢）
perms:
	@find $(BUILD) apps/*/build -maxdepth 1 -type f ! -name '*.*' -exec chmod +x {} + 2> /dev/null; true

# 形式化证明（formal/）和对拍：四套各 500 个固定种子的随机程序，Lean 的检查和 lark1 判断要一致。要装 Lean 4，所以不在 check 里
formal: stage1 perms
	cd formal && lake build
	sh formal/difftest.sh 500 1 loop
	sh formal/difftest.sh 500 1 call
	sh formal/difftest.sh 500 1 defer
	sh formal/difftest.sh 500 1 clo

# 构建练手程序：make apps（全部）或 make apps A=lgrep（也可以写几个：A="lgrep lcache"）
apps: lark-tool
	@sh tools/dev/apps.sh $(A)

# lgrep 和系统 grep 的速度对比（在 build/bench/big.txt 上）；RUNS=5 make bench-grep 改每项的次数
bench-grep:
	@$(MAKE) --no-print-directory apps A=lgrep
	@sh tools/dev/bench-grep.sh

# HTTP 服务压测：make bench-http A=lhttp 或 A=lcache [D=秒数]（需要 wrk）
bench-http:
	@test -n "$(A)" || { echo "用法：make bench-http A=lhttp|lcache [D=秒数]"; exit 2; }
	@$(MAKE) --no-print-directory apps A=$(A)
	@sh tools/dev/bench-http.sh $(A) $(D)

# 抓调用热点：make profile CMD="apps/lgrep/build/lgrep -ci err build/bench/big.txt" [S=秒数，默认 3]
profile:
	@test -n "$(CMD)" || { echo "用法：make profile CMD=\"命令 参数…\" [S=秒数]"; exit 2; }
	@sh tools/dev/profile.sh $(or $(S),3) $(CMD)

# lgrep 的热点：同一个大文件给 20 遍，让它跑得比采样久。make profile-grep [P="-ci err"] [S=3]
profile-grep:
	@$(MAKE) --no-print-directory apps A=lgrep
	@test -f build/bench/big.txt || sh tools/dev/bench-grep.sh > /dev/null
	@sh tools/dev/profile.sh $(or $(S),3) apps/lgrep/build/lgrep $(or $(P),-ci err) $(foreach i,1 2 3 4 5 6 7 8 9 10 11 12 13 14 15 16 17 18 19 20,build/bench/big.txt)

clean:
	rm -rf $(BUILD)
	cd stage0 && dune clean
