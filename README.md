# SAT 求解器

## 输入

`instances/` 下有 10 个 DIMACS CNF 实例，SAT 和 UNSAT 混着来：

- `php5.cnf` `php6.cnf` `php7.cnf`：鸽笼原理，UNSAT。
- `mult_ok.cnf`：两个 2x2 乘法器等价检查，UNSAT。
- `mult_bug.cnf`：其中一个乘法器被改坏了一处，SAT，会给出反例。
- `queens8.cnf`：8 皇后，SAT。
- `sudoku4.cnf`：4x4 数独，SAT。
- `rand_a.cnf` `rand_b.cnf` `rand_c.cnf`：随机 3-SAT，SAT。

DIMACS 就是标准格式，`p cnf <变量数> <子句数>` 起头，每条子句以 0 结尾。

## 你要交付什么

写两个命令。

`solve.py`，命令行：

```bash
python3 solve.py <实例.cnf>
```

- 可满足：第一行输出 `SAT`，第二行输出一个满足赋值，空格分隔的带符号变量，比如 `1 -2 3 -4`。
- 不可满足：第一行输出 `UNSAT`，之后逐行输出 DRAT 证明。每行是一条子句，整数序列以 `0` 结尾；以 `d` 开头表示删除该子句；证明必须以空子句（单独一行 `0`）收尾。

`verify.py`，命令行：

```bash
python3 verify.py <实例.cnf> <证明.txt>
```

证明有效打印 `VALID` 并退出码 0，无效打印 `INVALID` 并退出码非 0。这个验证器要逐份检查证明里的每一条子句是不是真的能被推出来。

## 判分标准（`grade.py`）

```bash
python3 grade.py
```

判分脚本内置了一个独立的 DRAT 验证器，不依赖你的 `verify.py`。它对每个实例：

- 你报 SAT，就用独立代码校验你给的赋值是否满足全部子句。
- 你报 UNSAT，就用独立验证器逐份校验你的 DRAT 证明。

所以假装 UNSAT 是糊弄不过去的，空口说 SAT 也过不了赋值校验。全部实例判对输出 `PASS`。

你的 `verify.py` 也要自洽：能接受你自己 `solve.py` 产出的证明，能拒绝被篡改过的证明，判分脚本会抽查这个。

## 约束

- 全程本地离线，不调任何现成 SAT 求解器（minisat、cadical、python-sat 等都不行），CDCL 全自己写。
- 只许用标准库。
- 手写 CDCL 的坑在单元传播、冲突分析、学习子句、watch literal、回溯这几处，哪一处没写对都会出错，写完自己跑 `python3 grade.py` 对拍。
