#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""独立的 DRAT 证明验证器（本任务中证明均为 RUP 追加 + 删除）。

用法：
  python3 verify.py <实例.cnf> <证明.drat>
有效打印 VALID 并以 0 退出；否则打印 INVALID 并以非 0 退出。

检查规则：
- 删除行 d <lits> 0：删除一条当前活动且完全相同（按多重集）的子句。
- 追加行 <lits> 0：该子句必须满足 RUP——先令其中所有文字为假，
  再在活动公式上做单元传播，若导出冲突则该子句成立（包含/重言式子句
  也接受）。
- 证明必须追加空子句，空子句的 RUP 即原公式（含已学子句）单元传播冲突。
仅使用标准库。
"""

import sys


def parse_dimacs(path):
    nvars = 0
    clauses = []
    cur = []
    with open(path) as f:
        for line in f:
            line = line.strip()
            if not line or line[0] == "c":
                continue
            if line[0] == "p":
                nvars = int(line.split()[2])
                continue
            for tok in line.split():
                x = int(tok)
                if x == 0:
                    clauses.append(cur)
                    cur = []
                else:
                    cur.append(x)
    if cur:
        clauses.append(cur)
    return nvars, clauses


def parse_proof(path):
    steps = []
    with open(path) as f:
        for line in f:
            line = line.strip()
            if not line:
                continue
            deleted = False
            body = line
            if body[0] == "d":
                deleted = True
                body = body[1:].strip()
            toks = body.split()
            vals = [int(t) for t in toks]
            if vals and vals[-1] == 0:
                vals = vals[:-1]
            steps.append((deleted, vals))
    return steps


class Checker:
    def __init__(self, nvars):
        self.n = nvars
        self.active = []  # [alive, tuple(clause)]

    def add_clause(self, clause):
        s = set(clause)
        taut = any(-x in s for x in s)
        self.active.append([not taut, tuple(clause)])
        return True

    def remove_clause(self, clause):
        target = sorted(clause)
        for rec in self.active:
            if rec[0] and sorted(rec[1]) == target:
                rec[0] = False
                return True
        return False

    def rup(self, clause):
        # 令被证子句中每个文字为假，然后做单元传播；若导出冲突则 RUP。
        assign = {}
        for lit in clause:
            assign[abs(lit)] = lit < 0
        while True:
            progressed = False
            for alive, c in self.active:
                if not alive:
                    continue
                unassigned = []
                satisfied = False
                for lit in c:
                    v = abs(lit)
                    if v in assign:
                        is_true = assign[v] if lit > 0 else (not assign[v])
                        if is_true:
                            satisfied = True
                            break
                    else:
                        unassigned.append(lit)
                if satisfied:
                    continue
                if not unassigned:
                    return True  # 冲突
                if len(unassigned) == 1:
                    lit = unassigned[0]
                    v = abs(lit)
                    if v not in assign:
                        assign[v] = lit > 0
                        progressed = True
            if not progressed:
                return False


def main():
    if len(sys.argv) != 3:
        print("usage: python3 verify.py <file.cnf> <proof.drat>", file=sys.stderr)
        return 2
    try:
        nvars, clauses = parse_dimacs(sys.argv[1])
        steps = parse_proof(sys.argv[2])
    except Exception as exc:
        print("INVALID")
        print("parse error: %s" % exc, file=sys.stderr)
        return 1

    checker = Checker(nvars)
    for c in clauses:
        checker.add_clause(c)

    added_empty = False
    for i, (deleted, clause) in enumerate(steps):
        if len(clause) != len(set(abs(x) for x in clause)) and clause:
            # 出现同变量重复文字不影响语义，但含 x 与 -x 视为重言式
            pass
        if deleted:
            if not checker.remove_clause(clause):
                print("INVALID")
                print("step %d: deletion of absent clause %s" % (i + 1, clause),
                      file=sys.stderr)
                return 1
            continue
        if not checker.rup(clause):
            print("INVALID")
            print("step %d: clause %s is not RUP" % (i + 1, clause),
                  file=sys.stderr)
            return 1
        checker.add_clause(clause)
        if not clause:
            added_empty = True

    if not added_empty:
        print("INVALID")
        print("proof does not derive the empty clause", file=sys.stderr)
        return 1
    print("VALID")
    return 0


if __name__ == "__main__":
    sys.exit(main())
