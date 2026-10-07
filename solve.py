#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""CDCL SAT 求解器，UNSAT 时输出 DRAT 证明（仅添加子句，以空子句收尾）。

用法: python3 solve.py <instance.cnf>
"""
import sys


def parse_dimacs(path):
    nvars = 0
    clauses = []
    with open(path) as f:
        for line in f:
            line = line.strip()
            if not line or line[0] in "cp%":
                continue
            toks = [int(t) for t in line.split()]
            if toks and toks[-1] == 0:
                toks = toks[:-1]
            for t in toks:
                nvars = max(nvars, abs(t))
            clauses.append(toks)
    return nvars, clauses


class Solver:
    def __init__(self, nvars, clauses):
        self.nvars = nvars
        self.clauses = []          # list of list[int]
        self.watches = {}          # lit -> list of clause idx
        self.assign = [0] * (nvars + 1)   # 0 unassigned, 1 true, -1 false
        self.level = [0] * (nvars + 1)
        self.reason = [-1] * (nvars + 1)  # clause idx or -1 (decision)
        self.trail = []
        self.trail_lim = []
        self.activity = [0.0] * (nvars + 1)
        self.var_inc = 1.0
        self.var_decay = 0.95
        self.phase = [1] * (nvars + 1)    # phase saving
        self.qhead = 0
        self.proof = []            # learned clauses in order
        for c in clauses:
            self.add_clause(c, learnt=False)

    def add_clause(self, c, learnt):
        # 去重文字、去恒真
        seen = set()
        cl = []
        for lit in c:
            if -lit in seen:
                return -1  # tautology, skip
            if lit not in seen:
                seen.add(lit)
                cl.append(lit)
        idx = len(self.clauses)
        self.clauses.append(cl)
        if len(cl) == 0:
            return idx
        if len(cl) == 1:
            # unit: enqueue immediately at level 0
            if not self.enqueue(cl[0], idx):
                pass
            self.watches.setdefault(cl[0], []).append(idx)
            self.watches.setdefault(cl[0], [])  # watch itself (unit: single watch)
            return idx
        self.watches.setdefault(cl[0], []).append(idx)
        self.watches.setdefault(cl[1], []).append(idx)
        return idx

    def value(self, lit):
        a = self.assign[abs(lit)]
        if a == 0:
            return 0
        return a if lit > 0 else -a

    def enqueue(self, lit, reason):
        v = abs(lit)
        val = 1 if lit > 0 else -1
        if self.assign[v] != 0:
            return self.assign[v] == val
        self.assign[v] = val
        self.level[v] = len(self.trail_lim)
        self.reason[v] = reason
        self.trail.append(lit)
        return True

    def propagate(self):
        """返回冲突子句 idx 或 -1。watched literal 传播。"""
        while self.qhead < len(self.trail):
            lit = self.trail[self.qhead]
            self.qhead += 1
            falsified = -lit  # 被赋假的文字，检查它的 watch 列表
            wlist = self.watches.get(falsified, [])
            i = 0
            while i < len(wlist):
                ci = wlist[i]
                c = self.clauses[ci]
                if len(c) == 1:
                    i += 1
                    continue
                # 保证 c[1] 是被赋假的那个 watch
                if c[0] == falsified:
                    c[0], c[1] = c[1], c[0]
                # c[1] == falsified now; 若另一 watch 为真则子句已满足
                if self.value(c[0]) > 0:
                    i += 1
                    continue
                # 找一个未赋假的新文字替换 c[1]
                found = False
                for k in range(2, len(c)):
                    if self.value(c[k]) >= 0:
                        c[1], c[k] = c[k], c[1]
                        self.watches.setdefault(c[1], []).append(ci)
                        wlist[i] = wlist[-1]
                        wlist.pop()
                        found = True
                        break
                if found:
                    continue  # 不递增 i，处理交换来的新元素
                # 没有可替换的：子句是单元或冲突
                if self.value(c[0]) < 0:
                    return ci
                else:
                    # 单元：传播 c[0]
                    if not self.enqueue(c[0], ci):
                        return ci
                    i += 1
        return -1

    def bump_var(self, v):
        self.activity[v] += self.var_inc
        if self.activity[v] > 1e100:
            for i in range(1, self.nvars + 1):
                self.activity[i] *= 1e-100
            self.var_inc *= 1e-100

    def decay(self):
        self.var_inc /= self.var_decay

    def analyze(self, confl):
        """1UIP 冲突分析，返回 (learned_clause, backtrack_level)。"""
        learnt = [0]
        seen = [False] * (self.nvars + 1)
        path_c = 0
        idx = len(self.trail) - 1
        c = self.clauses[confl]
        back = 0
        p = 0  # 上一个被解析的 trail 文字；reason 子句里要跳过它
        while True:
            for lit in c:
                if lit == p:
                    continue
                v = abs(lit)
                if not seen[v] and self.level[v] > 0:
                    seen[v] = True
                    self.bump_var(v)
                    if self.level[v] >= len(self.trail_lim):
                        path_c += 1
                    else:
                        learnt.append(lit)
                        if self.level[v] > back:
                            back = self.level[v]
            # 在 trail 上倒退找下一个 seen 的变量
            while True:
                lit = self.trail[idx]
                idx -= 1
                if seen[abs(lit)]:
                    break
            p = lit
            seen[abs(p)] = False
            path_c -= 1
            if path_c == 0:
                learnt[0] = -p
                break
            c = self.clauses[self.reason[abs(p)]]
            assert self.reason[abs(p)] >= 0
        # 把回溯层最高的文字放到第二位（watch 优化）
        if len(learnt) > 2:
            best = 1
            for i in range(2, len(learnt)):
                if self.level[abs(learnt[i])] > self.level[abs(learnt[best])]:
                    best = i
            learnt[1], learnt[best] = learnt[best], learnt[1]
        return learnt, back

    def backtrack(self, level):
        target = self.trail_lim[level] if level < len(self.trail_lim) else len(self.trail)
        while len(self.trail) > target:
            lit = self.trail.pop()
            v = abs(lit)
            self.phase[v] = 1 if self.assign[v] > 0 else -1
            self.assign[v] = 0
            self.reason[v] = -1
        del self.trail_lim[level:]
        self.qhead = len(self.trail)

    def pick_branch_lit(self):
        best = 0
        best_act = -1.0
        for v in range(1, self.nvars + 1):
            if self.assign[v] == 0 and self.activity[v] > best_act:
                best_act = self.activity[v]
                best = v
        if best == 0:
            return 0
        return best * self.phase[best]

    def solve(self):
        confl = self.propagate()
        if confl >= 0:
            # 0 层冲突：UNSAT，空子句可由原公式 RUP 推出
            self.proof.append([])
            return False
        restarts = 0
        while True:
            confl = self.propagate()
            if confl >= 0:
                if len(self.trail_lim) == 0:
                    self.proof.append([])
                    return False
                learnt, back = self.analyze(confl)
                self.decay()
                self.backtrack(back)
                ci = self.add_clause(learnt, learnt=True)
                self.proof.append(list(learnt))
                if len(learnt) == 1:
                    self.enqueue(learnt[0], ci)
                else:
                    self.enqueue(learnt[0], ci)
            else:
                lit = self.pick_branch_lit()
                if lit == 0:
                    return True
                self.trail_lim.append(len(self.trail))
                self.enqueue(lit, -1)


def main():
    nvars, clauses = parse_dimacs(sys.argv[1])
    s = Solver(nvars, clauses)
    sat = s.solve()
    if sat:
        print("SAT")
        out = []
        for v in range(1, nvars + 1):
            a = s.assign[v]
            out.append(str(v if a >= 0 else -v))
        print(" ".join(out))
    else:
        print("UNSAT")
        for c in s.proof:
            if c:
                print(" ".join(str(l) for l in c) + " 0")
            else:
                print("0")


if __name__ == "__main__":
    main()
