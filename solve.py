#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""手写 CDCL SAT 求解器。

SAT:  打印 SAT 与一组完整赋值。
UNSAT:打印 UNSAT，之后是 DRAT 风格证明：按冲突分析顺序追加 1-UIP 学习子句，
      每条学习子句都对当时的子句库满足 RUP，证明以空子句结束。
仅使用 Python 标准库。
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
                parts = line.split()
                nvars = int(parts[2])
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


class Solver:
    def __init__(self, nvars, clauses):
        self.n = nvars
        self.db = []                 # 子句库（含学习子句），子句前两个文字是 watch 位置
        self.watches = [[] for _ in range(2 * (nvars + 1))]
        self.value = [0] * (nvars + 1)   # 1=true, -1=false, 0=unknown
        self.level = [0] * (nvars + 1)
        self.reason = [-1] * (nvars + 1)  # 传播原因子句 id，决策为 -1
        self.phase = [0] * (nvars + 1)
        self.activity = [0.0] * (nvars + 1)
        self.trail = []
        self.qhead = 0
        self.trail_lim = []
        self.proof = []
        self.var_inc = 1.0
        self.decay = 1.0 / 0.95
        self.conflicts = 0

    @staticmethod
    def widx(lit):
        return 2 * abs(lit) + (1 if lit < 0 else 0)

    def lval(self, lit):
        v = self.value[abs(lit)]
        if v == 0:
            return 0
        return v if lit > 0 else -v

    def attach(self, cid):
        c = self.db[cid]
        self.watches[self.widx(c[0])].append(cid)
        self.watches[self.widx(c[1])].append(cid)

    def assign(self, lit, lev, why):
        v = abs(lit)
        self.value[v] = 1 if lit > 0 else -1
        self.level[v] = lev
        self.reason[v] = why
        self.trail.append(lit)

    def enqueue(self, lit, why=-1):
        v = abs(lit)
        if self.value[v] != 0:
            return self.lval(lit) != -1
        self.assign(lit, len(self.trail_lim), why)
        return True

    def propagate(self):
        """watch literal 单元传播，返回冲突子句 id 或 -1。"""
        while self.qhead < len(self.trail):
            p = self.trail[self.qhead]
            self.qhead += 1
            false_lit = -p
            ws = self.watches[self.widx(false_lit)]
            i = 0
            j = 0
            n = len(ws)
            conflict = -1
            while i < n:
                cid = ws[i]
                i += 1
                c = self.db[cid]
                if c[0] == false_lit:
                    c[0], c[1] = c[1], c[0]
                first = c[0]
                if self.lval(first) == 1:
                    ws[j] = cid
                    j += 1
                    continue
                moved = False
                for k in range(2, len(c)):
                    cand = c[k]
                    if self.lval(cand) != -1:
                        c[1], c[k] = cand, c[1]
                        self.watches[self.widx(cand)].append(cid)
                        moved = True
                        break
                if moved:
                    continue
                ws[j] = cid
                j += 1
                if self.lval(first) == -1:
                    conflict = cid
                    # 保留尚未处理的条目，绝不丢失 watch。
                    for t in range(i, n):
                        ws[j] = ws[t]
                        j += 1
                    break
                self.assign(first, len(self.trail_lim), cid)
            del ws[j:]
            if conflict != -1:
                return conflict
        return -1

    def bump_var(self, v):
        a = self.activity[v] + self.var_inc
        self.activity[v] = a
        if a > 1e100:
            for w in range(1, self.n + 1):
                self.activity[w] *= 1e-100
            self.var_inc *= 1e-100

    def analyze(self, conflict_cid):
        """1-UIP 冲突分析，返回 (学习子句, 回溯层)。"""
        seen = [False] * (self.n + 1)
        learnt = []
        path_c = 0
        p = 0
        cid = conflict_cid
        idx = len(self.trail) - 1
        cur_level = len(self.trail_lim)
        while True:
            for lit in self.db[cid]:
                v = abs(lit)
                if v == p or seen[v] or self.level[v] == 0:
                    continue
                seen[v] = True
                self.bump_var(v)
                if self.level[v] >= cur_level:
                    path_c += 1
                else:
                    learnt.append(lit)
            while not seen[abs(self.trail[idx])]:
                idx -= 1
            p = abs(self.trail[idx])
            idx -= 1
            path_c -= 1
            if path_c == 0:
                break
            cid = self.reason[p]
        # 断言文字取反于 1-UIP 变量 p（其在 trail 中的极性）
        uip_lit = self.trail[idx + 1]
        learnt.insert(0, -uip_lit)
        learnt[1:] = sorted(learnt[1:], key=lambda lit: self.level[abs(lit)], reverse=True)
        bt = self.level[abs(learnt[1])] if len(learnt) > 1 else 0
        return learnt, bt

    def cancel_until(self, target):
        if len(self.trail_lim) <= target:
            return
        bound = self.trail_lim[target]
        for k in range(len(self.trail) - 1, bound - 1, -1):
            lit = self.trail[k]
            v = abs(lit)
            rid = self.reason[v]
            if rid != -1:
                c = self.db[rid]
                for watch_lit in (c[0], c[1]):
                    ws = self.watches[self.widx(watch_lit)]
                    if rid not in ws:
                        ws.append(rid)
            self.phase[v] = self.value[v]
            self.value[v] = 0
            self.reason[v] = -1
            self.level[v] = 0
        del self.trail[bound:]
        del self.trail_lim[target:]
        self.qhead = len(self.trail)

    def add_learnt(self, clause):
        cid = len(self.db)
        self.db.append(clause)
        if len(clause) == 1:
            self.watches[self.widx(clause[0])].append(cid)
        else:
            self.attach(cid)
        return cid

    def pick_branch_var(self):
        best = 0
        best_act = -1.0
        for v in range(1, self.n + 1):
            if self.value[v] == 0 and self.activity[v] > best_act:
                best_act = self.activity[v]
                best = v
        if best == 0:
            for v in range(1, self.n + 1):
                if self.value[v] == 0:
                    return v
        return best

    def solve(self):
        # 安装原始子句，同时收集顶层单元
        units = []
        for c in self.proof_orig:
            if not c:
                self.proof.append(())
                return False
            cid = len(self.db)
            self.db.append(list(c))
            if len(c) == 1:
                self.watches[self.widx(c[0])].append(cid)
                units.append(c[0])
            else:
                self.attach(cid)
        for u in units:
            if not self.enqueue(u):
                self.proof.append(())
                return False
        if self.propagate() != -1:
            self.proof.append(())
            return False

        luby_i = 1
        luby_k = 1
        base_limit = 100
        restart_limit = base_limit * luby_i

        while True:
            conflict = self.propagate()
            if conflict != -1:
                self.conflicts += 1
                if len(self.trail_lim) == 0:
                    # 0 层冲突：空子句相对当前公式是 RUP
                    self.proof.append(())
                    return False
                learnt, bt = self.analyze(conflict)
                self.proof.append(tuple(learnt))
                cid = self.add_learnt(learnt)
                self.cancel_until(bt)
                self.enqueue(learnt[0], cid)
                self.var_inc *= self.decay
                if self.conflicts >= restart_limit:
                    self.cancel_until(0)
                    luby_k += 1
                    luby_i = luby(luby_k)
                    restart_limit = self.conflicts + base_limit * luby_i
                continue

            if len(self.trail) == self.n:
                return True

            # 重启点也在传播无冲突后处理
            if self.conflicts >= restart_limit:
                self.cancel_until(0)
                luby_k += 1
                luby_i = luby(luby_k)
                restart_limit = self.conflicts + base_limit * luby_i
                continue

            v = self.pick_branch_var()
            if v == 0:
                return True
            self.trail_lim.append(len(self.trail))
            pol = self.phase[v] if self.phase[v] != 0 else -1
            self.enqueue(v if pol > 0 else -v, -1)


def luby(k):
    """返回 Luby 序列第 k 项（k 从 1 开始）。"""
    pos = k
    size = 1
    seq = 1
    while size < pos:
        seq += 1
        size = 2 * size + 1
    while True:
        if size == pos:
            return 1 << (seq - 1)
        half = (size - 1) // 2
        if pos <= half:
            size = half
            seq -= 1
        elif pos <= 2 * half:
            pos -= half
            size = half
            seq -= 1
        else:
            return 1 << (seq - 1)


def main():
    if len(sys.argv) != 2:
        print("usage: python3 solve.py <file.cnf>", file=sys.stderr)
        return 2
    nvars, clauses = parse_dimacs(sys.argv[1])
    solver = Solver(nvars, clauses)
    solver.proof_orig = clauses
    ok = solver.solve()
    if ok:
        model = []
        for v in range(1, nvars + 1):
            val = solver.value[v]
            if val == 0:
                val = 1
            model.append(str(v if val > 0 else -v))
        print("SAT")
        print(" ".join(model))
        return 0
    print("UNSAT")
    out = []
    for clause in solver.proof:
        out.append(" ".join(str(x) for x in clause) + " 0")
    sys.stdout.write("\n".join(out))
    if out:
        sys.stdout.write("\n")
    return 0


if __name__ == "__main__":
    sys.exit(main())
