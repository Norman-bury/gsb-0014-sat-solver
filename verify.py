#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""独立 DRAT 证明验证器。

用法: python3 verify.py <instance.cnf> <proof.txt>
有效打印 VALID 退出 0，无效打印 INVALID 退出非 0。
"""
import sys


def parse_dimacs(path):
    clauses = []
    with open(path) as f:
        for line in f:
            line = line.strip()
            if not line or line[0] in "cp%":
                continue
            toks = [int(t) for t in line.split()]
            if toks and toks[-1] == 0:
                toks = toks[:-1]
            clauses.append(toks)
    return clauses


def parse_proof(path):
    steps = []
    with open(path) as f:
        for line in f:
            line = line.strip()
            if not line:
                continue
            is_del = line[0] == "d"
            body = line[1:] if is_del else line
            toks = [int(t) for t in body.split()]
            if toks and toks[-1] == 0:
                toks = toks[:-1]
            steps.append((is_del, toks))
    return steps


def unit_propagate(active, deleted, assign):
    while True:
        progressed = False
        for i, c in enumerate(active):
            if deleted[i]:
                continue
            sat = False
            unassigned = []
            for lit in c:
                v = abs(lit)
                if v in assign:
                    if (assign[v] and lit > 0) or (not assign[v] and lit < 0):
                        sat = True
                        break
                else:
                    unassigned.append(lit)
            if sat:
                continue
            if not unassigned:
                return True  # conflict
            if len(unassigned) == 1:
                lit = unassigned[0]
                v = abs(lit)
                if v not in assign:
                    assign[v] = lit > 0
                    progressed = True
        if not progressed:
            return False


def rup_check(active, deleted, clause):
    assign = {}
    for lit in clause:
        assign[abs(lit)] = lit < 0
    return unit_propagate(active, deleted, assign)


def verify(clauses, steps):
    active = [list(c) for c in clauses]
    deleted = [False] * len(active)
    added_empty = False
    for i, (is_del, clause) in enumerate(steps):
        if is_del:
            key = sorted(clause)
            found = False
            for j in range(len(active)):
                if not deleted[j] and sorted(active[j]) == key:
                    deleted[j] = True
                    found = True
                    break
            if not found:
                return False, "step %d: deleted clause not found %s" % (i + 1, clause)
        else:
            if not rup_check(active, deleted, clause):
                return False, "step %d: clause %s is not RUP" % (i + 1, clause)
            if clause == []:
                added_empty = True
            active.append(list(clause))
            deleted.append(False)
    if not added_empty:
        return False, "proof does not end with the empty clause"
    return True, "ok"


def main():
    if len(sys.argv) != 3:
        print("usage: verify.py <instance.cnf> <proof.txt>", file=sys.stderr)
        sys.exit(2)
    clauses = parse_dimacs(sys.argv[1])
    steps = parse_proof(sys.argv[2])
    ok, msg = verify(clauses, steps)
    print("VALID" if ok else "INVALID")
    if not ok:
        print(msg, file=sys.stderr)
    sys.exit(0 if ok else 1)


if __name__ == "__main__":
    main()
