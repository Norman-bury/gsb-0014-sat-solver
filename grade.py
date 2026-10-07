#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""task14（SAT 求解器）判分脚本。

规则：
1. 交付 solve.py，命令行 `python3 solve.py <实例.cnf>`，输出：
   - 可满足：第一行 SAT，第二行一个满足赋值（空格分隔的带符号变量）。
   - 不可满足：第一行 UNSAT，之后是 DRAT 证明，每行一条子句（整数序列以 0 结尾），
     最后必须是空子句（一行 0）。删除行以 d 开头。
2. 交付 verify.py，命令行 `python3 verify.py <实例.cnf> <证明.txt>`，
   证明有效打印 VALID 并退出 0，无效打印 INVALID 并退出非 0。
3. 判分用判分脚本自己内置的独立 DRAT 验证器逐份检查证明，不依赖模型的 verify.py。
   对每个实例：SAT 则独立校验赋值满足全部子句；UNSAT 则独立校验证明有效。
   此外对 verify.py 做自洽测试：它能接受 solve 自己产的证明、拒绝被篡改的证明。

用法：
  python3 grade.py
  python3 grade.py --solve path/to/solve.py --verify path/to/verify.py
"""

import argparse
import os
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
INSTANCES = os.path.join(HERE, "instances")


# ---------- DIMACS / DRAT 解析 ----------

def parse_dimacs(text):
    clauses = []
    for line in text.splitlines():
        line = line.strip()
        if not line:
            continue
        if line[0] == "p" or line[0] == "c" or line[0] == "%":
            continue
        toks = [int(t) for t in line.split()]
        if toks and toks[-1] == 0:
            toks = toks[:-1]
        clauses.append(toks)
    return clauses


def parse_proof(text):
    """返回 [(is_delete, clause)]。"""
    steps = []
    for line in text.splitlines():
        line = line.strip()
        if not line:
            continue
        if line[0] == "d":
            toks = [int(t) for t in line[1:].split()]
        else:
            toks = [int(t) for t in line.split()]
        if toks and toks[-1] == 0:
            toks = toks[:-1]
        steps.append((line[0] == "d", toks))
    return steps


# ---------- 独立 DRAT 验证器 ----------

def _unit_propagate(active, deleted, assign):
    """在 active 公式上做单元传播，assign 是 {var: bool}。返回 'conflict' 或 None。"""
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
                    lit_true = assign[v] if lit > 0 else (not assign[v])
                    if lit_true:
                        sat = True
                        break
                else:
                    unassigned.append(lit)
            if sat:
                continue
            if not unassigned:
                return "conflict"
            if len(unassigned) == 1:
                lit = unassigned[0]
                v = abs(lit)
                if v not in assign:
                    assign[v] = (lit > 0)
                    progressed = True
        if not progressed:
            return None


def rup_check(active, deleted, clause):
    """判断 clause 是否由 active 公式经反向单元传播（RUP）推出。"""
    assign = {}
    for lit in clause:
        v = abs(lit)
        assign[v] = (lit < 0)  # 令该文字为假
    return _unit_propagate(active, deleted, assign) == "conflict"


def verify_drat(clauses, steps):
    """独立验证 DRAT 证明。返回 (valid, message)。"""
    active = [list(c) for c in clauses]
    deleted = [False] * len(active)
    added_empty = False
    for i, (is_delete, clause) in enumerate(steps):
        if is_delete:
            # 删除一条已存在的子句
            found = False
            for j in range(len(active)):
                if not deleted[j] and sorted(active[j]) == sorted(clause):
                    deleted[j] = True
                    found = True
                    break
            if not found:
                return False, "第 %d 步：要删除的子句不存在 %s" % (i + 1, clause)
        else:
            if not rup_check(active, deleted, clause):
                return False, "第 %d 步：子句 %s 不是 RUP 推出" % (i + 1, clause)
            if clause == []:
                added_empty = True
            active.append(list(clause))
            deleted.append(False)
    if not added_empty:
        return False, "证明没有以空子句收尾，无法证明 UNSAT"
    return True, "证明有效"


# ---------- SAT 赋值校验 ----------

def verify_assignment(clauses, assign_line):
    """校验赋值满足全部子句。assign_line 是空格分隔的带符号变量。"""
    toks = assign_line.split()
    true_lits = set()
    for t in toks:
        v = int(t)
        if v == 0:
            continue
        true_lits.add(v)
    for c in clauses:
        if not any(l in true_lits for l in c):
            return False
    return True


# ---------- 主流程 ----------

def run(cmd):
    return subprocess.run(cmd, cwd=HERE, capture_output=True, text=True)


def grade_one(solve, name):
    cnf = os.path.join(INSTANCES, name)
    clauses = parse_dimacs(open(cnf).read())
    r = run([sys.executable, solve, cnf])
    if r.returncode != 0:
        return False, "solve 退出码非 0（%d）%s" % (r.returncode, r.stderr[-300:])
    lines = [l for l in r.stdout.splitlines() if l.strip() != ""]
    if not lines:
        return False, "solve 无输出"
    verdict = lines[0].strip().upper()
    if verdict == "SAT":
        if len(lines) < 2:
            return False, "SAT 但缺少赋值行"
        if not verify_assignment(clauses, lines[1]):
            return False, "给出的赋值不满足全部子句"
        return True, "SAT，赋值校验通过"
    elif verdict == "UNSAT":
        proof_text = "\n".join(lines[1:])
        steps = parse_proof(proof_text)
        if not steps:
            return False, "UNSAT 但没有给出证明"
        ok, msg = verify_drat(clauses, steps)
        if not ok:
            return False, "DRAT 证明无效：" + msg
        return True, "UNSAT，证明经独立验证器校验通过"
    else:
        return False, "无法识别的判定行：" + lines[0]


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--solve", default=os.path.join(HERE, "solve.py"))
    ap.add_argument("--verify", default=os.path.join(HERE, "verify.py"))
    ap.add_argument("--instances", default=INSTANCES)
    args = ap.parse_args()

    print("=" * 60)
    print("判分开始")

    if not os.path.exists(args.solve):
        print("[FAIL] 找不到 solve.py（%s）" % args.solve)
        sys.exit(1)

    names = sorted(f for f in os.listdir(args.instances) if f.endswith(".cnf"))
    all_ok = True
    for name in names:
        ok, msg = grade_one(args.solve, name)
        print("[%s] %s : %s" % ("OK" if ok else "FAIL", name, msg))
        if not ok:
            all_ok = False

    # verify.py 自洽测试：对 solve 产出有效 UNSAT 证明的实例，验证 verify.py 接受
    # solve 自己的证明、拒绝被篡改的证明
    if os.path.exists(args.verify):
        for name in names:
            cnf = os.path.join(INSTANCES, name)
            clauses = parse_dimacs(open(cnf).read())
            r = run([sys.executable, args.solve, cnf])
            lines = [l for l in r.stdout.splitlines() if l.strip() != ""]
            if not lines or lines[0].strip().upper() != "UNSAT":
                continue
            steps = parse_proof("\n".join(lines[1:]))
            if not steps or not verify_drat(clauses, steps)[0]:
                continue  # 证明本身无效，已由上面的独立校验拦下
            proof = "\n".join(lines[1:]) + "\n"
            import tempfile
            pf = tempfile.NamedTemporaryFile("w", suffix=".txt", delete=False)
            pf.write(proof)
            pf.close()
            rv = run([sys.executable, args.verify, cnf, pf.name])
            acc = rv.stdout.strip().upper().startswith("VALID")
            # 篡改：把证明里第一个非空子句行换成乱写
            bad_lines = list(lines[1:])
            if bad_lines:
                bad_lines[0] = "999999 0"
            bad = "\n".join(bad_lines) + "\n"
            bf = tempfile.NamedTemporaryFile("w", suffix=".txt", delete=False)
            bf.write(bad)
            bf.close()
            rb = run([sys.executable, args.verify, cnf, bf.name])
            rej = rb.stdout.strip().upper().startswith("INVALID")
            if not acc or not rej:
                print("[FAIL] verify.py 自洽测试不过（%s：接受=%s 拒绝=%s）" % (name, acc, rej))
                all_ok = False
            os.unlink(pf.name)
            os.unlink(bf.name)
    else:
        print("[FAIL] 找不到 verify.py（%s）" % args.verify)
        all_ok = False

    print("=" * 60)
    print("总结论：", "PASS" if all_ok else "FAIL")
    sys.exit(0 if all_ok else 1)


if __name__ == "__main__":
    main()
