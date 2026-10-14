"""Diagrammatic (d-independent size) version of the majority-vote LP (158), exact in d via Fractions.

Matrix elements <x|psi(sigma)|x> and partial traces are evaluated diagrammatically (Appendix A),
trace preservation is imposed by matching coefficients of the 3! diagrams of B_{3,0} (valid for d >= 3).
"""
import os
import sys
from fractions import Fraction as Fr

import numpy as np
from scipy.optimize import linprog

sys.path.insert(0, os.path.dirname(__file__))
from wb import *  # noqa

DB = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'wba_idempotents_db')
p, q, k = 3, 1, 4


def diag_elem(m, labels):
    """<x|psi(sigma)|x> with top and bottom labels both equal to x."""
    kk = len(m) // 2
    lab = lambda pt: labels[pt % kk]
    return int(all(lab(a) == lab(m[a]) for a in range(2 * kk)))


def ptrace_last(m):
    """Contract top node k with bottom node k. Returns (diagram on k-1 nodes, loops)."""
    kk = len(m) // 2
    top, bot = kk - 1, 2 * kk - 1
    if m[top] == bot:
        rest_loops = 1
        pairs = [(a, m[a]) for a in range(2 * kk) if a not in (top, bot) and a < m[a]]
    else:
        rest_loops = 0
        u, v = m[top], m[bot]
        pairs = [(a, m[a]) for a in range(2 * kk) if a not in (top, bot, u, v) and a < m[a]] + [(u, v)]
    remap = lambda a: a if a < kk else a - 1   # drop the two removed points
    new = [None] * (2 * (kk - 1))
    for a, b in pairs:
        ra, rb = remap(a), remap(b)
        new[ra], new[rb] = rb, ra
    return tuple(new), rest_loops


def lp(d, with123, db=None, solution=None):
    if db is None:
        fname = 'primitive_3_1.txt' if d >= 4 else 'primitive_3_1_%d.txt' % d
        db = parse_db(open(os.path.join(DB, fname)).read(), Algebra(p, q, d), Fr(d), Fr(1))
    paths = list(db)
    n = len(paths)
    reps = [((0, 0, 0), [0]), ((0, 0, 1), [0])] + ([((0, 1, 2), [0, 1, 2])] if with123 else [])
    fid = [[sum(c * diag_elem(m, x + (y,)) for m, c in db[T].c.items() for y in ys) for T in paths] for x, ys in reps]
    # trace constraint: Tr_out sum_T v_T eps_T = identity of B_{3,0}
    targets = all_diagrams(3, 0)
    ident = identity(3)
    A_eq, b_eq = [], []
    for tgt in targets:
        row = []
        for T in paths:
            s = Fr(0)
            for m, c in db[T].c.items():
                mm, l = ptrace_last(m)
                if mm == tgt:
                    s += c * Fr(d) ** l
            row.append(s)
        A_eq.append(row)
        b_eq.append(Fr(1) if tgt == ident else Fr(0))
    groups = {}
    for i, T in enumerate(paths):
        groups.setdefault((T[-2], T[-1]), []).append(i)
    sym = []
    for g in groups.values():
        for i in g[1:]:
            r = [0] * n
            r[g[0]], r[i] = 1, -1
            sym.append(r)
    if solution is not None:
        v = solution
        return dict(fid=[sum(f[i] * v[i] for i in range(n)) for f in fid],
                    tp=[sum(A_eq[j][i] * v[i] for i in range(n)) - b_eq[j] for j in range(len(A_eq))])
    c = [0.0] * n + [-1.0]
    A_ub = [[-float(f[i]) for i in range(n)] + [1.0] for f in fid]
    res = linprog(c, A_ub=A_ub, b_ub=[0.0] * len(A_ub),
                  A_eq=[[float(a) for a in r] + [0.0] for r in A_eq] + [list(map(float, r)) + [0.0] for r in sym],
                  b_eq=[float(b) for b in b_eq] + [0.0] * len(sym),
                  bounds=[(0, None)] * n + [(None, None)], method='highs')
    assert res.status == 0
    return -res.fun, res.x[:n], paths


def original_solution(d):
    """Closed form printed in the originally published app2.nb ('General d solution'; replaced by
    corrected_solution in the current app2.nb), weights in DB path order."""
    return [0, 0, 0, Fr(d - 2, (d - 3) * (d + 1)), Fr(d + 2, 3), 0, 0, Fr(2 * (d + 1), 3), Fr(2 * (d + 1), 3), 0]


def corrected_solution(d):
    """Closed form satisfying all three rules of eq. (156) for every d >= 3 (equals app2.nb's d = 3 solution;
    the 'General d solution' of the current app2.nb)."""
    return [0, 0, 0, 0, Fr(d + 2, 3), 0, 0, Fr(2 * (d + 1), 3), Fr(2 * (d + 1), 3), Fr(d - 2, 3)]


if __name__ == '__main__':
    for d in [3, 4, 5, 8, 9, 10, 12, 16, 20, 50, 100]:
        F0, _, _ = lp(d, False)
        F1, v, paths = lp(d, True)
        out = 'd=%3d  LP F(no 123)=%.10f  F(with 123)=%.10f' % (d, F0, F1)
        if d >= 4:
            for name, sol in (('original notebook', original_solution(d)), ('corrected', corrected_solution(d))):
                chk = lp(d, True, solution=sol)
                out += '  | %s: F=(%s) TP-residual=%s' % (name, ', '.join(str(x) for x in chk['fid']),
                                                          max(abs(x) for x in chk['tp']))
        print(out, flush=True)
    # F_123 of the original notebook's closed-form solution equals (5d+8)/(6(d+1)) -> below 8/9 for d >= 9
    for D in range(4, 13):
        assert lp(D, True, solution=original_solution(D))['fid'][2] == Fr(5 * D + 8, 6 * (D + 1))
    print('F_123(original notebook solution) == (5d+8)/(6(d+1)) for d = 4..12')
