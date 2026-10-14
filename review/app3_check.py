"""Independent check of Sect. 7.3 (asymmetric 1 -> 3 cloning), Examples 7.2 (d=2) and 7.3 (d=3).

R_true : {(p1,p2,p3)} from the direct SDP over the full d^4 x d^4 Choi matrix
         X = sum_sigma x_sigma psi_d(sigma) (24 diagrams of B_{1,3}), X >= 0, Tr X = d,
         p_i = (d <00|Tr_{others} X|00> - 1)/(d-1).      (no idempotents, no Schur basis)
R_paper: region described by the block SDPs (160)-(164) and (165)-(169) of the paper.
Both are compact convex sets; we compare their support functions h(w) = max w.p.
"""
import os
import sys

import cvxpy as cp
import numpy as np

sys.path.insert(0, os.path.dirname(__file__))
from wb import all_diagrams  # noqa
from app2_check import psi_matrix, independent_basis  # noqa

s2, s3, s6 = np.sqrt(2), np.sqrt(3), np.sqrt(6)
s15, s30 = np.sqrt(15), np.sqrt(30)


def true_problem(d):
    p, q = 1, 3
    mats = independent_basis([psi_matrix(m, d) for m in all_diagrams(p, q)])
    x = cp.Variable(len(mats))
    X = cp.Variable((d ** 4, d ** 4), PSD=True)
    cons = [X == sum(x[i] * mats[i] for i in range(len(mats))), cp.trace(X) == d]
    ps = []
    for i in (1, 2, 3):
        # <0, 0_i| Tr_{others} X |0, 0_i> = sum over the two other outputs
        idxs = []
        for a in range(d):
            for b in range(d):
                out = [None, None, None]
                others = [j for j in (1, 2, 3) if j != i]
                out[i - 1] = 0
                out[others[0] - 1], out[others[1] - 1] = a, b
                digits = [0] + out
                n = 0
                for t in digits:
                    n = n * d + t
                idxs.append(n)
        f = sum(X[n, n] for n in idxs)
        ps.append((d * f - 1) / (d - 1))
    return cons, ps


def paper_problem(d):
    if d == 2:
        X1 = cp.Variable((1, 1), PSD=True)
        X2 = cp.Variable((2, 2), PSD=True)
        X3 = cp.Variable((3, 3), PSD=True)
        A = lambda M, i, j: M[i - 1, j - 1]
        cons = [5 * A(X1, 1, 1) + A(X2, 1, 1) + A(X2, 2, 2) + 3 * A(X3, 1, 1) + 3 * A(X3, 2, 2) + 3 * A(X3, 3, 3) == 2]
        p1 = (3 * A(X3, 1, 1) + A(X2, 1, 1) + 5 * A(X1, 1, 1) + 3 * A(X3, 2, 2) + 9 * A(X3, 3, 3) + 3 * A(X2, 2, 2) - 3) / 3
        p2 = (6 * A(X3, 1, 1) + 5 * A(X2, 1, 1) + 10 * A(X1, 1, 1) + 15 * A(X3, 2, 2) + 3 * s3 * A(X3, 2, 3) + 3 * s3 * A(X3, 3, 2)
              + 9 * A(X3, 3, 3) + s3 * A(X2, 1, 2) + s3 * A(X2, 2, 1) + 3 * A(X2, 2, 2) - 6) / 6
        p3 = (14 * A(X3, 1, 1) + 5 * A(X2, 1, 1) + 10 * A(X1, 1, 1) + 2 * s2 * A(X3, 1, 2) + 2 * s2 * A(X3, 2, 1) + 7 * A(X3, 2, 2)
              + 9 * A(X3, 3, 3) + 2 * s6 * A(X3, 1, 3) + 2 * s6 * A(X3, 3, 1) + s3 * A(X3, 2, 3) + s3 * A(X3, 3, 2)
              - s3 * A(X2, 1, 2) - s3 * A(X2, 2, 1) + 3 * A(X2, 2, 2) - 6) / 6
        return cons, [p1, p2, p3]
    X1 = cp.Variable((1, 1), PSD=True)
    X2 = cp.Variable((2, 2), PSD=True)
    X3 = cp.Variable((3, 3), PSD=True)
    X4 = cp.Variable((3, 3), PSD=True)
    A = lambda M, i, j: M[i - 1, j - 1]
    cons = [A(X4, 1, 1) + 2 * A(X3, 1, 1) + 5 * A(X2, 1, 1) + 8 * A(X1, 1, 1) + A(X4, 2, 2) + A(X4, 3, 3)
            + 2 * A(X3, 2, 2) + 2 * A(X3, 3, 3) + 5 * A(X2, 2, 2) == 1]
    p1 = (3 * A(X4, 1, 1) + 6 * A(X3, 1, 1) + 15 * A(X2, 1, 1) + 24 * A(X1, 1, 1) + 3 * A(X4, 2, 2)
          + 12 * A(X4, 3, 3) + 6 * A(X3, 2, 2) + 24 * A(X3, 3, 3) + 15 * A(X2, 2, 2) - 4) / 8
    p2 = (3 * A(X4, 1, 1) + 6 * A(X3, 1, 1) + 15 * A(X2, 1, 1) + 24 * A(X1, 1, 1) + 11 * A(X4, 2, 2)
          + 2 * s2 * A(X4, 2, 3) + 2 * s2 * A(X4, 3, 2) + 4 * A(X4, 3, 3) + 22 * A(X3, 2, 2) + 4 * s2 * A(X3, 2, 3)
          + 4 * s2 * A(X3, 3, 2) + 8 * A(X3, 3, 3) + 15 * A(X2, 2, 2) - 4) / 8
    p3 = (9 * A(X4, 1, 1) + 21 * A(X3, 1, 1) + 15 * A(X2, 1, 1) + 24 * A(X1, 1, 1) + 8 * A(X3, 3, 3) + 15 * A(X2, 2, 2)
          + 5 * A(X4, 2, 2) + 7 * A(X3, 2, 2) + 4 * A(X4, 3, 3) + 2 * s3 * A(X4, 1, 2) + 2 * s3 * A(X4, 2, 1) - 4
          - s2 * A(X4, 2, 3) - s2 * A(X4, 3, 2) - s6 * A(X4, 3, 1) - s6 * A(X4, 1, 3) + s15 * A(X3, 1, 2)
          + s15 * A(X3, 2, 1) + s30 * A(X3, 3, 1) + s30 * A(X3, 1, 3) + s2 * A(X3, 2, 3) + s2 * A(X3, 3, 2)) / 8
    return cons, [p1, p2, p3]


def support(problem, w):
    cons, ps = problem
    obj = sum(w[i] * ps[i] for i in range(3))
    pr = cp.Problem(cp.Maximize(obj), cons)
    pr.solve(solver=cp.CLARABEL)
    return pr.value


if __name__ == '__main__':
    rng = np.random.default_rng(7)
    dirs = [np.array(v, float) for v in [(1, 0, 0), (0, 1, 0), (0, 0, 1), (-1, 0, 0), (0, -1, 0), (0, 0, -1),
                                         (1, 1, 1), (-1, -1, -1), (1, 1, 0), (1, -1, 0), (0, 1, -1), (1, 0, -1)]]
    dirs += [v / np.linalg.norm(v) for v in rng.normal(size=(30, 3))]
    for d in (2, 3):
        T, Pp = true_problem(d), paper_problem(d)
        worst = 0
        rows = []
        for w in dirs:
            ht, hp = support(T, w), support(Pp, w)
            worst = max(worst, abs(ht - hp))
            rows.append((w, ht, hp))
        print('d=%d: max |h_true - h_paper| over %d directions = %.2e' % (d, len(dirs), worst))
        for w, ht, hp in rows[:8]:
            print('   w=%s  true=%.6f  paper=%.6f' % (np.round(w, 3), ht, hp))
        # symmetric cloning: max p subject to p1=p2=p3
        cons, ps = T
        t = cp.Variable()
        pr = cp.Problem(cp.Maximize(t), cons + [ps[0] == t, ps[1] == t, ps[2] == t])
        pr.solve(solver=cp.CLARABEL)
        print('   symmetric optimum (true) = %.6f ; universal 1->3 cloner (3+d)/(3(1+d)) = %.6f' % (pr.value, (3 + d) / (3 * (1 + d))))
