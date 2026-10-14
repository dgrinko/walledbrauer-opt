"""Independent check of Sect. 7.2 (quantum majority vote, p=3 inputs, q=1 output).

Two independent formulations, both with the matrices built explicitly (d^4 x d^4):
 (A) LP: X = sum_T v_T psi_d(eps_T) with the idempotents from the repo DB (GT symmetry, eq. (157)),
     trace preservation imposed numerically on the full matrix (valid for every d, incl. d = 2).
 (B) SDP: X = sum_sigma x_sigma psi_d(sigma) over all 24 walled Brauer diagrams of B_{3,1}
     (unitary equivariance only, no extra symmetry, no idempotents), X >= 0.
Each is solved for the relation of eq. (156) with and without the '123 -> {1,2,3}' rule.
"""
import itertools
import os
import sys
from fractions import Fraction

import cvxpy as cp
import numpy as np
from scipy.optimize import linprog

sys.path.insert(0, os.path.dirname(__file__))
from wb import *  # noqa

DB = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'wba_idempotents_db')
p, q = 3, 1
k = p + q


def psi_matrix(m, d):
    """Rows = top labels (big-endian over nodes 1..k), columns = bottom labels."""
    k = len(m) // 2
    eye = np.eye(d)
    letters = 'abcdefghijklmnopqrstuvwxyz'
    lab = [None] * (2 * k)
    specs, ops = [], []
    seen = set()
    li = 0
    for x in range(2 * k):
        if x in seen:
            continue
        y = m[x]
        seen.update((x, y))
        a, b = letters[li], letters[li + 1]
        li += 2
        lab[x], lab[y] = a, b
        specs.append(a + b)
        ops.append(eye)
    out = ''.join(lab[:k]) + ''.join(lab[k:])
    T = np.einsum(','.join(specs) + '->' + out, *ops)
    return T.reshape(d ** k, d ** k)


def lc_matrix(lc, d):
    M = np.zeros((d ** k, d ** k))
    for m, c in lc.c.items():
        M += float(c) * psi_matrix(m, d)
    return M


def idx(digits, d):
    i = 0
    for t in digits:
        i = i * d + t
    return i


def relation(d, with123):
    """Majority relation (156) on all orderings of the inputs (the SDP has no S3 symmetry imposed)."""
    reps = [((0, 0, 0), [0]), ((0, 0, 1), [0])]
    if with123 and d >= 3:
        reps.append(((0, 1, 2), [0, 1, 2]))
    rel = []
    for x, ys in reps:
        for perm in sorted(set(itertools.permutations(range(3)))):
            xp = tuple(x[i] for i in perm)
            if (xp, ys) not in rel:
                rel.append((xp, ys))
    return rel


def ptrace_out(M, d):
    """Trace out the last tensor factor (the single output system)."""
    T = M.reshape(d ** p, d, d ** p, d)
    return np.einsum('aibi->ab', T)


def load_idempotents(d):
    fname = 'primitive_3_1.txt' if d >= 4 else 'primitive_3_1_%d.txt' % d
    alg = Algebra(p, q, d)
    text = open(os.path.join(DB, fname)).read()
    db = parse_db(text, alg, Fraction(d), Fraction(1))
    return db


def solve_lp(d, with123, sym=True):
    db = load_idempotents(d)
    paths = list(db)
    mats = [lc_matrix(db[T], d) for T in paths]
    for Mt in mats:  # sanity: projectors
        assert np.allclose(Mt @ Mt, Mt, atol=1e-9)
    n = len(paths)
    # variables: v_1..v_n, F ; maximise F
    A_ub, b_ub = [], []
    for x, ys in relation(d, with123):
        row = [-sum(Mt[idx(x + (y,), d), idx(x + (y,), d)] for y in ys) for Mt in mats] + [1.0]
        A_ub.append(row)
        b_ub.append(0.0)
    A_eq, b_eq = [], []
    PT = [ptrace_out(Mt, d) for Mt in mats]
    I = np.eye(d ** p)
    for a in range(d ** p):
        for b in range(d ** p):
            row = [P_[a, b] for P_ in PT] + [0.0]
            if any(abs(r) > 1e-12 for r in row) or abs(I[a, b]) > 0:
                A_eq.append(row)
                b_eq.append(I[a, b])
    if sym:  # S3 x S1 symmetry (Prop. 6.2): equal weights for paths sharing the last edge
        groups = {}
        for i, T in enumerate(paths):
            groups.setdefault((T[-2], T[-1]), []).append(i)
        for g in groups.values():
            for i in g[1:]:
                row = [0.0] * (n + 1)
                row[g[0]], row[i] = 1.0, -1.0
                A_eq.append(row)
                b_eq.append(0.0)
    res = linprog(c=[0.0] * n + [-1.0], A_ub=A_ub, b_ub=b_ub, A_eq=A_eq, b_eq=b_eq,
                  bounds=[(0, None)] * n + [(None, None)], method='highs')
    assert res.status == 0, res.message
    return -res.fun, dict(zip(paths, res.x[:n]))


def independent_basis(mats):
    """Symmetrised, linearly independent basis of span{psi(sigma)} (handles d < p+q)."""
    sym = [(M + M.T) / 2 for M in mats]
    V = np.array([S.ravel() for S in sym])
    basis = []
    cur = np.zeros((0, V.shape[1]))
    for i in range(len(sym)):
        cand = np.vstack([cur, V[i]])
        if np.linalg.matrix_rank(cand, tol=1e-9) > cur.shape[0]:
            cur = cand
            basis.append(sym[i])
    return basis


def solve_sdp(d, with123, solver=None):
    mats = independent_basis([psi_matrix(m, d) for m in all_diagrams(p, q)])
    nb = len(mats)
    x = cp.Variable(nb)
    F = cp.Variable()
    Y = cp.Variable((d ** k, d ** k), PSD=True)
    cons = [Y == sum(x[i] * mats[i] for i in range(nb))]
    for xx, ys in relation(d, with123):
        cons.append(sum(Y[idx(xx + (y,), d), idx(xx + (y,), d)] for y in ys) >= F)
    # trace preservation Tr_out X = I, as independent linear equations in x
    PT = np.array([ptrace_out(M, d).ravel() for M in mats]).T     # (d^2p) x nb
    rhs = np.eye(d ** p).ravel()
    r = np.linalg.matrix_rank(PT, tol=1e-9)
    U, s, Vt = np.linalg.svd(PT, full_matrices=False)
    A = np.diag(s[:r]) @ Vt[:r]          # independent rows spanning the row space
    b = U[:, :r].T @ rhs
    assert np.allclose(U[:, :r] @ b, rhs), 'identity not in range of partial trace'
    cons.append(A @ x == b)
    prob = cp.Problem(cp.Maximize(F), cons)
    prob.solve(solver=solver or cp.CLARABEL)
    return prob.value


if __name__ == '__main__':
    # the unrestricted SDP is a dense d^4 x d^4 problem: d <= 3 is cheap, d = 4 needs a lot of memory
    for d in [int(a) for a in sys.argv[1:]] or [2, 3]:
        out = []
        for w in (False, True):
            if d == 2 and w:
                continue
            lp, sol = solve_lp(d, w)
            lp_nosym, _ = solve_lp(d, w, sym=False)
            print('   d=%d %s LP(S3xS1)=%.10f LP(GT)=%.10f' % (d, 'with 123' if w else 'no 123', lp, lp_nosym), flush=True)
            sdp = solve_sdp(d, w) if d <= 3 else float('nan')
            out.append('%s: LP(S3xS1)=%.9f LP(GT)=%.9f SDP=%.9f' % ('with 123' if w else 'no 123  ', lp, lp_nosym, sdp))
        print('d=%d  ' % d + ' | '.join(out), flush=True)
    print('8/9 =', 8 / 9)
