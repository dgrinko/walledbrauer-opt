"""Is the block extraction in app3.nb basis-independent?

app3.nb builds U from an arbitrary orthonormal basis of Im(psi(eps_T)) for every path T separately
(Eigensystem + Orthogonalize) and then reads block lambda off the first basis vector of every path.
This is only correct if the bases of different paths T,T' with the same leaf are aligned
(related by the matrix units eps_{TT'}). Here we redo the cloning feasibility (d=2, 1->3) with
(a) aligned bases and (b) random orthonormal bases, and compare h(w) = max w.p with the true region.
"""
import os
import sys
from fractions import Fraction

import cvxpy as cp
import numpy as np

sys.path.insert(0, os.path.dirname(__file__))
from wb import *  # noqa
from app2_check import psi_matrix, independent_basis  # noqa
from app3_check import true_problem, support  # noqa

d, p, q = 2, 1, 3
DB = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'wba_idempotents_db')
db = parse_db(open(os.path.join(DB, 'primitive_1_3_2.txt')).read(),
              Algebra(p, q, d), Fraction(d), Fraction(1))
Pi = {T: sum(float(c) * psi_matrix(m, d) for m, c in e.c.items()) for T, e in db.items()}
leaves = {}
for T in db:
    leaves.setdefault(T[-1], []).append(T)
rng = np.random.default_rng(11)


def image_basis(P, random_rotation):
    w, V = np.linalg.eigh((P + P.T) / 2)
    B = V[:, w > 0.5]
    if random_rotation and B.shape[1] > 1:
        Q, _ = np.linalg.qr(rng.normal(size=(B.shape[1], B.shape[1])))
        B = B @ Q
    return B


def first_vectors(mode):
    vecs = {}
    Hrand = rng.normal(size=(d ** 4, d ** 4))
    Hrand = Hrand + Hrand.T
    for lam, Ts in leaves.items():
        if mode == 'aligned':
            # Appendix D idea: v_T proportional to Pi_T H Pi_T1 v_T1 for a generic H in the commutant
            Hc = sum(rng.normal() * Mx for Mx in independent_basis([psi_matrix(m, d) for m in all_diagrams(p, q)]))
            v1 = image_basis(Pi[Ts[0]], False)[:, 0]
            vecs[Ts[0]] = v1
            for T in Ts[1:]:
                v = Pi[T] @ Hc @ v1
                vecs[T] = v / np.linalg.norm(v)
        else:
            for T in Ts:
                vecs[T] = image_basis(Pi[T], True)[:, 0]
    return vecs


def block_problem(vecs):
    mats = independent_basis([psi_matrix(m, d) for m in all_diagrams(p, q)])
    x = cp.Variable(len(mats))
    M = sum(x[i] * mats[i] for i in range(len(mats)))
    cons = [cp.trace(M) == d]
    for lam, Ts in leaves.items():
        V = np.array([vecs[T] for T in Ts]).T          # columns = first vectors
        Bk = V.T @ M @ V
        n = len(Ts)
        Y = cp.Variable((n, n), PSD=True)
        cons.append(Y == (Bk + Bk.T) / 2)
    # p_i computed from the full matrix as in app3.nb
    ps = []
    for i in (1, 2, 3):
        idxs = []
        for a in range(d):
            for b in range(d):
                out = [None] * 3
                others = [j for j in (1, 2, 3) if j != i]
                out[i - 1] = 0
                out[others[0] - 1], out[others[1] - 1] = a, b
                n_ = 0
                for t in [0] + out:
                    n_ = n_ * d + t
                idxs.append(n_)
        f = sum(M[n_, n_] for n_ in idxs)
        ps.append((d * f - 1) / (d - 1))
    return cons, ps


if __name__ == '__main__':
    dirs = [np.array(v, float) for v in [(1, 1, 1), (-1, -1, -1), (1, 0, 0), (1, 1, 0), (1, -1, 0), (-1, 0, 0)]]
    T = true_problem(d)
    print('leaf -> number of paths:', {k: len(v) for k, v in leaves.items()})
    for mode in ('aligned', 'random', 'random'):
        Pp = block_problem(first_vectors(mode))
        print('%-8s ' % mode + '  '.join('h%s: true=%.4f blocks=%.4f' % (tuple(int(t) for t in w), support(T, w), support(Pp, w)) for w in dirs[:4]))
