"""Verify every file in wba_idempotents_db independently of Sage.

Symbolic files primitive_p_q.txt (coefficients in Q(z)):  evaluate z at a random element of GF(2^61-1)
and check, inside the walled Brauer algebra B^z_{p,q}:
  * the set of keys == all root-leaf paths of the (untruncated) Bratteli diagram
  * sum_T eps_T == 1
  * J_k eps_T == eps_T J_k == c_T(k) eps_T for all k (contents from paper Sect. 5.3)
  * content vectors are pairwise distinct
  * Tr(eps_T) == dim of the U(d) irrep lambda (Weyl dimension polynomial, evaluated at z)
  * eps_T^2 == eps_T directly (for p+q <= 5)
Numeric files primitive_p_q_d.txt: coefficients in Q, delta = d. The elements only need to be idempotents
after applying psi_d, so the identities are checked on random vectors in (C^d)^{p+q} (mod 2^31-1, exact).
"""
import glob
import os
import random
import string
import sys
import time
from fractions import Fraction

import numpy as np

sys.path.insert(0, os.path.dirname(__file__))
from wb import *  # noqa

DB = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'wba_idempotents_db')
P31 = (1 << 31) - 1
random.seed(1)


def lagrange_eval(xs, ys, x):
    tot = Fp(0)
    for i, (xi, yi) in enumerate(zip(xs, ys)):
        term = Fp(yi)
        for j, xj in enumerate(xs):
            if j != i:
                term = term * (x - xj) / Fp(xi - xj)
        tot = tot + term
    return tot


def weyl_poly_at(lam, z):
    deg = sum(lam[0]) + sum(lam[1])
    d0 = len(lam[0]) + len(lam[1]) + 1
    xs = list(range(d0, d0 + deg + 1))
    ys = [weyl_dim(lam, x) for x in xs]
    assert all(y.denominator == 1 for y in ys)
    return lagrange_eval(xs, [int(y) for y in ys], z)


def contents(path, p, delta):
    return tuple(edge_content(path[i - 1], path[i], i, p, delta) for i in range(1, len(path)))


# ------------------------------------------------------------- psi_d on vectors (mod P31)

def psi_apply(m, d, v):
    """(psi(sigma) v)[top x] = sum_{bottom y} [x,y consistent with sigma] v[y]."""
    k = len(m) // 2
    letters = iter(string.ascii_letters)
    top = [None] * k
    bot = [None] * k
    extra_ops, extra_specs = [], []
    seen = set()
    for x in range(2 * k):
        if x in seen:
            continue
        y = m[x]
        seen.update((x, y))
        if x < k and y < k:                       # cup in top row
            a, b = next(letters), next(letters)
            top[x], top[y] = a, b
            extra_ops.append(np.eye(d, dtype=np.int64))
            extra_specs.append(a + b)
        elif x >= k and y >= k:                   # cap in bottom row
            a = next(letters)
            bot[x - k], bot[y - k] = a, a
        else:                                     # through line
            a = next(letters)
            t, b = (x, y - k) if x < k else (y, x - k)
            top[t], bot[b] = a, a
    spec = ''.join(bot) + (',' + ','.join(extra_specs) if extra_specs else '') + '->' + ''.join(top)
    return np.einsum(spec, v, *extra_ops) % P31


def psi_lc_apply(lc, d, v, coef_mod):
    out = np.zeros_like(v)
    for m, c in lc.c.items():
        cm = coef_mod(c)
        if cm:
            out = (out + cm * psi_apply(m, d, v)) % P31
    return out


def frac_mod(c):
    c = Fraction(c)
    return c.numerator % P31 * pow(c.denominator % P31, P31 - 2, P31) % P31


# ------------------------------------------------------------- checks

def check_symbolic(p, q, path_file, direct_square):
    k = p + q
    z = Fp(random.randrange(10 ** 6, P61))
    alg = Algebra(p, q, z)
    one = Fp(1)
    db = parse_db(open(path_file).read(), alg, z, one)
    errs = []
    exp_paths = {tuple(P) for P in all_paths(p, q)}
    if set(db) != exp_paths:
        errs.append('path set mismatch: %d stored vs %d expected' % (len(db), len(exp_paths)))
    total = LC(alg)
    for e in db.values():
        total = total + e
    if not (total - LC(alg, {identity(k): one})).is_zero():
        errs.append('sum of idempotents != 1')
    J = [None] + [jm(alg, kk, one) for kk in range(1, k + 1)]
    cvs = {}
    for T, e in db.items():
        cT = contents(T, p, z)
        cvs.setdefault(tuple(x.v if isinstance(x, Fp) else Fp(x).v for x in cT), []).append(T)
        for kk in range(1, k + 1):
            c = Fp(cT[kk - 1])
            if not (J[kk] * e - c * e).is_zero():
                errs.append('J_%d eps != c eps for %s' % (kk, T))
            if not (e * J[kk] - c * e).is_zero():
                errs.append('eps J_%d != c eps for %s' % (kk, T))
        if not (e.trace() == weyl_poly_at(T[-1], z)):
            errs.append('trace mismatch for %s' % (T,))
        if direct_square and not (e * e - e).is_zero():
            errs.append('eps^2 != eps for %s' % (T,))
    if any(len(v) > 1 for v in cvs.values()):
        errs.append('content vectors not distinct')
    return len(db), errs


def check_numeric(p, q, d, path_file, nvec=2):
    k = p + q
    alg = Algebra(p, q, d)
    one = Fraction(1)
    db = parse_db(open(path_file).read(), alg, None, one)
    errs = []
    exp_paths = {tuple(P) for P in all_paths(p, q, d)}
    if set(db) != exp_paths:
        errs.append('path set mismatch: %d stored vs %d expected' % (len(db), len(exp_paths)))
    rng = np.random.default_rng(0)
    vs = [rng.integers(0, P31, size=(d,) * k, dtype=np.int64) for _ in range(nvec)]
    J = [None] + [jm(alg, kk, one) for kk in range(1, k + 1)]
    total = LC(alg)
    for e in db.values():
        total = total + e
    diff = total - LC(alg, {identity(k): one})
    for v in vs:
        if psi_lc_apply(diff, d, v, frac_mod).any():
            errs.append('psi(sum eps) != I')
    for T, e in db.items():
        cT = contents(T, p, d)
        for kk in range(1, k + 1):
            for R, side in ((J[kk] * e - cT[kk - 1] * e, 'left'), (e * J[kk] - cT[kk - 1] * e, 'right')):
                for v in vs:
                    if psi_lc_apply(R, d, v, frac_mod).any():
                        errs.append('psi(J_%d eps - c eps) != 0 (%s) for %s' % (kk, side, T))
                        break
        for v in vs:
            ev = psi_lc_apply(e, d, v, frac_mod)
            eev = psi_lc_apply(e, d, ev, frac_mod)
            if ((eev - ev) % P31).any():
                errs.append('psi(eps)^2 != psi(eps) for %s' % (T,))
        tr = e.trace()
        if tr != weyl_dim(T[-1], d):
            errs.append('trace %s != dim %s for %s' % (tr, weyl_dim(T[-1], d), T))
    return len(db), errs


def main():
    files = sorted(glob.glob(os.path.join(DB, 'primitive_*.txt')),
                   key=lambda f: (sum(map(int, os.path.basename(f)[10:-4].split('_')[:2])), f))
    only = sys.argv[1:] if len(sys.argv) > 1 else None
    bad = 0
    for f in files:
        name = os.path.basename(f)
        parts = list(map(int, name[len('primitive_'):-4].split('_')))
        if only and name not in only:
            continue
        t0 = time.time()
        if len(parts) == 2:
            p, q = parts
            n, errs = check_symbolic(p, q, f, direct_square=(p + q <= 5))
        else:
            p, q, d = parts
            n, errs = check_numeric(p, q, d, f)
        bad += bool(errs)
        print('%-24s paths=%4d  %s  (%.1fs)' % (name, n, 'OK' if not errs else 'FAIL: ' + '; '.join(errs[:5]),
                                                time.time() - t0), flush=True)
    print('files with errors:', bad)


if __name__ == '__main__':
    main()
