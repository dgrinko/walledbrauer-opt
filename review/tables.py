"""Recompute Tables 4-7 of the paper (Appendix E) independently.

Table 4: |Irr(A^d_{p,q})| = #bipartitions (l, r), l |- p-k, r |- q-k, len(l)+len(r) <= d.
Table 6: sum_lambda d_lambda = #root-leaf paths of the truncated Bratteli diagram.
Table 7: dim A^d_{p,q} = dim A^d_{p+q} = sum_{lambda |- p+q, len <= d} (f^lambda)^2.
Table 5: dim of the commutant of U(d) x S_p x S_q on V^{p,q}
         = int |chi(g)|^2 = 1/(p!q!) sum_{pi,sigma} int |p_{type(pi) u type(sigma)}(U)|^2 dU
         = sum_{alpha |- p, beta |- q} 1/(z_alpha z_beta) sum_{lambda |- p+q, len<=d} chi^lambda(alpha u beta)^2
"""
import sys, os
from fractions import Fraction
from functools import lru_cache
from math import factorial
from collections import Counter

sys.path.insert(0, os.path.dirname(__file__))
from wb import partitions, all_paths


def n_brauer(p, q, d):
    return sum(1 for k in range(min(p, q) + 1) for l in partitions(p - k) for r in partitions(q - k)
               if len(l) + len(r) <= d)


def n_gt(p, q, d):
    return len(all_paths(p, q, d))


def f_lambda(lam):
    n = sum(lam)
    h = 1
    lamc = [sum(1 for x in lam if x > j) for j in range(lam[0])] if lam else []
    for i, row in enumerate(lam):
        for j in range(row):
            h *= (row - j - 1) + (lamc[j] - i - 1) + 1
    return factorial(n) // h


def dim_A(n, d):
    return sum(f_lambda(l) ** 2 for l in partitions(n) if len(l) <= d)


@lru_cache(maxsize=None)
def chi(lam, mu):
    """Murnaghan-Nakayama: chi^lam evaluated at cycle type mu (tuple, any order)."""
    if not mu:
        return 1 if sum(lam) == 0 else 0
    r, rest = mu[0], mu[1:]
    # remove border strips of size r; use beta-numbers
    L = len(lam)
    beta = [lam[i] + (L - 1 - i) for i in range(L)]
    total = 0
    bset = set(beta)
    for b in beta:
        nb = b - r
        if nb >= 0 and nb not in bset:
            # sign = (-1)^(number of beta numbers strictly between nb and b)
            h = sum(1 for x in beta if nb < x < b)
            newbeta = sorted([x for x in beta if x != b] + [nb], reverse=True)
            Ln = len(newbeta)
            newlam = tuple(x - (Ln - 1 - i) for i, x in enumerate(newbeta))
            newlam = tuple(x for x in newlam if x > 0)
            total += (-1) ** h * chi(newlam, rest)
    return total


def z_alpha(alpha):
    c = Counter(alpha)
    z = 1
    for part, m in c.items():
        z *= part ** m * factorial(m)
    return z


def n_spsq(p, q, d):
    tot = Fraction(0)
    lams = [l for l in partitions(p + q) if len(l) <= d]
    for a in partitions(p):
        for b in partitions(q):
            mu = tuple(sorted(a + b, reverse=True))
            s = sum(chi(l, mu) ** 2 for l in lams)
            tot += Fraction(s, z_alpha(a) * z_alpha(b))
    assert tot.denominator == 1
    return int(tot)


if __name__ == '__main__':
    # sanity: characters orthonormal
    for n in range(1, 8):
        for l in partitions(n):
            s = sum(Fraction(chi(l, mu) ** 2, z_alpha(mu)) for mu in partitions(n))
            assert s == 1
            assert chi(l, (1,) * n) == f_lambda(l)
    print('characters OK')

    print('\nTable 4 (n_Brauer), rows d=2..10, columns (p,q) as in paper:')
    cols = [(1, 1), (1, 2), (1, 3), (2, 2), (1, 4), (2, 3), (1, 5), (2, 4), (3, 3), (1, 6), (2, 5), (3, 4), (1, 7), (2, 6),
            (3, 5), (4, 4), (1, 8), (2, 7), (3, 6), (4, 5), (1, 9), (2, 8), (3, 7), (4, 6), (5, 5)]
    for d in range(2, 11):
        print('d=%2d ' % d + ' '.join('%3d' % n_brauer(p, q, d) if d <= p + q else '  .' for p, q in cols))

    print('\nTable 5 (n_{SpxSq}):')
    rows = [(1, 1), (1, 2), (1, 3), (2, 2), (1, 4), (2, 3), (1, 5), (2, 4), (3, 3), (1, 6), (2, 5), (3, 4), (1, 7), (2, 6),
            (3, 5), (4, 4), (1, 8), (2, 7), (3, 6), (4, 5), (1, 9), (2, 8), (3, 7), (4, 6), (5, 5)]
    for p, q in rows:
        print('%d %d ' % (p, q) + ' '.join('%4d' % n_spsq(p, q, d) for d in range(2, p + q + 1)))

    print('\nTable 3 (log10 d^(2(p+q))), rows d=2..10, columns p+q=2..10:')
    import math
    for d in range(2, 11):
        print('d=%2d ' % d + ' '.join('%5.2f' % (2 * n * math.log10(d)) for n in range(2, 11)))

    print('\nTable 6 (n_GT = #paths), check independence of the (p,q) split:')
    for n in range(2, 11):
        line = []
        for d in range(2, n + 1):
            splits = range(0, n + 1) if n <= 8 else (0, 1, n // 2, n)
            vals = {n_gt(p, n - p, d) for p in splits}
            line.append('/'.join(map(str, sorted(vals))))
        print('p+q=%d: ' % n + '  '.join(line))

    print('\nTable 7 (dim A):')
    for n in range(2, 11):
        print('p+q=%2d: ' % n + ' '.join(str(dim_A(n, d)) for d in range(2, n + 1)))
    # cross-check dim A via paths: sum over leaves of (#paths to leaf)^2 for one split
    from collections import Counter as C
    for n in range(2, 8):
        for d in range(2, n + 1):
            for p in range(0, n + 1):
                cnt = C(tuple(P[-1]) for P in all_paths(p, n - p, d))
                assert sum(v * v for v in cnt.values()) == dim_A(n, d), (n, d, p)
    print('dim A = sum_lambda d_lambda^2 consistent with Bratteli paths for all splits, p+q<=7')
