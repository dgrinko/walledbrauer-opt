"""Independent recomputation of Sect. 7.1 / Example 7.1 (deciding the principal eigenvalue), d = 2, k = 2.

rho has eigenvalues (x, 1-x) with density mu(x) on [0,1] (paper eq. (147), projected coordinates),
P = sum_lambda c_lambda Pi_lambda with Pi_lambda the isotypic projectors of S_n on (C^2)^{(x)n},
Tr(rho^{(x)n} Pi_lambda) = f^lambda s_lambda(x, 1-x).
Success probability: P[lmax>=c] + sum_lambda c_lambda (int_{lmax<c} mu t_lambda - int_{lmax>=c} mu t_lambda),
maximised over c_lambda in [0,1]  ->  P[lmax>=c] + sum_lambda max(0, A_lambda(c)).
"""
import sympy as sp
from math import factorial

x, c = sp.symbols('x c', real=True)


def two_row_partitions(n):
    return [(n - j, j) if j else (n,) for j in range(0, n // 2 + 1)]


def schur2(lam, a, b):
    l1 = lam[0]
    l2 = lam[1] if len(lam) > 1 else 0
    return sp.expand((a * b) ** l2 * sum(a ** i * b ** (l1 - l2 - i) for i in range(l1 - l2 + 1)))


def flam(lam):
    l1 = lam[0]
    l2 = lam[1] if len(lam) > 1 else 0
    n = l1 + l2
    return factorial(n) * (l1 - l2 + 1) // (factorial(l1 + 1) * factorial(l2))


def density(d=2, k=2):
    # Z[d,k] * prod lambda_i^(k-d) * Vandermonde^2   (d = 2)
    Z = sp.gamma(k * d) / sp.prod([sp.gamma(d + 1 - j) * sp.gamma(k - j) for j in range(d)])
    return sp.simplify(Z * (x * (1 - x)) ** (k - d) * (x - (1 - x)) ** 2)


mu = density()
assert sp.integrate(mu, (x, 0, 1)) == 1


def pieces(n):
    """Return (base, [A_lambda(c)]) on c in [1/2, 1] using the x <-> 1-x symmetry."""
    base = sp.expand(2 * sp.integrate(mu, (x, c, 1)))
    As = []
    for lam in two_row_partitions(n):
        g = sp.expand(mu * flam(lam) * schur2(lam, x, 1 - x))
        A = sp.expand(2 * (sp.integrate(g, (x, sp.Rational(1, 2), c)) - sp.integrate(g, (x, c, 1))))
        As.append((lam, A))
    return base, As


def p_of_c(n, cval):
    base, As = pieces(n)
    return base.subs(c, cval) + sum(max(0, A.subs(c, cval)) for _, A in As)


if __name__ == '__main__':
    # n = 1 : trivial bound (eq. 153)
    base, As = pieces(1)
    print('n=1 base   =', sp.factor(base), '  A =', sp.factor(As[0][1]))
    print('   paper: max{2(1-c)(4c^2-2c+1), (2c-1)^3}; check base - 2(1-c)(4c^2-2c+1) =',
          sp.simplify(base - 2 * (1 - c) * (4 * c ** 2 - 2 * c + 1)))
    for n in range(1, 9):
        base, As = pieces(n)
        # breakpoints: sign changes of A_lambda in (1/2, 1)
        bps = []
        for lam, A in As:
            for r in sp.Poly(A, c).nroots(n=30):
                if abs(sp.im(r)) < 1e-25 and 0.5 < sp.re(r) < 1:
                    bps.append((float(sp.re(r)), lam))
        bps.sort()
        # sample the piecewise function
        grid = [0.5 + i / 2000 for i in range(1001)]
        vals = [float(p_of_c(n, sp.Rational(g).limit_denominator(10 ** 6))) for g in grid[::20]]
        print('n=%d breakpoints:' % n, ['%.9f %s' % b for b in bps], ' min over grid ~ %.6f' % min(vals))
    # Example 7.1: n = 3, compare piece by piece
    base, As = pieces(3)
    print('\nn=3 A_lambda:')
    for lam, A in As:
        print('  ', lam, sp.factor(A))
    c1 = sp.nsolve(96 * c ** 5 - 240 * c ** 4 + 200 * c ** 3 - 60 * c ** 2 + 3, c, 0.82)
    c2 = sp.nsolve(24 * c ** 5 - 60 * c ** 4 + 70 * c ** 3 - 45 * c ** 2 + 15 * c - 3, c, 0.91)
    print('c1 =', c1, ' c2 =', c2)
    paper = [(2 * (1 - c) * (4 * c ** 2 - 2 * c + 1), 0.5, float(c1)),
             (sp.Rational(7, 5) - sp.Rational(6, 5) * c * (16 * c ** 4 - 40 * c ** 3 + 40 * c ** 2 - 20 * c + 5), float(c1), float(c2)),
             ((2 * c - 1) ** 3, float(c2), 1.0)]
    worst = 0
    for expr, lo, hi in paper:
        for t in [lo + (hi - lo) * i / 50 for i in range(1, 50)]:
            tv = sp.Rational(t).limit_denominator(10 ** 9)
            worst = max(worst, abs(float(expr.subs(c, tv) - p_of_c(3, tv))))
    print('max |paper formula (152) - recomputed p^3(c)| on [1/2,1]:', worst)
    print('p^3(c2) =', sp.N(p_of_c(3, c2), 12), '  (paper: ~0.566968020)')
    # n = 2 piece reported by the notebook (Out[257])
    nb2 = sp.Rational(17, 10) - 6 * c + 18 * c ** 2 - 28 * c ** 3 + 24 * c ** 4 - sp.Rational(48, 5) * c ** 5
    t = sp.Rational(86, 100)
    print('n=2 notebook middle piece at c=0.86:', float(nb2.subs(c, t)), ' recomputed:', float(p_of_c(2, t)))
