"""Independent check of the exact optimal comb for f(U) = U^T with n = 4 calls and d = 2
(Sect. 7.4, Table 2: fidelity 1.000000), stored in ../guess_magic_4_1_2.nb.

The notebook gives the Choi matrix of the comb in the form of eq. (177),

    C = sum_{lambda,mu} sum_{i,j,k,l} B[lambda,mu][(i,k),(j,l)]  E^lambda_ij (x) E^mu_kl ,

where E^lambda_ij = psi^2_{4,1}(eps^lambda_ij) are the matrix units of A^2_{4,1} stored in
../idempotents/elementary_4_1_2.m, the first factor acts on O_1..O_4, P and the second on I_1..I_4, F.
Its first Input cell defines the blocks B[lambda,mu] exactly (v[lambda,mu], lambdas[lambda,mu]); this script reads
that cell (linearised with nb2txt.py), evaluates it in exact arithmetic over Q(sqrt 2, sqrt 3, sqrt 5) and checks

  1. the blocks: symmetric, and PSD exactly (B = v^T.diag(lambdas).v with orthonormal rows v and lambdas >= 0,
     or diagonal with entries >= 0);
  2. the variables x[lambda,mu,i,j,k,l] of app4.nb (same naming rule): no conflicting duplicates, and the same rules
     as the saved output of Normal@guessAnsatz in the notebook (if present);
  3. the 672 exact linear constraints of ../app4_data/eq_4_1_2_exact.m (Tr C = d^5 and the comb conditions in the
     notebook's variables) vanish exactly;
  4. at operator level, with C built as a 1024 x 1024 matrix from the matrix units (no constraint files used):
     the E^lambda_ij are matrix units, C = C^T >= 0, Tr C = d^{n+1} = 32, the sequential-comb conditions
     Tr_F C = C_4 (x) 1_{O_4}, Tr_{I_4} C_4 = C_3 (x) 1_{O_3}, ..., Tr_{I_1} C_1 = C_0 1_P with
     C_{i-1} = (1/d) Tr_{I_i O_{i-1}} C_i and C_0 = 1;
  5. the fidelity (1/d^2) <<I|C|I>> at U = 1 (by covariance this is the Haar-average fidelity, the Table 2 value),
     and for Haar-random U the link product of C with the Choi matrices of U on (I_k, O_k): the resulting channel
     P -> F must have Choi matrix |U^T>><<U^T| (fidelity 1 to U^T); the fidelity to U^{-1} is printed for contrast.

The psi map: diagram labels k > 0 (top row) index the rows (ket) and -k (bottom row) the columns (bra) of site k,
so that psi(sigma tau) = psi(sigma) psi(tau) for the product of compute_matrix_units_and_blocks.nb (sigma on top).
The diagram basis WalledBrauerBasis[4,1] is read from ../idempotents/metadata_4_1_2.m.

Usage:   python3 app4_certificate_check.py [--samples K] [--seed S]
Needs:   numpy; nb2txt.py from this folder. Runtime: a few seconds.
Exit code 0 if every check passes, 1 otherwise.
"""
import argparse
import os
import re
import sys
from fractions import Fraction
from math import gcd, sqrt

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.normpath(os.path.join(HERE, '..'))
sys.path.insert(0, HERE)
import nb2txt  # noqa: E402

NOTEBOOK = os.path.join(ROOT, 'guess_magic_4_1_2.nb')
METADATA = os.path.join(ROOT, 'idempotents', 'metadata_4_1_2.m')
ELEMENTARY = os.path.join(ROOT, 'idempotents', 'elementary_4_1_2.m')
CONSTRAINTS = os.path.join(ROOT, 'app4_data', 'eq_4_1_2_exact.m')

P_, Q_, D = 4, 1, 2           # (p, q, d): U^T task with n = p = 4 calls on qubits
N_SITES = P_ + Q_             # sites per register: O_1..O_4, P  and  I_1..I_4, F
TOL = 1e-10


# ----------------------------------------------------------------------------------------------------------------
# exact arithmetic in Q(sqrt(n) : n squarefree)

def _squarefree(n):
    """Write n = f^2 s with s squarefree; return (s, f)."""
    f, k = 1, 2
    while k * k <= n:
        while n % (k * k) == 0:
            n //= k * k
            f *= k
        k += 1
    return n, f


def _primes(n):
    out, k = [], 2
    while k * k <= n:
        if n % k == 0:
            out.append(k)
            n //= k
        else:
            k += 1
    return out + ([n] if n > 1 else [])


class Surd:
    """Exact element sum_s c_s sqrt(s) (s squarefree, c_s rational) of a multiquadratic field."""
    __slots__ = ('c',)

    def __init__(self, c=0):
        if isinstance(c, dict):
            self.c = {k: v for k, v in c.items() if v != 0}
        else:
            c = Fraction(c)
            self.c = {1: c} if c != 0 else {}

    @staticmethod
    def sqrt(x):
        r = x.rational()
        if r < 0:
            raise ValueError('Sqrt of a negative number')
        s, f = _squarefree(r.numerator * r.denominator)
        return Surd({s: Fraction(f, r.denominator)})

    def rational(self):
        if set(self.c) - {1}:
            raise ValueError('not a rational number: %s' % self)
        return self.c.get(1, Fraction(0))

    def is_zero(self):
        return not self.c

    def __add__(self, o):
        out = dict(self.c)
        for k, v in o.c.items():
            out[k] = out.get(k, 0) + v
        return Surd(out)

    def __neg__(self):
        return Surd({k: -v for k, v in self.c.items()})

    def __sub__(self, o):
        return self + (-o)

    def __mul__(self, o):
        out = {}
        for a, x in self.c.items():
            for b, y in o.c.items():
                g = gcd(a, b)
                k = (a // g) * (b // g)
                out[k] = out.get(k, 0) + x * y * g
        return Surd(out)

    def inverse(self):
        num, den = Surd(1), self
        while True:
            primes = sorted({p for k in den.c for p in _primes(k)})
            if not primes:
                break
            conj = Surd({k: (-v if k % primes[0] == 0 else v) for k, v in den.c.items()})
            num, den = num * conj, den * conj
        return num * Surd(1 / den.rational())

    def __truediv__(self, o):
        return self * o.inverse()

    def __float__(self):
        return float(sum(float(v) * sqrt(k) for k, v in self.c.items()))

    def __repr__(self):
        return ' + '.join('%s*sqrt(%d)' % (v, k) if k != 1 else str(v) for k, v in sorted(self.c.items())) or '0'


ZERO, ONE = Surd(0), Surd(1)


# ----------------------------------------------------------------------------------------------------------------
# evaluator for the subset of the Wolfram Language used in the notebook cell and in the .m data files

class Sym(str):
    """An undefined symbol (only allowed on the left of a rule)."""


_TOKEN = re.compile(r'\s*(?:(?P<num>\d+)|(?P<name>[^\W\d_\u1d40][^\W_\u1d40]*)'
                    r'|(?P<op>->|//|==|[-+*/^.=;,\[\]{}()\u1d40]))')


def _tokenize(src):
    src = re.sub(r'\(\*.*?\*\)', ' ', src, flags=re.S)        # comments
    src = src.replace('\\[NoBreak]', ' ').replace('\\n', '\n')   # nb2txt leftovers
    toks, pos = [], 0
    while True:
        m = _TOKEN.match(src, pos)
        if not m or m.end() == pos:
            if src[pos:].strip():
                raise SyntaxError('cannot tokenize at %r' % src[pos:pos + 40])
            return toks
        pos = m.end()
        toks.append((m.lastgroup, m.group(m.lastgroup)))


def _mat(x):
    if not (isinstance(x, list) and x and all(isinstance(r, list) for r in x)):
        raise TypeError('matrix expected')
    return x


def _dot(a, b):
    if isinstance(a, list) and isinstance(b, list):
        if a and isinstance(a[0], list):                     # matrix . (matrix or vector)
            return [_dot(row, b) for row in a]
        if b and isinstance(b[0], list):                     # vector . matrix
            return [_dot(a, col) for col in map(list, zip(*b))]
        if len(a) != len(b):
            raise ValueError('Dot: incompatible lengths')
        acc = ZERO
        for x, y in zip(a, b):
            acc = acc + x * y
        return acc
    raise TypeError('Dot of non-lists')


def _scalar(x):
    if isinstance(x, Sym):
        raise NameError('undefined symbol %s' % x)
    if not isinstance(x, Surd):
        raise TypeError('arithmetic on a non-scalar: %r' % (x,))
    return x


def _int(x):
    r = _scalar(x).rational()
    if r.denominator != 1:
        raise ValueError('integer expected')
    return int(r)


def _nonneg(x):
    """x >= 0, exactly for rationals (the only case met here), else numerically."""
    try:
        return x.rational() >= 0
    except ValueError:
        return float(x) > -TOL


def _constant_array(c, dims):
    dims = [_int(n) for n in dims]
    if len(dims) == 1:
        return [c] * dims[0]
    return [_constant_array(c, [Surd(n) for n in dims[1:]]) for _ in range(dims[0])]


class Evaluator:
    """Recursive-descent evaluator: numbers, symbols, f[args], {lists}, + - * / ^ (integer powers), juxtaposition,
    Dot (.), postfix transpose, Rule (->), expr // FullSimplify, and assignments s = e, s[i,...] = e."""

    def __init__(self, env=None, functions=None):
        self.env = {} if env is None else env
        self.functions = {
            'Sqrt': lambda x: Surd.sqrt(_scalar(x)),
            'DiagonalMatrix': lambda v: [[v[i] if i == j else ZERO for j in range(len(v))] for i in range(len(v))],
            'ConstantArray': _constant_array,
            'Transpose': lambda m: [list(r) for r in zip(*_mat(m))],
        }
        self.functions.update(functions or {})
        self.used = set()

    def run(self, src):
        """Evaluate a program (statements separated by ';'); return the value of the last statement."""
        self.t, self.i = _tokenize(src), 0
        val = None
        while self.i < len(self.t):
            val = self.statement()
            if self.i < len(self.t):
                self.expect(';')
        return val

    # -- token helpers
    def peek(self, k=0):
        j = self.i + k
        return self.t[j] if j < len(self.t) else (None, None)

    def take(self):
        tok = self.t[self.i]
        self.i += 1
        return tok

    def expect(self, v):
        tok = self.take()
        if tok[1] != v:
            raise SyntaxError('expected %r, got %r' % (v, tok[1]))

    # -- grammar
    def statement(self):
        kind, name = self.peek()
        if kind == 'name' and self.peek(1)[1] == '=':
            self.i += 2
            self.env[name] = self.expr()
            return self.env[name]
        if kind == 'name' and self.peek(1)[1] == '[':
            depth, j = 0, self.i + 1                           # find the matching ']' and look for '='
            while j < len(self.t):
                depth += {'[': 1, ']': -1}.get(self.t[j][1], 0)
                if depth == 0:
                    break
                j += 1
            if j + 1 < len(self.t) and self.t[j + 1][1] == '=':
                self.i += 2
                key = (name, tuple(_int(a) for a in self.args(']')))
                self.expect('=')
                self.env[key] = self.expr()
                return self.env[key]
        return self.expr()

    def expr(self):
        val = self.rule()
        while self.peek()[1] == '//':
            self.take()
            fn = self.take()[1]
            if fn not in ('FullSimplify', 'Simplify'):         # identities on exact values
                raise SyntaxError('unsupported postfix function %s' % fn)
        return val

    def rule(self):
        lhs = self.sum()
        if self.peek()[1] == '->':
            self.take()
            return ('Rule', lhs, self.rule())
        return lhs

    def sum(self):
        val = self.term()
        while self.peek()[1] in ('+', '-'):
            op = self.take()[1]
            rhs = self.term()
            val = _scalar(val) + _scalar(rhs) if op == '+' else _scalar(val) - _scalar(rhs)
        return val

    def term(self):
        val = self.unary()
        while True:
            kind, v = self.peek()
            if v == '*' or v == '/':
                self.take()
                rhs = self.unary()
                val = _scalar(val) * _scalar(rhs) if v == '*' else _scalar(val) / _scalar(rhs)
            elif kind in ('num', 'name') or v in ('(', '{'):     # implicit multiplication
                val = _scalar(val) * _scalar(self.unary())
            else:
                return val

    def unary(self):
        if self.peek()[1] == '-':
            self.take()
            return -_scalar(self.unary())
        if self.peek()[1] == '+':
            self.take()
            return self.unary()
        return self.dot()

    def dot(self):
        val = self.power()
        while self.peek()[1] == '.':
            self.take()
            val = _dot(val, self.power())
        return val

    def power(self):
        base = self.postfix()
        if self.peek()[1] == '^':
            self.take()
            e = _int(self.unary())
            out = ONE
            for _ in range(abs(e)):
                out = out * _scalar(base)
            return out if e >= 0 else out.inverse()
        return base

    def postfix(self):
        val = self.primary()
        while self.peek()[1] == '\u1d40':                    # transpose glyph written by nb2txt
            self.take()
            val = self.functions['Transpose'](val)
        return val

    def args(self, close):
        out = []
        if self.peek()[1] == close:
            self.take()
            return out
        while True:
            out.append(self.expr())
            v = self.take()[1]
            if v == close:
                return out
            if v != ',':
                raise SyntaxError('expected , or %s, got %r' % (close, v))

    def primary(self):
        kind, v = self.take()
        if kind == 'num':
            return Surd(int(v))
        if v == '(':
            val = self.expr()
            self.expect(')')
            return val
        if v == '{':
            return self.args('}')
        if kind == 'name':
            if self.peek()[1] == '[':
                self.take()
                a = self.args(']')
                if v in self.functions:
                    return self.functions[v](*a)
                key = (v, tuple(_int(x) for x in a))
                if key not in self.env:
                    raise NameError('undefined %s%s' % key)
                return self.env[key]
            if v in self.env:
                self.used.add(v)
                return self.env[v]
            return Sym(v)
        raise SyntaxError('unexpected token %r' % v)


def load_m(path, **kw):
    """Evaluate a Mathematica .m data file (an expression in InputForm)."""
    return Evaluator(**kw).run(open(path, encoding='ascii').read())


# ----------------------------------------------------------------------------------------------------------------
# notebook

def notebook_cells(path):
    """(style, label, linear text) of every cell, via nb2txt.py."""
    text = open(path, encoding='utf-8').read()
    body = text[text.index('Notebook['):text.rfind('(* End of Notebook Content *)')]
    body = re.sub(r'(?<!\\)\\\r?\n', '', body)
    tree = nb2txt.P(nb2txt.tokenize(nb2txt.strip_heads(body))).expr()
    cells = []
    nb2txt.walk_cells(tree, cells)
    return cells


def x_name(lam, mu, i, j, k, l, dims):
    """Name of the variable x[lam,mu,i,j,k,l,dims] of app4.nb:
    "x" <> Str[lam] <> Str[mu] <> StringJoin @@ Sort[{Str[i] <> Str[k], Str[j] <> Str[l]}]."""
    s = lambda a, mx: str(a).zfill(len(str(mx)))
    return ('x' + s(lam, len(dims)) + s(mu, len(dims))
            + ''.join(sorted([s(i, dims[lam - 1]) + s(k, dims[mu - 1]), s(j, dims[lam - 1]) + s(l, dims[mu - 1])])))


# ----------------------------------------------------------------------------------------------------------------
# operators

def psi(diagram, n=N_SITES, d=D):
    """Matrix of a walled Brauer diagram (pairs of labels, k = top/ket of site k, -k = bottom/bra of site k)."""
    M = np.zeros((d ** n, d ** n))
    for vals in np.ndindex(*([d] * len(diagram))):
        row, col = [0] * n, [0] * n
        for (a, b), v in zip(diagram, vals):
            for e in (a, b):
                (row if e > 0 else col)[abs(e) - 1] = v
        M[int(''.join(map(str, row)), d), int(''.join(map(str, col)), d)] = 1
    return M


def permute(M, names, order, d=D):
    """Reorder the tensor factors of the operator M on the sites `names` into `order`."""
    m = len(names)
    perm = [names.index(x) for x in order]
    return M.reshape([d] * (2 * m)).transpose(perm + [m + p for p in perm]).reshape(d ** m, d ** m)


def ptrace(M, names, site, d=D):
    m, s = len(names), names.index(site)
    T = np.trace(M.reshape([d] * (2 * m)), axis1=s, axis2=m + s)
    return T.reshape(d ** (m - 1), d ** (m - 1)), [x for x in names if x != site]


def haar(rng, d=D):
    Z = (rng.normal(size=(d, d)) + 1j * rng.normal(size=(d, d))) / np.sqrt(2)
    Qm, R = np.linalg.qr(Z)
    return Qm * (np.diag(R) / abs(np.diag(R)))


def choi_vec(V, d=D):
    """|V>> = sum_a |a>_in (x) V|a>_out."""
    return np.array([V[b, a] for a in range(d) for b in range(d)])


def link_with_unitary(C, names, U, n=P_, d=D):
    """Channel P -> F obtained by plugging U into every slot I_k -> O_k: link product of C with |U>><<U|."""
    K = np.einsum('ba,dc->abcd', U, U.conj())        # K[a,b,a',b'] = <a b|U>><<U|a' b'> = U[b,a] conj(U[b',a'])
    T, cur = C.reshape([d] * (2 * len(names))), list(names)
    for k in range(1, n + 1):
        m = len(cur)
        a, b = cur.index('I%d' % k), cur.index('O%d' % k)
        out = [x for x in range(2 * m) if x not in (a, b, m + a, m + b)]
        T = np.einsum(T, list(range(2 * m)), K, [a, b, m + a, m + b], out)
        cur = [x for x in cur if x not in ('I%d' % k, 'O%d' % k)]
    J = T.reshape(d ** len(cur), d ** len(cur))
    return permute(J, cur, ['P', 'F'])


# ----------------------------------------------------------------------------------------------------------------

def main():
    ap = argparse.ArgumentParser(description=__doc__.split('\n')[0])
    ap.add_argument('--samples', type=int, default=5, help='number of Haar-random unitaries (default 5)')
    ap.add_argument('--seed', type=int, default=2024)
    args = ap.parse_args()
    failures = []

    def report(ok, msg):
        print(('  PASS  ' if ok else '  FAIL  ') + msg)
        if not ok:
            failures.append(msg)

    # -- data
    dims_meta, _paths, basis = load_m(METADATA, functions={
        'B': lambda *pairs: tuple(tuple(_int(x) for x in p) for p in pairs)})
    dims = [_int(x) for x in dims_meta]
    eps = load_m(ELEMENTARY)
    print('A^%d_{%d,%d}: irrep dimensions %s, %d basis diagrams' % (D, P_, Q_, dims, len(basis)))

    # -- 1. blocks from the notebook's definition cell
    cells = notebook_cells(NOTEBOOK)
    src = [t for s, _, t in cells if s == 'Input' and re.search(r'v\[2,3\]\s*=', t)]
    assert len(src) == 1, 'definition cell of v[2,3] not found (or not unique)'
    nb = Evaluator()
    nb.run(src[0])
    Bblk = {(l, m): nb.env[('B', (l, m))] for l in range(1, len(dims) + 1) for m in range(1, len(dims) + 1)}
    print('\n1. blocks B[lambda,mu] from %s (first Input cell)' % os.path.basename(NOTEBOOK))
    for (l, m), M in sorted(Bblk.items()):
        n = dims[l - 1] * dims[m - 1]
        shape_ok = len(M) == n and all(len(r) == n for r in M)
        sym = shape_ok and all((M[r][c] - M[c][r]).is_zero() for r in range(n) for c in range(n))
        if ('v', (l, m)) in nb.env:
            v, lam = nb.env[('v', (l, m))], nb.env[('\u03bbs', (l, m))]
            vvT = _dot(v, [list(r) for r in zip(*v)])
            ortho = all((vvT[r][c] - (ONE if r == c else ZERO)).is_zero() for r in range(len(v)) for c in range(len(v)))
            again = _dot(_dot([list(r) for r in zip(*v)], [[lam[r] if r == c else ZERO for c in range(len(v))]
                                                          for r in range(len(v))]), v)
            same = all((again[r][c] - M[r][c]).is_zero() for r in range(n) for c in range(n))
            nonneg = all(_nonneg(x) for x in lam)
            exact_psd = ortho and same and nonneg
            how = 'v^T.diag(%s).v, orthonormal rows' % ','.join(str(x) for x in lam)
        else:
            nonneg = all((M[r][c].is_zero() if r != c else _nonneg(M[r][r])) for r in range(n) for c in range(n))
            exact_psd, how = nonneg, 'diagonal %s' % ','.join(str(M[r][r]) for r in range(n))
        ev = np.linalg.eigvalsh(np.array([[float(x) for x in r] for r in M]))
        report(shape_ok and sym and exact_psd and ev.min() > -TOL,
               'B[%d,%d] (%dx%d) symmetric, PSD (%s), rank %d, min eig %.1e'
               % (l, m, n, n, how, (ev > 1e-9).sum(), ev.min()))

    # -- 2. variables of app4.nb
    print('\n2. variables x[lambda,mu,i,j,k,l] (naming of app4.nb)')
    guess, conflicts = {}, 0
    for (l, m), M in Bblk.items():
        dl, dm = dims[l - 1], dims[m - 1]
        for i, k, j, ll in np.ndindex(dl, dm, dl, dm):
            name = x_name(l, m, i + 1, j + 1, k + 1, ll + 1, dims)
            val = M[i * dm + k][j * dm + ll]
            if name in guess and not (guess[name] - val).is_zero():
                conflicts += 1
            guess.setdefault(name, val)
    report(conflicts == 0, '%d distinct variables, %d conflicting duplicates' % (len(guess), conflicts))
    saved = [cells[c + 1][2] for c in range(len(cells) - 1)
             if cells[c][0] == 'Input' and cells[c][2].strip() == 'Normal@guessAnsatz' and cells[c + 1][0] == 'Output']
    if saved:
        rules = Evaluator().run(saved[0])
        names_ok = {r[1] for r in rules} == set(guess)
        vals_ok = all((r[2] - guess[r[1]]).is_zero() for r in rules if r[1] in guess)
        report(names_ok and vals_ok, 'saved output of Normal@guessAnsatz (%d rules) has the same variables and values'
               % len(rules))
    else:
        print('  (no saved output of Normal@guessAnsatz in the notebook; comparison skipped)')

    # -- 3. exact linear constraints
    print('\n3. exact constraints %s' % os.path.relpath(CONSTRAINTS, ROOT))
    ev3 = Evaluator(env=guess)
    eqs = ev3.run(open(CONSTRAINTS, encoding='ascii').read())
    nonzero = [r for r, e in enumerate(eqs) if not _scalar(e).is_zero()]
    report(not nonzero, '%d constraints in %d variables, all exactly 0 at the solution%s'
           % (len(eqs), len(ev3.used), '' if not nonzero else ' -- NONZERO: %s' % nonzero[:10]))
    zero = Evaluator(env={k: ZERO for k in guess}).run(open(CONSTRAINTS, encoding='ascii').read())
    report(not _scalar(zero[0]).is_zero(), 'not vacuous: at C = 0 the first (trace) constraint is %s' % zero[0])

    # -- 4. operator level
    print('\n4. Choi matrix C (1024 x 1024) on O1..O4,P | I1..I4,F')
    Pmat = np.array([psi(s) for s in basis])
    units, E = [], []
    for l, block in enumerate(eps, 1):
        for i, row in enumerate(block, 1):
            for j, vec in enumerate(row, 1):
                units.append((l, i, j))
                E.append(np.tensordot(np.array([float(x) for x in vec]), Pmat, 1))
    E = np.array(E)
    idx = {u: a for a, u in enumerate(units)}
    err = max(abs(E[idx[(l, i, j)]] @ E[idx[(l2, k, ll)]]
                  - (E[idx[(l, i, ll)]] if (l == l2 and j == k) else 0)).max()
              for (l, i, j) in units for (l2, k, ll) in units)
    mdims = [round(np.trace(E[idx[(l, 1, 1)]])) for l in range(1, len(dims) + 1)]
    sym_err = max(abs(E[idx[(l, i, j)]].T - E[idx[(l, j, i)]]).max() for (l, i, j) in units)
    report(err < TOL and sym_err < TOL, 'E^lambda_ij E^mu_kl = delta E^lambda_il (max err %.1e), (E_ij)^T = E_ji, '
           'Tr E^lambda_11 = %s (U(2) irrep dims)' % (err, mdims))
    X = np.zeros((len(units), len(units)))
    for a, (l, i, j) in enumerate(units):
        for b, (m, k, ll) in enumerate(units):
            X[a, b] = float(Bblk[(l, m)][(i - 1) * dims[m - 1] + k - 1][(j - 1) * dims[m - 1] + ll - 1])
    T = np.tensordot(X, E, axes=(1, 0))                                     # T[a] = sum_b X[a,b] E[b]
    s = D ** N_SITES
    C = np.tensordot(E, T, axes=(0, 0)).transpose(0, 2, 1, 3).reshape(s * s, s * s)
    names = ['O1', 'O2', 'O3', 'O4', 'P', 'I1', 'I2', 'I3', 'I4', 'F']
    ev = np.linalg.eigvalsh(C)
    report(abs(C - C.T).max() < TOL and ev.min() > -TOL,
           'C = C^T (err %.1e), C >= 0 (min eig %.1e), rank %d'
           % (abs(C - C.T).max(), ev.min(), (ev > 1e-9).sum()))
    report(abs(np.trace(C) - D ** (P_ + 1)) < TOL, 'Tr C = %.12f (d^{n+1} = %d)' % (np.trace(C), D ** (P_ + 1)))
    cur, cn = C, names                                                      # C_5 = C, I_5 = F, O_0 = P
    steps = [('F', 'O4'), ('I4', 'O3'), ('I3', 'O2'), ('I2', 'O1'), ('I1', 'P')]
    for i, (In, Oprev) in zip(range(P_ + 1, 0, -1), steps):
        A, an = ptrace(cur, cn, In)                                         # Tr_{I_i} C_i
        Cprev, pn = ptrace(A, an, Oprev)
        Cprev = Cprev / D                                                   # C_{i-1}
        e = abs(permute(A, an, pn + [Oprev]) - np.kron(Cprev, np.eye(D))).max()
        report(e < TOL, 'Tr_%s C_%d = C_%d (x) 1_%s   (max err %.1e)' % (In, i, i - 1, Oprev, e))
        cur, cn = Cprev, pn
    report(cur.shape == (1, 1) and abs(cur[0, 0] - 1) < TOL, 'C_0 = %.12f (normalisation Tr_I1 C_1 = 1_P)'
           % cur[0, 0])

    # -- 5. fidelity
    print('\n5. fidelity')
    vI = np.zeros(D ** (2 * N_SITES))
    for bits in np.ndindex(*([D] * N_SITES)):            # one value per pair (I_k,O_k), (P,F)
        val = dict(zip(['1', '2', '3', '4', 'PF'], bits))
        digits = [val[x[1]] if x[0] in 'OI' else val['PF'] for x in names]
        vI[int(''.join(map(str, digits)), D)] = 1
    fI = vI @ C @ vI / D ** 2
    report(abs(fI - 1) < TOL, 'U = 1: (1/d^2) <<1|C|1>> = %.12f (= Haar-average fidelity by covariance)' % fI)
    rng = np.random.default_rng(args.seed)
    for t in range(args.samples):
        U = haar(rng)
        J = link_with_unitary(C, names, U)
        w, wi = choi_vec(U.T), choi_vec(U.conj().T)
        f, finv = (w.conj() @ J @ w).real / D ** 2, (wi.conj() @ J @ wi).real / D ** 2
        e = abs(J - np.outer(w, w.conj())).max()
        report(abs(f - 1) < TOL and e < TOL, 'Haar U #%d: output channel = U^T (Choi err %.1e), F(U^T) = %.12f, '
               'F(U^-1) = %.4f' % (t + 1, e, f, finv))

    print('\n%s' % ('ALL CHECKS PASSED' if not failures else '%d CHECK(S) FAILED' % len(failures)))
    return 0 if not failures else 1


if __name__ == '__main__':
    sys.exit(main())
