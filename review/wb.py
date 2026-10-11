"""Independent walled Brauer algebra engine (no Sage) used to verify the repo's idempotent DB.

Diagram convention (same labels as Sage's printout):
  label  i > 0  -> top node i       -> point index i-1
  label -i < 0  -> bottom node i    -> point index k+i-1
A diagram is a tuple m of length 2k with m[x] = partner of point x.
Product a*b: a on top of b (bottom row of a glued to top row of b).
"""
import itertools
import re
from fractions import Fraction

P61 = (1 << 61) - 1


class Fp:
    """Element of GF(P61)."""
    __slots__ = ('v',)

    def __init__(self, v):
        if isinstance(v, Fp):
            self.v = v.v
        elif isinstance(v, Fraction):
            self.v = v.numerator % P61 * pow(v.denominator % P61, P61 - 2, P61) % P61
        else:
            self.v = int(v) % P61

    def _c(self, o):
        return o if isinstance(o, Fp) else Fp(o)

    def __add__(self, o): return Fp(self.v + self._c(o).v)
    __radd__ = __add__
    def __sub__(self, o): return Fp(self.v - self._c(o).v)
    def __rsub__(self, o): return Fp(self._c(o).v - self.v)
    def __mul__(self, o):
        if isinstance(o, LC):
            return o * self
        return Fp(self.v * self._c(o).v)
    __rmul__ = __mul__
    def __neg__(self): return Fp(-self.v)
    def __pos__(self): return self
    def inv(self):
        if self.v == 0:
            raise ZeroDivisionError
        return Fp(pow(self.v, P61 - 2, P61))
    def __truediv__(self, o): return self * self._c(o).inv()
    def __rtruediv__(self, o): return self._c(o) * self.inv()
    def __pow__(self, n): return Fp(pow(self.v, n, P61))
    def __eq__(self, o): return self.v == self._c(o).v
    def __hash__(self): return hash(self.v)
    def __repr__(self): return 'Fp(%d)' % self.v
    def is_zero(self): return self.v == 0


def zero_of(x):
    return Fp(0) if isinstance(x, Fp) else Fraction(0)


def iszero(x):
    return x == 0 if not isinstance(x, Fp) else x.v == 0


# ---------------------------------------------------------------- diagrams

def walled_ok(k, p, a, b):
    """Is pairing points a,b allowed in a walled Brauer diagram?"""
    ta, tb = a < k, b < k                     # top row?
    na, nb = (a % k) + 1, (b % k) + 1         # node number 1..k
    la, lb = na <= p, nb <= p                 # left of the wall?
    if ta == tb:                              # same row: must cross the wall
        return la != lb
    return la == lb                           # different rows: same side


def all_diagrams(p, q):
    k = p + q
    pts = list(range(2 * k))
    out = []

    def rec(m, free):
        if not free:
            out.append(tuple(m))
            return
        a = free[0]
        for b in free[1:]:
            if walled_ok(k, p, a, b):
                m[a], m[b] = b, a
                rest = [x for x in free if x != a and x != b]
                rec(m, rest)
        m[a] = None

    rec([None] * (2 * k), pts)
    return out


def from_labels(blocks, k):
    m = [None] * (2 * k)
    idx = lambda l: l - 1 if l > 0 else k + (-l) - 1
    for a, b in blocks:
        ia, ib = idx(a), idx(b)
        m[ia], m[ib] = ib, ia
    assert None not in m
    return tuple(m)


def to_labels(m):
    k = len(m) // 2
    lab = lambda x: x + 1 if x < k else -(x - k + 1)
    seen = set()
    out = []
    for x in range(2 * k):
        if x not in seen:
            seen.update((x, m[x]))
            out.append(tuple(sorted((lab(x), lab(m[x])))))
    return sorted(out)


def identity(k):
    return tuple([k + i for i in range(k)] + [i for i in range(k)])


def compose(a, b):
    """a on top of b. Returns (diagram, number of closed loops)."""
    k = len(a) // 2
    res = [None] * (2 * k)
    mid_seen = [False] * k

    # Walk from an outer point. side: 'A' for a-top, 'B' for b-bottom.
    def walk_from_a_top(t):
        u = a[t]
        while True:
            if u < k:                 # reached a-top
                return ('A', u)
            j = u - k                 # middle point j (a-bottom == b-top)
            mid_seen[j] = True
            v = b[j]
            if v >= k:                # reached b-bottom
                return ('B', v)
            mid_seen[v] = True        # middle point v
            u = a[k + v]

    def walk_from_b_bottom(s):
        v = b[s]
        while True:
            if v >= k:
                return ('B', v)
            mid_seen[v] = True
            u = a[k + v]
            if u < k:
                return ('A', u)
            j = u - k
            mid_seen[j] = True
            v = b[j]

    for t in range(k):
        if res[t] is None:
            side, e = walk_from_a_top(t)
            r = e if side == 'A' else e   # result index: a-top x -> x, b-bottom y -> y
            res[t], res[r] = r, t
    for s in range(k, 2 * k):
        if res[s] is None:
            side, e = walk_from_b_bottom(s)
            res[s], res[e] = e, s
    loops = 0
    for j in range(k):
        if not mid_seen[j]:
            loops += 1
            # traverse the loop: middle j -> b[j] (a b-top point) -> a[k+.] ...
            x = j
            while True:
                mid_seen[x] = True
                y = b[x]          # must be b-top (middle)
                mid_seen[y] = True
                x = a[k + y] - k  # a-bottom (middle)
                if mid_seen[x]:
                    break
    return tuple(res), loops


def num_loops_trace(m):
    """Tr(sigma) = delta^loops: connect top i with bottom i for all i."""
    k = len(m) // 2
    seen = [False] * (2 * k)
    loops = 0
    for x in range(2 * k):
        if not seen[x]:
            loops += 1
            y = x
            while not seen[y]:
                seen[y] = True
                z = m[y]
                seen[z] = True
                y = z + k if z < k else z - k   # close via the trace identification
    return loops


# ---------------------------------------------------------------- linear combinations

class Algebra:
    def __init__(self, p, q, delta):
        self.p, self.q, self.k = p, q, p + q
        self.delta = delta
        self.cache = {}

    def mul_diag(self, a, b):
        key = (a, b)
        r = self.cache.get(key)
        if r is None:
            r = compose(a, b)
            self.cache[key] = r
        return r


class LC:
    """Linear combination of diagrams with coefficients in a field (Fp or Fraction)."""
    __slots__ = ('alg', 'c')

    def __init__(self, alg, c=None):
        self.alg = alg
        self.c = c if c is not None else {}

    def copy(self):
        return LC(self.alg, dict(self.c))

    def __add__(self, o):
        if not isinstance(o, LC):
            o = self.scalar(o)
        r = dict(self.c)
        for d, v in o.c.items():
            w = r.get(d)
            r[d] = v if w is None else w + v
        return LC(self.alg, {d: v for d, v in r.items() if not iszero(v)})
    __radd__ = __add__

    def __neg__(self):
        return LC(self.alg, {d: -v for d, v in self.c.items()})

    def __sub__(self, o):
        return self + (-o)

    def __rsub__(self, o):
        return (-self) + o

    def scalar(self, s):
        return LC(self.alg, {identity(self.alg.k): s} if not iszero(s) else {})

    def __mul__(self, o):
        if isinstance(o, LC):
            alg = self.alg
            dpow = {}
            r = {}
            for a, va in self.c.items():
                for b, vb in o.c.items():
                    m, l = alg.mul_diag(a, b)
                    f = dpow.get(l)
                    if f is None:
                        f = alg.delta ** l
                        dpow[l] = f
                    t = va * vb * f
                    w = r.get(m)
                    r[m] = t if w is None else w + t
            return LC(alg, {d: v for d, v in r.items() if not iszero(v)})
        return LC(self.alg, {d: v * o for d, v in self.c.items() if not iszero(v * o)})

    def __rmul__(self, s):
        return LC(self.alg, {d: s * v for d, v in self.c.items() if not iszero(s * v)})

    def is_zero(self):
        return all(iszero(v) for v in self.c.values())

    def trace(self):
        t = None
        for d, v in self.c.items():
            x = v * self.alg.delta ** num_loops_trace(d)
            t = x if t is None else t + x
        return t if t is not None else 0


# ---------------------------------------------------------------- JM elements and contents (paper eq. 85)

def transposition(k, i, j):
    m = list(identity(k))
    a, b = i - 1, j - 1
    # top a <-> bottom b, top b <-> bottom a
    m[a], m[k + b] = k + b, a
    m[b], m[k + a] = k + a, b
    return tuple(m)


def contraction(k, i, j):
    m = list(identity(k))
    a, b = i - 1, j - 1
    m[a], m[b] = b, a
    m[k + a], m[k + b] = k + b, k + a
    return tuple(m)


def jm(alg, kk, one):
    """J_kk of B_{p,q} as an element of the full algebra (paper eq. (85))."""
    p, k = alg.p, alg.k
    c = {}
    if kk <= p:
        for i in range(1, kk):
            c[transposition(k, i, kk)] = one
    else:
        for i in range(p + 1, kk):
            c[transposition(k, i, kk)] = one
        for i in range(1, p + 1):
            c[contraction(k, i, kk)] = -one
        c[identity(k)] = alg.delta * one
    return LC(alg, c)


def cells(part):
    return {(r, c) for r, row in enumerate(part) for c in range(row)}


def edge_content(lam, mu, level, p, delta):
    """Content of Bratteli edge lam -> mu entering level `level` (1-based), paper Sect. 5.3."""
    Ll, Lr = cells(lam[0]), cells(lam[1])
    Ml, Mr = cells(mu[0]), cells(mu[1])
    if level <= p:
        (r, c), = Ml - Ll
        assert Lr == Mr == set()
        return c - r
    if len(Ml) < len(Ll):
        (r, c), = Ll - Ml
        assert Lr == Mr
        return r - c
    (r, c), = Mr - Lr
    assert Ll == Ml
    return c - r + delta


# ---------------------------------------------------------------- partitions / Bratteli diagram

def partitions(n, maxpart=None):
    if maxpart is None:
        maxpart = n
    if n == 0:
        yield ()
        return
    for f in range(min(n, maxpart), 0, -1):
        for rest in partitions(n - f, f):
            yield (f,) + rest


def add_cells(part):
    part = list(part)
    out = []
    for r in range(len(part) + 1):
        prev = part[r - 1] if r > 0 else 10 ** 9
        cur = part[r] if r < len(part) else 0
        if cur < prev:
            new = part[:]
            if r < len(part):
                new[r] += 1
            else:
                new.append(1)
            out.append(tuple(new))
    return out


def remove_cells(part):
    part = list(part)
    out = []
    for r in range(len(part)):
        nxt = part[r + 1] if r + 1 < len(part) else 0
        if part[r] > nxt:
            new = part[:]
            new[r] -= 1
            if new[r] == 0:
                new.pop()
            out.append(tuple(new))
    return out


def children(v, level, p, d=None):
    """Vertices at `level` reachable from v at level-1."""
    l, r = v
    if level <= p:
        out = [(x, r) for x in add_cells(l)]
    else:
        out = [(l, x) for x in add_cells(r)] + [(x, r) for x in remove_cells(l)]
    if d is not None:
        out = [w for w in out if len(w[0]) + len(w[1]) <= d]
    return out


def all_paths(p, q, d=None):
    paths = [[((), ())]]
    for level in range(1, p + q + 1):
        paths = [P + [w] for P in paths for w in children(P[-1], level, p, d)]
    return paths


# ---------------------------------------------------------------- Weyl dimension of mixed irreps

def weyl_dim(lam, d):
    """Dimension of the U(d) irrep labelled by bipartition (lam_l, lam_r) (as a Fraction or Fp polynomial value).
    Works for symbolic d evaluated at a field element `d` when len(l)+len(r) <= d isn't checkable."""
    l, r = lam
    # highest weight: (l_1..l_a, 0..0, -r_b..-r_1), length d
    # dim = prod_{i<j} (w_i - w_j + j - i)/(j - i). For symbolic d use the closed form via products over
    # the explicit structure; here we only support integer d.
    w = list(l) + [0] * (d - len(l) - len(r)) + [-x for x in reversed(r)]
    num = Fraction(1)
    for i in range(d):
        for j in range(i + 1, d):
            num *= Fraction(w[i] - w[j] + j - i, j - i)
    return num


# ---------------------------------------------------------------- DB parsing

KEY_RE = re.compile(r'\(\((?:\[[\d, ]*\], \[[\d, ]*\])\)(?:, \((?:\[[\d, ]*\], \[[\d, ]*\])\))*\): ')
DIAG_RE = re.compile(r'B\{(\{[-\d, ]+\}(?:, \{[-\d, ]+\})*)\}')


def parse_key(s):
    s = s.strip()[:-1].strip()   # drop ':'
    verts = re.findall(r'\(\[([\d, ]*)\], \[([\d, ]*)\]\)', s)
    tup = lambda t: tuple(int(x) for x in t.split(',') if x.strip())
    return tuple((tup(a), tup(b)) for a, b in verts)


def parse_db(text, alg, zval, one):
    """Return dict path -> LC with z evaluated at zval."""
    text = text.strip()
    assert text[0] == '{' and text[-1] == '}'
    body = text[1:-1]
    keys = list(KEY_RE.finditer(body))
    out = {}
    k = alg.k
    for n, m in enumerate(keys):
        start = m.end()
        end = keys[n + 1].start() if n + 1 < len(keys) else len(body)
        val = body[start:end].strip()
        if val.endswith(','):
            val = val[:-1]
        diags = []

        def repl(mm):
            blocks = [tuple(int(x) for x in b.split(',')) for b in re.findall(r'\{([-\d, ]+)\}', mm.group(1))]
            diags.append(LC(alg, {from_labels(blocks, k): one}))
            return ' D[%d] ' % (len(diags) - 1)

        expr = DIAG_RE.sub(repl, val)
        expr = expr.replace('^', '**')
        expr = re.sub(r'(?<![\w\]\[])(?<!\*\*)(\d+)', r'F(\1)', expr)
        env = {'F': (lambda x: one * int(x)), 'z': zval, 'D': diags}
        out[parse_key(m.group())] = eval(expr, {'__builtins__': {}}, env)
    return out
