"""Octonions over Q, Coxeter's integral octonions, and the Albert algebra H_3(O).

Exact arithmetic with fractions.Fraction throughout.
"""
from fractions import Fraction as Fr
from itertools import combinations, product, permutations

# Standard octonions: e_i e_j = e_k for (i,j,k) cyclic in each line below; e_i^2 = -1.
LINES = [(1, 2, 4), (2, 3, 5), (3, 4, 6), (4, 5, 7), (5, 6, 1), (6, 7, 2), (7, 1, 3)]

MT = {}  # (i,j) -> (sign, k)
for i in range(8):
    MT[(0, i)] = (1, i)
    MT[(i, 0)] = (1, i)
for i in range(1, 8):
    MT[(i, i)] = (-1, 0)
for (a, b, c) in LINES:
    for (x, y, z) in [(a, b, c), (b, c, a), (c, a, b)]:
        MT[(x, y)] = (1, z)
        MT[(y, x)] = (-1, z)


def omul(x, y):
    r = [Fr(0)] * 8
    for i in range(8):
        if x[i] == 0:
            continue
        for j in range(8):
            if y[j] == 0:
                continue
            s, k = MT[(i, j)]
            r[k] += s * x[i] * y[j]
    return tuple(r)


def oconj(x):
    return (x[0],) + tuple(-c for c in x[1:])


def onorm(x):
    return sum(c * c for c in x)


def oadd(x, y):
    return tuple(a + b for a, b in zip(x, y))


def osub(x, y):
    return tuple(a - b for a, b in zip(x, y))


def oscale(s, x):
    return tuple(s * a for a in x)


ZERO = tuple([Fr(0)] * 8)
ONE = tuple([Fr(1)] + [Fr(0)] * 7)


def e(i):
    v = [Fr(0)] * 8
    v[i] = Fr(1)
    return tuple(v)


# ---------- lattices (Z-spans) via integer HNF on scaled coordinates ----------

def _hnf(rows):
    """Row-style Hermite normal form of an integer matrix (list of lists); returns nonzero rows."""
    A = [list(r) for r in rows]
    m = len(A)
    n = len(A[0]) if A else 0
    piv_row = 0
    for col in range(n):
        # gcd reduction on column col among rows piv_row..m-1
        while True:
            nz = [i for i in range(piv_row, m) if A[i][col] != 0]
            if not nz:
                break
            i0 = min(nz, key=lambda i: abs(A[i][col]))
            A[piv_row], A[i0] = A[i0], A[piv_row]
            done = True
            for i in range(piv_row + 1, m):
                if A[i][col]:
                    q = A[i][col] // A[piv_row][col]
                    A[i] = [a - q * b for a, b in zip(A[i], A[piv_row])]
                    if A[i][col]:
                        done = False
            if done:
                break
        if piv_row < m and A[piv_row][col] != 0:
            if A[piv_row][col] < 0:
                A[piv_row] = [-a for a in A[piv_row]]
            for i in range(piv_row):
                q = A[i][col] // A[piv_row][col]
                A[i] = [a - q * b for a, b in zip(A[i], A[piv_row])]
            piv_row += 1
            if piv_row == m:
                break
    return [r for r in A if any(r)]


class Lattice:
    """Z-span of rational vectors, stored as HNF basis with a common denominator."""

    def __init__(self, gens, denom=4):
        self.d = denom
        rows = []
        for g in gens:
            r = [c * denom for c in g]
            assert all(x.denominator == 1 for x in r), "increase denom"
            rows.append([int(x) for x in r])
        self.H = _hnf(rows)
        self.basis = [tuple(Fr(x, denom) for x in r) for r in self.H]

    def contains(self, v):
        r = [c * self.d for c in v]
        if any(x.denominator != 1 for x in r):
            return False
        r = [int(x) for x in r]
        H = self.H
        # reduce along pivots
        for row in H:
            col = next(i for i, x in enumerate(row) if x)
            if r[col] % row[col]:
                return False
            q = r[col] // row[col]
            r = [a - q * b for a, b in zip(r, row)]
        return not any(r)

    def rank(self):
        return len(self.H)


def fano_planes():
    """All 30 Fano planes on {1..7} (as sets of 7 triples)."""
    pts = range(1, 8)
    triples = list(combinations(pts, 3))
    planes = set()
    for S in combinations(triples, 7):
        ok = True
        for p, q in combinations(pts, 2):
            if sum(1 for t in S if p in t and q in t) != 1:
                ok = False
                break
        if ok:
            planes.add(frozenset(S))
    return [sorted(P) for P in planes]


def coxeter_candidates():
    """Lattices spanned by 1, e_i, (1+e_a+e_b+e_c)/2 for triples of a Fano plane P
    and (e_a+e_b+e_c+e_d)/2 for complements; keep those closed under multiplication
    with 240 units."""
    out = []
    for P in fano_planes():
        gens = [e(i) for i in range(8)]
        for (a, b, c) in P:
            v = [Fr(0)] * 8
            v[0] = Fr(1, 2)
            for t in (a, b, c):
                v[t] = Fr(1, 2)
            gens.append(tuple(v))
            comp = [t for t in range(1, 8) if t not in (a, b, c)]
            w = [Fr(0)] * 8
            for t in comp:
                w[t] = Fr(1, 2)
            gens.append(tuple(w))
        L = Lattice(gens)
        if L.rank() != 8:
            continue
        closed = all(L.contains(omul(x, y)) for x in L.basis for y in L.basis)
        if closed:
            out.append((P, L))
    return out


def units_of(L):
    """All norm-1 elements of the lattice L (coordinates in {0,+-1/2,+-1})."""
    vals = [Fr(-1), Fr(-1, 2), Fr(0), Fr(1, 2), Fr(1)]
    us = []
    # norm 1 vectors: either one +-1, or four +-1/2
    for i in range(8):
        for s in (1, -1):
            v = [Fr(0)] * 8
            v[i] = Fr(s)
            us.append(tuple(v))
    for S in combinations(range(8), 4):
        for signs in product((1, -1), repeat=4):
            v = [Fr(0)] * 8
            for t, s in zip(S, signs):
                v[t] = Fr(s, 2)
            us.append(tuple(v))
    return [u for u in us if L.contains(u)]
