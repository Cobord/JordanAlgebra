"""Spin-factor checks for the standard form B(x,y) = sum x_i y_i on Z[1/2]^n.

1. Unit vectors of Z[1/2]^n for n <= 4 (searching denominators up to 2^3).
2. |O_n(Z[1/2])| for n = 1..4, as orthogonal matrices whose columns are unit vectors.
3. The stabilizer of v = (1/2,1/2,1/2,1/2) in O_4(Z[1/2]).
4. For n = 5, the product of the reflections in w = (1,1,1,1,0) and w' = (1,1,1,0,1) is a dyadic
   orthogonal matrix of infinite order (rotation with cos = 1/8 on span(w, w')).
Exact arithmetic with fractions.Fraction.
"""
from fractions import Fraction as Fr
from itertools import product, permutations


def unit_vectors(n, kmax=3):
    out = set()
    for k in range(kmax + 1):
        d = 2 ** k
        rng = range(-d, d + 1)
        for m in product(rng, repeat=n):
            if sum(x * x for x in m) == d * d:
                out.add(tuple(Fr(x, d) for x in m))
    return sorted(out)


def dot(x, y):
    return sum(a * b for a, b in zip(x, y))


def orthogonal_group(n):
    U = unit_vectors(n)
    mats = []

    def rec(cols):
        if len(cols) == n:
            mats.append(tuple(cols))
            return
        for u in U:
            if all(dot(u, c) == 0 for c in cols):
                rec(cols + [u])
    rec([])
    return U, mats


for n in range(1, 5):
    U, G = orthogonal_group(n)
    print(f"n = {n}: {len(U)} unit vectors in Z[1/2]^{n}; |O_{n}(Z[1/2])| = {len(G)}")
    if n == 4:
        v = (Fr(1, 2),) * 4
        # matrix with columns c acts by x -> sum x_j c_j
        def act(M, x):
            return tuple(sum(x[j] * M[j][i] for j in range(4)) for i in range(4))
        stab = [M for M in G if act(M, v) == v]
        print(f"   stabilizer of (1/2,1/2,1/2,1/2): order {len(stab)}")
        print("   all unit vectors are +-e_i or (+-1/2)^4:",
              all(sorted(map(abs, u)) in ([0, 0, 0, 1], [Fr(1, 2)] * 4) for u in U))

# n = 5: explicit element of infinite order
w = (1, 1, 1, 1, 0)
w2 = (1, 1, 1, 0, 1)


def refl(w):
    nw = dot(w, w)
    return [[Fr(int(i == j)) - Fr(2 * w[i] * w[j], nw) for j in range(5)] for i in range(5)]


def mul(A, B):
    return [[sum(A[i][k] * B[k][j] for k in range(5)) for j in range(5)] for i in range(5)]


g = mul(refl(w), refl(w2))
print("n = 5: g = s_w s_w' has dyadic entries:", all(x.denominator in (1, 2, 4) for row in g for x in row),
      "; orthogonal:", mul(g, [list(r) for r in zip(*g)]) == [[Fr(int(i == j)) for j in range(5)] for i in range(5)])
cos = Fr(dot(w, w2), dot(w, w))
print("   cos(angle(w, w')) =", cos, "; rotation angle 2*theta has cos =", 2 * cos * cos - 1)
tr = sum(g[i][i] for i in range(5))
print("   trace(g) =", tr, "(= 3 + 2 cos 2theta); 2 cos 2theta =", tr - 3,
      "is not an integer, so g has infinite order (Niven / algebraic integers)")

# Stabilizer of the line D*v, v = (1/2,1/2,1/2,1/2), in O_4(Z[1/2]): the group of the
# spin-factor diagram J(D v) -> J(D^4).
U4, G4 = orthogonal_group(4)
v = (Fr(1, 2),) * 4
def act4(M, x):
    return tuple(sum(x[j] * M[j][i] for j in range(4)) for i in range(4))
mv = tuple(-c for c in v)
print("line stabilizer of D(1/2,1/2,1/2,1/2) in O_4(Z[1/2]): order",
      sum(1 for M in G4 if act4(M, v) in (v, mv)))
roots_perp = [u for u in U4 if dot(u, v) == 0]
long_perp = [u for u in product([-1, 0, 1], repeat=4)
             if sum(x * x for x in u) == 2 and sum(u) == 0]
print("F4 roots orthogonal to v:", len(roots_perp), "short +", len(long_perp), "long =",
      len(roots_perp) + len(long_perp), "(B3 has 18 roots)")

# H_2(O) is the spin factor of alpha^2 + N(x): check v o w = B(v,w) I on random rational inputs.
import random
from octo import omul, oconj, oadd, oscale, ZERO
random.seed(1)
def rnd():
    return Fr(random.randint(-9, 9), random.choice([1, 2, 4]))
def mmul(X, Y):  # 2x2 octonion matrices, entries as octonion tuples
    return [[oadd(omul(X[i][0], Y[0][j]), omul(X[i][1], Y[1][j])) for j in range(2)] for i in range(2)]
def sc(a):
    return (a,) + (Fr(0),) * 7
ok = True
for _ in range(50):
    a, b = rnd(), rnd()
    x = tuple(rnd() for _ in range(8)); y = tuple(rnd() for _ in range(8))
    Vm = [[sc(a), x], [oconj(x), sc(-a)]]
    Wm = [[sc(b), y], [oconj(y), sc(-b)]]
    P, Q = mmul(Vm, Wm), mmul(Wm, Vm)
    S = [[oscale(Fr(1, 2), oadd(P[i][j], Q[i][j])) for j in range(2)] for i in range(2)]
    Bvw = a * b + sum(p * q for p, q in zip(x, y))
    ok &= S == [[sc(Bvw), ZERO], [ZERO, sc(Bvw)]]
print("H_2(O): v o w = (ab + <x,y>) I on 50 random pairs:", ok)
