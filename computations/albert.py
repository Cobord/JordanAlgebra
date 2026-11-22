"""H_3(O) over Q with the integral Coxeter lattice; trace form and trilinear form."""
from fractions import Fraction as Fr
import numpy as np
from octo import *

COX_P, COX = coxeter_candidates()[0]
UNITS = units_of(COX)


def jmat(v):
    """v = 27-tuple (r1,r2,r3,x1[8],x2[8],x3[8]) -> 3x3 matrix of octonions."""
    r1, r2, r3 = v[0], v[1], v[2]
    x1 = tuple(v[3:11]); x2 = tuple(v[11:19]); x3 = tuple(v[19:27])
    R = lambda r: tuple([r] + [Fr(0)] * 7)
    return [[R(r1), x3, oconj(x2)],
            [oconj(x3), R(r2), x1],
            [x2, oconj(x1), R(r3)]]


def jvec(M):
    r1, r2, r3 = M[0][0][0], M[1][1][0], M[2][2][0]
    for i in range(3):
        assert all(c == 0 for c in M[i][i][1:]), "diagonal not real"
    x1, x2, x3 = M[1][2], M[2][0], M[0][1]
    assert M[2][1] == oconj(x1) and M[0][2] == oconj(x2) and M[1][0] == oconj(x3)
    return (r1, r2, r3) + x1 + x2 + x3


def mmul(A, B):
    C = [[ZERO] * 3 for _ in range(3)]
    for i in range(3):
        for j in range(3):
            s = ZERO
            for k in range(3):
                s = oadd(s, omul(A[i][k], B[k][j]))
            C[i][j] = s
    return C


def jprod(u, v):
    A, B = jmat(u), jmat(v)
    P, Q = mmul(A, B), mmul(B, A)
    M = [[oscale(Fr(1, 2), oadd(P[i][j], Q[i][j])) for j in range(3)] for i in range(3)]
    return jvec(M)


def zero27():
    return tuple([Fr(0)] * 27)


def diag(i):
    v = [Fr(0)] * 27
    v[i] = Fr(1)
    return tuple(v)


POS = {'23': 3, '31': 11, '12': 19}  # x1 at (2,3), x2 at (3,1), x3 at (1,2)


def F(pos, u):
    v = [Fr(0)] * 27
    o = POS[pos]
    for k in range(8):
        v[o + k] = u[k]
    return tuple(v)


def ip(u, v):
    """trace form tr(u o v) = sum r r' + 2 sum <x,x'>"""
    s = u[0] * v[0] + u[1] * v[1] + u[2] * v[2]
    s += 2 * sum(a * b for a, b in zip(u[3:], v[3:]))
    return s


# structure tensor in standard coordinates (exact)
STD = [tuple(Fr(int(i == j)) for j in range(27)) for i in range(27)]


def build_tensor():
    prods = {}
    for i in range(27):
        for j in range(i, 27):
            prods[(i, j)] = jprod(STD[i], STD[j])
            prods[(j, i)] = prods[(i, j)]
    return prods


PRODS = build_tensor()


def jprod_fast(u, v):
    r = [Fr(0)] * 27
    for i in range(27):
        if u[i] == 0:
            continue
        for j in range(27):
            if v[j] == 0:
                continue
            c = u[i] * v[j]
            p = PRODS[(i, j)]
            for k in range(27):
                if p[k]:
                    r[k] += c * p[k]
    return tuple(r)


# float versions for search
G = np.diag([1.0] * 3 + [2.0] * 24)
Tn = np.zeros((27, 27, 27))
for (i, j), p in PRODS.items():
    Tn[i, j, :] = [float(x) for x in p]
# trilinear form T(x,y,z) = tr((x o y) o z) = ip(x o y, z) = (x^T Tn y)^T G z
TRI = np.einsum('ijk,kl->ijl', Tn, G)


def f(v):
    return np.array([float(x) for x in v])
