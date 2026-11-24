"""The subgroup D_8 x 2T of the Baez-Schwahn chain group.

C = span(1, e1), Q = span(1, e1, e2, e4) (a quaternion subalgebra containing C in the Fano basis of
octo.py), and ell = e3.  D_8 acts by X -> diag(P,1) X diag(P,1)^T with P a signed 2x2 permutation
matrix; a Hurwitz unit u of Q acts entrywise by x + y ell -> x + (u y) ell (x, y in Q).  Checks, in
exact rational arithmetic: every map is a Jordan automorphism of H_3(O_Q) preserving the corner
H_2(C) and H_3(C); the 192 products act by distinct maps; the images on H_2(C), H_3(C) have orders
4 and 8.
"""
import itertools, random, sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from fractions import Fraction as Fr
from octo import omul, oadd, osub, oscale, e
from albert import jprod

Qidx = [0, 1, 2, 4]
ELL = e(3)

def phi(u, x):
    q1 = tuple(x[i] if i in Qidx else Fr(0) for i in range(8))
    q2 = oscale(-1, omul(osub(x, q1), ELL))
    return oadd(q1, omul(omul(u, q2), ELL))

H = []
for i in Qidx:
    for s in (1, -1):
        v = [Fr(0)] * 8; v[i] = Fr(s); H.append(tuple(v))
for sg in itertools.product((1, -1), repeat=4):
    v = [Fr(0)] * 8
    for i, s in zip(Qidx, sg): v[i] = Fr(s, 2)
    H.append(tuple(v))
D8 = []
for perm in ((0, 1), (1, 0)):
    for s in itertools.product((1, -1), repeat=2):
        P = [[0, 0], [0, 0]]
        for r in range(2): P[r][perm[r]] = s[r]
        D8.append(P)

def split(v): return [v[0], v[1], v[2], v[3:11], v[11:19], v[19:27]]
def to_mat(v):  # [[r1,x3,x2bar],[x3bar,r2,x1],[x2,x1bar,r3]] with octonion entries
    from octo import oconj
    r1, r2, r3, x1, x2, x3 = split(v)
    sc = lambda r: (r,) + (Fr(0),) * 7
    return [[sc(r1), x3, oconj(x2)], [oconj(x3), sc(r2), x1], [x2, oconj(x1), sc(r3)]]
def from_mat(M):
    return (M[0][0][0], M[1][1][0], M[2][2][0]) + tuple(M[1][2]) + tuple(M[2][0]) + tuple(M[0][1])
def conjP(P, v):
    Q3 = [[P[0][0], P[0][1], 0], [P[1][0], P[1][1], 0], [0, 0, 1]]
    M = to_mat(v)
    out = [[None] * 3 for _ in range(3)]
    for i in range(3):
        for j in range(3):
            acc = (Fr(0),) * 8
            for k in range(3):
                for l in range(3):
                    c = Q3[i][k] * Q3[j][l]
                    if c: acc = oadd(acc, oscale(Fr(c), M[k][l]))
            out[i][j] = acc
    return from_mat(out)
def act(P, u, v):
    r1, r2, r3, x1, x2, x3 = split(conjP(P, v))
    return (r1, r2, r3) + phi(u, x1) + phi(u, x2) + phi(u, x3)

random.seed(5)
rnd = lambda: tuple(Fr(random.randint(-4, 4), random.choice([1, 2])) for _ in range(27))
tests = [(rnd(), rnd()) for _ in range(4)]
ok = all(act(P, u, jprod(x, y)) == jprod(act(P, u, x), act(P, u, y)) for P in D8 for u in H for x, y in tests)
print("all 192 maps are Jordan automorphisms:", ok)
probe = [rnd() for _ in range(2)]
images = {tuple(act(P, u, p) for p in probe) for P in D8 for u in H}
print("distinct maps:", len(images))
def in_C(x): return all(x[i] == 0 for i in range(2, 8))
def corner(): return (Fr(random.randint(-3, 3)), Fr(random.randint(-3, 3)), Fr(0)) + (Fr(0),) * 16 + (Fr(1), Fr(2)) + (Fr(0),) * 6
def bC():
    v = [Fr(random.randint(-3, 3)) for _ in range(27)]
    for blk in (3, 11, 19):
        for i in range(2, 8): v[blk + i] = Fr(0)
    return tuple(v)
pres = all(in_C(act(P, u, b)[19:27]) and in_C(act(P, u, b)[3:11]) and in_C(act(P, u, b)[11:19]) for P in D8 for u in H for b in [bC()])
c0 = corner()
pres &= all(act(P, u, c0)[2] == 0 and all(t == 0 for t in act(P, u, c0)[3:19]) for P in D8 for u in H)
print("preserve H_3(C) and the corner H_2(C):", pres)
bs = [bC() for _ in range(2)]
print("image orders on H_2(C), H_3(C):",
      len({tuple(act(P, u, c0) for _ in [0]) for P in D8 for u in H}),
      len({tuple(act(P, u, b) for b in bs) for P in D8 for u in H}))
