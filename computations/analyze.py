import sys, pickle, collections, itertools
import numpy as np
from sympy.combinatorics import Permutation, PermutationGroup
from albert import *
from fractions import Fraction as Fr

which = sys.argv[1]
D = pickle.load(open(which + '2.pkl', 'rb'))
u, lifts, K = D['u'], D['lifts'], D['K']

# finite faithful G-set: norm-2 vectors of J_Z (off-diagonal units, and +-e_i +- e_j)
S = []
for p in ('12', '23', '31'):
    for v in UNITS:
        S.append(f(F(p, v)))
for i, j in itertools.combinations(range(3), 2):
    for si, sj in itertools.product((1, -1), repeat=2):
        w = np.zeros(27); w[i] = si; w[j] = sj; S.append(w)
key = lambda w: tuple(int(round(4 * x)) for x in w)
idx = {key(w): n for n, w in enumerate(S)}
assert len(idx) == len(S) == 732


def perm(g):
    return Permutation([idx[key(g @ w)] for w in S])


gens = [perm(m) for _, m in lifts] + [perm(k) for k in K]
Gp = PermutationGroup(gens)
print(which, "|G_Lambda| (closure of generators) =", Gp.order())
Kp = PermutationGroup([perm(k) for k in K])
print("|K_Lambda| =", Kp.order(), " normal in G_Lambda:", Kp.is_normal(Gp))

# identity component test: Im tr(H1 H2 H3) on B = H_3(C)
im_u = np.array([0.0] + [float(x) for x in u[1:]])
iC = im_u / np.linalg.norm(im_u)


def to_cplx(o8):
    return o8[0] + 1j * (o8 @ iC)


def Bmat(v):
    r1, r2, r3 = v[0], v[1], v[2]
    x1, x2, x3 = to_cplx(v[3:11]), to_cplx(v[11:19]), to_cplx(v[19:27])
    return np.array([[r1, x3, np.conj(x2)], [np.conj(x3), r2, x1], [x2, np.conj(x1), r3]])


def Bvec(z1, z2, z3, r):
    v = np.zeros(27)
    v[:3] = r
    for o, z in ((3, z1), (11, z2), (19, z3)):
        v[o] = z.real
        v[o:o + 8] += z.imag * iC
    return v


rng = np.random.default_rng(1)
Hs = [Bvec(*(rng.normal(size=3) + 1j * rng.normal(size=3)), rng.normal(size=3)) for _ in range(3)]
inv0 = np.trace(Bmat(Hs[0]) @ Bmat(Hs[1]) @ Bmat(Hs[2])).imag


def eps(g):
    val = np.trace(Bmat(g @ Hs[0]) @ Bmat(g @ Hs[1]) @ Bmat(g @ Hs[2])).imag
    assert abs(abs(val) - abs(inv0)) < 1e-8
    return 1 if val * inv0 > 0 else -1


# enumerate the group as matrices (cosets lift * K) to split by component
mats = [m @ k for _, m in lifts for k in K]
signs = [eps(g) for g in mats]
print("components (eps=+1 identity component of Stab(B)):", dict(collections.Counter(signs)))
pos = [g for g, s in zip(mats, signs) if s == 1]
rng2 = np.random.default_rng(7)
G0 = PermutationGroup([perm(pos[i]) for i in rng2.choice(len(pos), 40, replace=False)])
print("|G_Lambda cap Stab(B)^0| =", G0.order())

if which == 'gauss':
    # complex 3-dim representation of K_Lambda on the orthogonal complement of C in O (complex structure: left mult by iC)
    def Lmul(a):
        return np.array([[float(omul(a, e(j))[i]) for j in range(8)] for i in range(8)])
    J8 = sum(iC[k] * Lmul(e(k)) for k in range(1, 8))   # left multiplication by iC
    Pc = np.eye(8) - np.outer([1]+[0]*7, [1]+[0]*7) - np.outer(iC, iC)
    w, V = np.linalg.eigh(Pc)
    W = V[:, w > 0.5]                                     # real basis of C-perp (6-dim)
    # complex basis: pick w1, then J w1, etc. via Gram-Schmidt over C
    cb = []
    for col in W.T:
        v = col.copy()
        for b in cb:
            v -= (b @ v) * b + ((J8 @ b) @ v) * (J8 @ b)
        if np.linalg.norm(v) > 1e-6:
            cb.append(v / np.linalg.norm(v))
        if len(cb) == 3: break
    def cplx_rep(M8):
        # matrix of M8 on C-perp in complex basis cb: entry = <b_r, M b_c> + i <J b_r, M b_c>
        R = np.zeros((3, 3), complex)
        for r in range(3):
            for c in range(3):
                y = M8 @ cb[c]
                R[r, c] = cb[r] @ y + 1j * ((J8 @ cb[r]) @ y)
        return R
    Kc = [cplx_rep(k[3:11, 3:11]) for k in K]
    
    print("   K_Lambda in U(3): unitary", all(np.allclose(R @ R.conj().T, np.eye(3)) for R in Kc),
          " det=1:", all(abs(np.linalg.det(R) - 1) < 1e-9 for R in Kc))
    # abelian normal subgroup: elements whose permutation lies in derived^2
    D2p = set(Kp.derived_subgroup().derived_subgroup().generate())
    D2m = [R for R, k in zip(Kc, K) if perm(k) in D2p]
    print("   |Z4xZ4 candidate| =", len(D2m), " abelian:", all(np.allclose(a @ b, b @ a) for a in D2m for b in D2m))
    # simultaneous eigenbasis of D2m
    Mgen = sum((n + 1) * R for n, R in enumerate(D2m))
    ev, P = np.linalg.eig(Mgen)
    Pin = np.linalg.inv(P)
    mono = [Pin @ R @ P for R in Kc]
    def is_monomial(A):
        nz = np.abs(A) > 1e-8
        return nz.sum(axis=0).max() == 1 and nz.sum(axis=1).max() == 1
    nth = int(sys.argv[2]) if len(sys.argv) > 2 else 4
    roots = np.exp(2j * np.pi * np.arange(nth) / nth)
    def entries_ok(A):
        return all(min(abs(x - roots)) < 1e-8 for x in A[np.abs(A) > 1e-8])
    # normalise phases: make an order-3 cyclic monomial element a pure permutation matrix
    def pattern(A):
        return tuple(int(np.argmax(np.abs(A[:, c]))) for c in range(3))
    cyc = next(A for A in mono if pattern(A) in [(1, 2, 0), (2, 0, 1)])
    pat = pattern(cyc)
    # cyc e_c = a_c e_{pat[c]}; choose D = diag(d) with D^-1 cyc D a permutation matrix:
    d = np.ones(3, complex)
    c = 0
    for _ in range(2):
        nxt = pat[c]
        d[nxt] = cyc[nxt, c] * d[c]
        c = nxt
    Dm = np.diag(d)
    mono = [np.linalg.inv(Dm) @ A @ Dm for A in mono]
    # remaining: entries should now lie in a fixed finite set
    vals = np.concatenate([A[np.abs(A) > 1e-8] for A in mono])
    angles = sorted(set(np.round(np.angle(vals) / (2 * np.pi) * 24).astype(int) % 24))
    print("   after phase normalisation, entry phases (in units of 2pi/24):", angles)
    # compare with the explicit group of monomial SU(3) matrices with entries in mu_nth
    std = []
    for p in itertools.permutations(range(3)):
        for a in itertools.product(range(nth), repeat=3):
            A = np.zeros((3, 3), complex)
            for col in range(3):
                A[p[col], col] = roots[a[col]]
            if abs(np.linalg.det(A) - 1) < 1e-9:
                std.append(A)
    Sset = {tuple(np.round(A.real.flatten(), 6)) + tuple(np.round(A.imag.flatten(), 6)) for A in std}
    Kset = {tuple(np.round(A.real.flatten(), 6)) + tuple(np.round(A.imag.flatten(), 6)) for A in mono}
    print(f"   explicit monomial group with mu_{nth} entries and det 1: order {len(std)};  K_Lambda equals it after conjugation: {Sset == Kset}")
    print(f"   in the eigenbasis of the abelian normal subgroup: all monomial {all(is_monomial(A) for A in mono)}, "
          f"nonzero entries are {nth}th roots of unity: {all(entries_ok(A) for A in mono)}")
