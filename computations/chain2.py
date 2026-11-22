"""Structured computation of G_Lambda = Aut(J_Z) cap Stab(B) cap Stab(X).

1. K_Lambda = pointwise stabilizer of B = {tau in Aut(O_Z) : tau(u) = u}, acting diagonally.
2. For each automorphism h of B_Lambda preserving X_Lambda (and permuting {e1,e2}), decide whether h lifts
   to an automorphism of J_Q preserving J_Z, by depth-first search for one lift.
|G_Lambda| = |K_Lambda| * #(liftable h).  Every lift is verified in exact rational arithmetic by chain.verify_exact.
"""
import numpy as np
from fractions import Fraction as Fr
from albert import *
from chain import setup, to_matrix, verify


def dot8(x, y):
    return sum(a * b for a, b in zip(x, y))


def aut_O():
    """All 12096 automorphisms of the Coxeter order, as 8x8 rational matrices (lists of images of e_i)."""
    im = [u for u in UNITS if u[0] == 0]
    g1, g2 = e(1), e(2)
    q = omul(g1, g2)
    g3 = next(u for u in im if dot8(u, g1) == 0 and dot8(u, g2) == 0 and dot8(u, q) == 0)

    def basis_from(a, b, c):
        ab = omul(a, b)
        return [ONE, a, b, ab, c, omul(a, c), omul(b, c), omul(ab, c)]
    B0 = basis_from(g1, g2, g3)
    out = []
    for a in im:
        for b in im:
            if dot8(a, b) != 0:
                continue
            ab = omul(a, b)
            for c in im:
                if dot8(c, a) or dot8(c, b) or dot8(c, ab):
                    continue
                Bi = basis_from(a, b, c)

                def apply(x):
                    co = [dot8(x, y) for y in B0]
                    return tuple(sum(cc * y[k] for cc, y in zip(co, Bi)) for k in range(8))
                if all(COX.contains(apply(x)) for x in COX.basis):
                    out.append([apply(e(i)) for i in range(8)])
    return out


def oct_map_matrix(imgs_e):
    return np.array([[float(imgs_e[j][i]) for j in range(8)] for i in range(8)])


def diag_lift(M8):
    """tau acting entrywise on H_3: identity on diagonal, M8 on x1,x2,x3."""
    g = np.zeros((27, 27))
    g[0, 0] = g[1, 1] = g[2, 2] = 1
    for o in (3, 11, 19):
        g[o:o + 8, o:o + 8] = M8
    return g


def make_search(u):
    in_C, C_units, comp = setup(u)
    order = []
    for x in (ONE, u):
        for p in ('12', '23', '31'):
            order.append((p, x, True))
    for x in comp:
        for p in ('12', '23', '31'):
            order.append((p, x, False))
    basis = [diag(0), diag(1), diag(2)] + [F(p, x) for (p, x, _) in order]
    Bmat = np.array([f(b) for b in basis])
    gram = Bmat @ G @ Bmat.T
    tri = np.einsum('ai,bj,ijl,cl->abc', Bmat, Bmat, TRI, Bmat, optimize=True)
    tol = 1e-9

    def run(swap, prefix_only=False, fixed_prefix=None, first_only=False, accept=None):
        sig = {'12': '12', '23': '31', '31': '23'} if swap else {'12': '12', '23': '23', '31': '31'}
        img_diag = [diag(1), diag(0), diag(2)] if swap else [diag(0), diag(1), diag(2)]
        imgs0 = [f(v) for v in img_diag]
        cand = {}
        for k in range(3, 27):
            p, x, inC = order[k - 3]
            pool = C_units if inC else UNITS
            cand[k] = np.array([f(F(sig[p], v)) for v in pool])
        if fixed_prefix is not None:
            for k, y in enumerate(fixed_prefix, start=9 - len(fixed_prefix)):
                cand[k] = np.array([y])
        out = []

        class Stop(Exception):
            pass

        def rec(imgs, A, P, Pidx, k):
            if prefix_only and k == 9:
                out.append([v.copy() for v in imgs[3:9]])
                return
            if k == 27:
                if accept is not None and not accept(imgs):
                    return
                out.append([v.copy() for v in imgs])
                if first_only:
                    raise Stop
                return
            Y = cand[k]
            I = np.array(imgs)
            mask = np.abs((I @ G) @ Y.T - gram[:k, k][:, None]).max(axis=0) < tol
            mask &= np.abs(np.einsum('ni,ij,nj->n', Y, G, Y) - gram[k, k]) < tol
            if mask.any():
                target = tri[np.array([q[0] for q in Pidx]), np.array([q[1] for q in Pidx]), k]
                mask &= np.abs(P @ Y.T - target[:, None]).max(axis=0) < tol
            for n in np.nonzero(mask)[0]:
                y = Y[n]
                Ay = np.einsum('abl,a->bl', TRI, y)
                rows = np.array([Ai @ y for Ai in A])
                if np.abs(rows @ y - tri[:k, k, k]).max() > tol:
                    continue
                if abs(y @ Ay @ y - tri[k, k, k]) > tol:
                    continue
                P2 = np.vstack([P, rows, (Ay @ y)[None, :]])
                Pidx2 = Pidx + [(i, k) for i in range(k)] + [(k, k)]
                imgs.append(y); A.append(Ay)
                rec(imgs, A, P2, Pidx2, k + 1)
                imgs.pop(); A.pop()

        A0 = [np.einsum('abl,a->bl', TRI, v) for v in imgs0]
        P0, Pidx0 = [], []
        for i in range(3):
            for j in range(i, 3):
                P0.append(A0[i] @ imgs0[j]); Pidx0.append((i, j))
        try:
            rec(list(imgs0), A0, np.array(P0), Pidx0, 3)
        except Stop:
            pass
        return out

    return basis, run, in_C
