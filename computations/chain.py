"""Shared setup for the integral Baez--Schwahn chain X = H_2(C) (corner 1,2) in B = H_3(C) in J = H_3(O).

C = Q + Q*u for a unit u of the Coxeter order (u^2 = -1 Gaussian, u^2 + u + 1 = 0 Eisenstein).
setup() returns the membership test for C, the units of C_Z, and six units spanning C-perp;
to_matrix() turns images of a basis into a 27x27 matrix.
verify() is a fast floating-point filter used inside the search; verify_exact() rounds a candidate
to the grid (1/8)Z and checks it in exact rational arithmetic.
"""
import sys
import numpy as np
from fractions import Fraction as Fr
from albert import *


def dot8(x, y):
    return sum(a * b for a, b in zip(x, y))


def setup(u):
    """Return C-units, complement basis units, for C = span(1,u)."""
    # exact membership test in span(1,u)
    im_u = tuple([Fr(0)] + list(u[1:]))
    nu = dot8(im_u, im_u)

    def in_C(v):
        a = v[0]
        im = tuple([Fr(0)] + list(v[1:]))
        t = dot8(im, im_u) / nu
        return all(x == 0 for x in osub(im, oscale(t, im_u)))
    C_units = [v for v in UNITS if in_C(v)]
    # complement: units orthogonal to C, choose 6 independent
    orth = [v for v in UNITS if dot8(v, ONE) == 0 and dot8(v, u) == 0]
    comp = []
    for v in orth:
        trial = comp + [v]
        if Lattice([ONE, u] + trial).rank() == 2 + len(trial):
            comp = trial
        if len(comp) == 6:
            break
    assert len(comp) == 6
    return in_C, C_units, comp


def to_matrix(basis, imgs):
    Bm = np.array([f(b) for b in basis]).T
    Im = np.array(imgs).T
    return Im @ np.linalg.inv(Bm)


def verify(gm, in_C):
    """Floating-point filter: g preserves the product on all standard basis pairs (tolerance 1e-9)
    and maps the Z-basis of J_Z into J_Z after rounding to (1/4)Z.  Not a proof; see verify_exact."""
    # product
    for i in range(27):
        for j in range(i, 27):
            lhs = gm @ np.array([float(x) for x in PRODS[(i, j)]])
            rhs = np.einsum('i,ijk,j->k', gm[:, i], Tn, gm[:, j])
            if np.max(np.abs(lhs - rhs)) > 1e-9:
                return False
    # lattice J_Z = Z^3 + COX^3
    Zb = [diag(0), diag(1), diag(2)] + [F(p, b) for p in ('23', '31', '12') for b in COX.basis]
    for b in Zb:
        w = gm @ f(b)
        wq = [Fr(round(x * 4), 4) for x in w]
        if max(abs(float(a) - x) for a, x in zip(wq, w)) > 1e-9:
            return False
        if any(x.denominator != 1 for x in wq[:3]):
            return False
        for o in (3, 11, 19):
            if not COX.contains(tuple(wq[o:o + 8])):
                return False
    return True


def _det(M):
    """Exact determinant of a square matrix of Fractions (Gaussian elimination)."""
    A = [row[:] for row in M]
    n = len(A)
    d = Fr(1)
    for c in range(n):
        p = next((r for r in range(c, n) if A[r][c] != 0), None)
        if p is None:
            return Fr(0)
        if p != c:
            A[c], A[p] = A[p], A[c]
            d = -d
        d *= A[c][c]
        for r in range(c + 1, n):
            if A[r][c]:
                q = A[r][c] / A[c][c]
                A[r] = [x - q * y for x, y in zip(A[r], A[c])]
    return d


def verify_exact(gm, in_C, u):
    """Exact verification of a candidate automorphism g (27x27 float matrix in standard coordinates).
    Rounds g to (1/8)Z and checks, in exact rational arithmetic, that g
      * preserves the Jordan product on all pairs of standard basis vectors,
      * maps the Z-basis of J_Z into J_Z and has determinant +-1 (hence g(J_Z) = J_Z),
      * maps B = H_3(C) and X = H_2(C) (upper-left corner) into themselves (hence onto, by dimension).
    Returns the exact matrix (list of rows of Fractions) or raises AssertionError."""
    R = [[Fr(round(8 * x), 8) for x in row] for row in gm]
    assert max(abs(float(R[i][j]) - gm[i][j]) for i in range(27) for j in range(27)) < 1e-9, "not on the 1/8 grid"
    cols = [tuple(R[k][i] for k in range(27)) for i in range(27)]

    def apply(v):
        return tuple(sum(R[k][i] * v[i] for i in range(27) if v[i]) for k in range(27))
    for i in range(27):
        for j in range(i, 27):
            p = PRODS[(i, j)]
            lhs = tuple(sum(p[k] * cols[k][r] for k in range(27) if p[k]) for r in range(27))
            assert lhs == jprod_fast(cols[i], cols[j]), "product not preserved"
    Zb = [diag(0), diag(1), diag(2)] + [F(p, b) for p in ('23', '31', '12') for b in COX.basis]
    for b in Zb:
        w = apply(b)
        assert all(x.denominator == 1 for x in w[:3]), "diagonal not integral"
        for o in (3, 11, 19):
            assert COX.contains(tuple(w[o:o + 8])), "off-diagonal entry not in the Coxeter order"
    assert abs(_det(R)) == 1, "determinant not +-1"

    def in_B(w):
        return all(in_C(tuple(w[o:o + 8])) for o in (3, 11, 19))

    def in_X(w):
        return w[2] == 0 and all(x == 0 for x in w[3:19]) and in_C(tuple(w[19:27]))
    Bb = [diag(0), diag(1), diag(2)] + [F(p, x) for p in ('23', '31', '12') for x in (ONE, u)]
    Xb = [diag(0), diag(1), F('12', ONE), F('12', u)]
    assert all(in_B(apply(b)) for b in Bb), "B not preserved"
    assert all(in_X(apply(b)) for b in Xb), "X not preserved"
    return R
