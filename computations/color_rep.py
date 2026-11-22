"""The color group K_Lambda acting on C-perp = C^3 (complex structure: left multiplication by the unit
imaginary element of C).  Checks determinant 1 and irreducibility (mean of |trace|^2 equals 1)."""
import pickle
import numpy as np
from albert import *

for which in ('gauss', 'eis'):
    D = pickle.load(open(which + '2.pkl', 'rb'))
    u, K = D['u'], D['K']
    im_u = np.array([0.0] + [float(x) for x in u[1:]])
    iC = im_u / np.linalg.norm(im_u)

    def Lmul(a):
        return np.array([[float(omul(a, e(j))[i]) for j in range(8)] for i in range(8)])
    J8 = sum(iC[k] * Lmul(e(k)) for k in range(1, 8))
    Pc = np.eye(8) - np.outer([1] + [0] * 7, [1] + [0] * 7) - np.outer(iC, iC)
    wv, V = np.linalg.eigh(Pc)
    W = V[:, wv > 0.5]
    cb = []
    for col in W.T:
        v = col.copy()
        for b in cb:
            v -= (b @ v) * b + ((J8 @ b) @ v) * (J8 @ b)
        if np.linalg.norm(v) > 1e-6:
            cb.append(v / np.linalg.norm(v))
        if len(cb) == 3:
            break

    def rep(M8):
        R = np.zeros((3, 3), complex)
        for r in range(3):
            for c in range(3):
                y = M8 @ cb[c]
                R[r, c] = cb[r] @ y + 1j * ((J8 @ cb[r]) @ y)
        return R
    Kc = [rep(k[3:11, 3:11]) for k in K]
    print(which, "|K| =", len(Kc),
          " unitary:", all(np.allclose(R @ R.conj().T, np.eye(3)) for R in Kc),
          " det 1:", all(abs(np.linalg.det(R) - 1) < 1e-9 for R in Kc),
          " mean |tr|^2 =", round(float(np.mean([abs(np.trace(R)) ** 2 for R in Kc])), 10))
