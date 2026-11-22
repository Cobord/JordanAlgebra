"""Write GAP files: Aut(O_Z) (autO.g) and, for Lambda = Z[i] (gauss) and Z[omega] (eis), the color group
K_Lambda (as permutations of the 240 units of O_Z) and G_Lambda
(as permutations of the 732 norm-2 vectors of J_Z), for both choices of C."""
import pickle, itertools
import numpy as np
from albert import *

def keys(X):
    """Exact key for each row of X (coordinates lie in (1/4)Z)."""
    return [r.tobytes() for r in np.rint(4 * X).astype(np.int8)]

U8 = np.array([f(v) for v in UNITS])
iU = {k: n for n, k in enumerate(keys(U8))}
S = []
for p in ('12', '23', '31'):
    for v in UNITS:
        S.append(f(F(p, v)))
for i, j in itertools.combinations(range(3), 2):
    for si, sj in itertools.product((1, -1), repeat=2):
        w = np.zeros(27); w[i] = si; w[j] = sj; S.append(w)
S = np.array(S)
iS = {k: n for n, k in enumerate(keys(S))}

def gap_perm(M, vecs, idx):
    imgs = [idx[k] + 1 for k in keys(vecs @ M.T)]   # row n is M @ vecs[n]
    return "PermList([" + ",".join(map(str, imgs)) + "])"

for which in ('gauss', 'eis'):
    D = pickle.load(open(which + '2.pkl', 'rb'))
    K, lifts = D['K'], D['lifts']
    with open(f"{which}.g", "w") as fh:
        fh.write(f"K_{which} := Group([" + ",\n".join(gap_perm(k[3:11, 3:11], U8, iU) for k in K) + "]);\n")
        fh.write(f"G_{which} := Group([" + ",\n".join([gap_perm(m, S, iS) for _, m in lifts] + [gap_perm(k, S, iS) for k in K]) + "]);\n")
# Aut(O_Z): 40 random elements of the 12096 automorphisms, as permutations of the 240 units;
# ident.g checks that they generate a group of order 12096.
A = pickle.load(open('autO.pkl', 'rb'))
Uidx = {tuple(v): n for n, v in enumerate(UNITS)}
def img(M, v):
    return tuple(sum(M[j][i] * v[j] for j in range(8)) for i in range(8))
rng = np.random.default_rng(3)
pick = [A[i] for i in rng.choice(len(A), 40, replace=False)]
with open("autO.g", "w") as fh:
    fh.write("AutO := Group([" + ",\n".join(
        "PermList([" + ",".join(str(Uidx[img(M, v)] + 1) for v in UNITS) + "])" for M in pick) + "]);\n")
print("written autO.g, gauss.g, eis.g")
