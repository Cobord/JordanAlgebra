import pickle, collections
from albert import *
autO = pickle.load(open('autO.pkl','rb'))
def apply(M, x): return tuple(sum(M[j][i]*x[j] for j in range(8)) for i in range(8))
# primitive elements of O_Z with trace t, norm n generating C=Q(sqrt(-d)), d = 4n - t^2 (discriminant -(4n-t^2))
from itertools import product
# enumerate lattice vectors of COX with norm <= 3 via small coordinates
vals=[Fr(k,2) for k in range(-4,5)]
cands=collections.defaultdict(list)
import itertools
B=COX.basis
# enumerate integer combos of basis with small coefficients is messy; use coordinates in (1/2)Z with |x_i|<=2 and filter
for x in itertools.product(range(-3,4), repeat=8):
    if sum(c*c for c in x) > 4*3*1: continue
    v = tuple(Fr(c,2) for c in x)
    if not COX.contains(v): continue
    n = sum(c*c for c in v); t = 2*v[0]
    if n == 0: continue
    disc = 4*n - t*t
    if disc <= 0: continue
    if any(c for c in v[1:]):
        cands[int(disc)].append(v)
for disc in sorted(cands)[:8]:
    xs = cands[disc]
    x = xs[0]
    st = sum(1 for M in autO if apply(M, x) == x)
    print(f"-disc = {disc:2d}: e.g. x with trace {2*x[0]}, norm {sum(c*c for c in x)}; |Stab_Aut(O_Z)(x)| = {st}, orbit size {12096//st}")
