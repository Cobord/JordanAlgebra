import sys, time, pickle
import numpy as np
from chain2 import *
from chain import verify_exact
which = sys.argv[1]
u = e(1) if which == 'gauss' else next(v for v in UNITS if v[0] == Fr(-1, 2))
print(which, "u =", [str(x) for x in u], flush=True)
autO = pickle.load(open('autO.pkl', 'rb'))
uidx = [str(x) for x in u]
K = [M for M in autO if tuple(sum(M[j][i]*u[j] for j in range(8)) for i in range(8)) == u]
print("|K_Lambda| = |Stab_{Aut(O_Z)}(u)| =", len(K), flush=True)
basis, run, in_C = make_search(u)
lifts = []
t = time.time()
for swap in (False, True):
    prefixes = run(swap, prefix_only=True)
    print(f"swap={swap}: automorphisms of B_Lambda preserving X_Lambda with this action on the frame: {len(prefixes)}", flush=True)
    for pre in prefixes:
        sol = run(swap, fixed_prefix=pre, first_only=True, accept=lambda im: verify(to_matrix(basis, im), in_C))
        if sol:
            m = to_matrix(basis, sol[0])
            verify_exact(m, in_C, u)   # raises unless exact checks pass
            lifts.append((swap, m))
    print(f"  liftable: {sum(1 for s,_ in lifts if s==swap)}   ({round(time.time()-t,1)} s)", flush=True)
Kmats = [diag_lift(oct_map_matrix(M)) for M in K]
pickle.dump({'u': u, 'lifts': lifts, 'K': Kmats}, open(which + '2.pkl', 'wb'))
print("|G_Lambda| =", len(K) * len(lifts))
