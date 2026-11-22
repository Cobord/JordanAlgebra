# Independent check: enumerate ALL leaves of the backtracking (no coset assumption) and keep integral ones.
import time
from chain2 import *
u = e(1)
basis, run, in_C = make_search(u)
t = time.time()
tot = 0
for swap in (False, True):
    sols = run(swap, accept=lambda im: verify(to_matrix(basis, im), in_C))
    print("swap", swap, "integral automorphisms:", len(sols), round(time.time()-t,1), flush=True)
    tot += len(sols)
print("TOTAL |G_Lambda| by brute force =", tot)
