import pickle, collections, itertools, sys
import numpy as np
from sympy.combinatorics import Permutation, PermutationGroup
from albert import *
D = pickle.load(open('eis2.pkl','rb'))
u, lifts, K = D['u'], D['lifts'], D['K']
# act on the 240 units of O via the x1-block of K
key = lambda w: tuple(int(round(4*x)) for x in w)
Uf = [f(v) for v in UNITS]; idx = {key(w): n for n, w in enumerate(Uf)}
perm = lambda M: Permutation([idx[key(M @ w)] for w in Uf])
Kp = PermutationGroup([perm(k[3:11,3:11]) for k in K])
print("|K| =", Kp.order())
Z = Kp.center(); print("center", Z.order())
S3 = Kp.derived_subgroup().derived_subgroup()
print("K'' order", S3.order(), "K'' abelian", S3.is_abelian, "center(K'')", S3.center().order(), "exponent-3:", all(x.order() in (1,3) for x in S3.generate()))
# quotient K/K'' : coset action
Q = Kp.coset_transversal(S3) if hasattr(Kp,'coset_transversal') else None
els = list(Kp.generate())
S3set = set(S3.generate())
# build quotient elements as frozensets of cosets
cos = {}
for g in els:
    c = frozenset(g*h for h in S3set)
    cos.setdefault(c, g)
reps = list(cos.values())
print("|K/K''| =", len(reps))
def qorder(g):
    n, x = 1, g
    while x not in S3set:
        x = x*g; n += 1
    return n
print("orders in K/K'':", sorted(collections.Counter(qorder(g) for g in reps).items()), "(Q8: one element of order 2, six of order 4)")
