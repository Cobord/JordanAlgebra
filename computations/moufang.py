"""Checks for the Moufang lifts of the diagonal: the three maps are Jordan
automorphisms of H_3(O_Q) for a Gaussian and an Eisenstein unit, and the cubic norm formula in the
paper's coordinates satisfies the cubic identity."""
import random, sys
sys.path.insert(0, __import__('os').path.dirname(__file__))
from fractions import Fraction as Fr
from octo import omul, oconj, e, ONE
from albert import jprod
random.seed(3)
def rnd(): return Fr(random.randint(-5,5), random.choice([1,2]))
def split(v): return v[0],v[1],v[2],tuple(v[3:11]),tuple(v[11:19]),tuple(v[19:27])
def join(r1,r2,r3,x1,x2,x3): return (r1,r2,r3)+tuple(x1)+tuple(x2)+tuple(x3)
L=lambda a:(lambda x: omul(a,x)); Rm=lambda a:(lambda x: omul(x,a)); Bm=lambda a:(lambda x: omul(omul(a,x),a))
def make(t1,t2,t3):
    def g(v):
        r1,r2,r3,x1,x2,x3=split(v); return join(r1,r2,r3,t1(x1),t2(x2),t3(x3))
    return g
def check(g,n=30):
    for _ in range(n):
        u=tuple(rnd() for _ in range(27)); w=tuple(rnd() for _ in range(27))
        if g(jprod(u,w))!=jprod(g(u),g(w)): return False
    return True
for name,a in [('gauss',e(1)),('eis',tuple(Fr(x,2) for x in (-1,1,1,1,0,0,0,0)))]:
    ab=oconj(a)
    g1=make(L(a),Rm(a),Bm(ab)); g2=make(Bm(ab),L(a),Rm(a)); g3=make(Rm(a),Bm(ab),L(a))
    print(name,[check(g) for g in (g1,g2,g3)])
from octo import onorm, oadd
def N3(v):
    r1,r2,r3,x1,x2,x3=split(v)
    return r1*r2*r3 - r1*onorm(x1) - r2*onorm(x2) - r3*onorm(x3) + 2*omul(omul(x1,x2),x3)[0]
def add(u,w): return tuple(p+q for p,q in zip(u,w))
def sc(c,u): return tuple(c*p for p in u)
I=(Fr(1),Fr(1),Fr(1))+(Fr(0),)*24
ok=True
for _ in range(20):
    X=tuple(rnd() for _ in range(27)); X2=jprod(X,X); X3=jprod(X2,X)
    T=X[0]+X[1]+X[2]; T2=X2[0]+X2[1]+X2[2]; S=(T*T-T2)/2
    lhs=add(add(X3,sc(-T,X2)),add(sc(S,X),sc(-N3(X),I)))
    ok&= all(c==0 for c in lhs)
print('cubic identity with N=r1r2r3-sum r_i N(x_i)+2Re((x1x2)x3):',ok)
