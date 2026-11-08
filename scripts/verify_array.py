"""Exact Gaussian-rational test of transported query on arbitrary inputs.

Not a proof of universal array statements: exhaustive only for a fixed 4-index
permutation and 8 basis vectors. Universal proofs are authored in Lean source.
"""
from dataclasses import dataclass
from fractions import Fraction as F

@dataclass(frozen=True)
class G:
    a:F=F(0)
    b:F=F(0)
    def __add__(self,o):
        o=g(o); return G(self.a+o.a,self.b+o.b)
    __radd__=__add__
    def __neg__(self):return G(-self.a,-self.b)
    def __sub__(self,o):return self+-g(o)
    def __mul__(self,o):
        o=g(o); return G(self.a*o.a-self.b*o.b,self.a*o.b+self.b*o.a)
    __rmul__=__mul__
    def __truediv__(self,o):
        o=g(o);den=o.a*o.a+o.b*o.b
        return G((self.a*o.a+self.b*o.b)/den,(self.b*o.a-self.a*o.b)/den)
def g(x):return x if isinstance(x,G) else G(F(x),F(0))

I=G(F(0),F(1)); ONE=g(1); ZERO=g(0)
sigma=[1,0,3,2]

def add(x,y):return tuple(a+b for a,b in zip(x,y))
def sub(x,y):return tuple(a-b for a,b in zip(x,y))
def mul(c,x):return tuple(c*a for a in x)
def P(a):return tuple(a[sigma[i]] for i in range(4))
def Q(a):return add(mul((ONE+I)/2,a),mul((ONE-I)/2,P(a)))

def H(v):return (add(*v),sub(*v))
def Hi(v):return (mul(g(F(1,2)),add(*v)),mul(g(F(1,2)),sub(*v)))
def D(v):return (v[0],P(v[1]))
def Lam(v):return H(D(Hi(D(v))))
def QQ(v):return(Q(v[0]),Q(v[1]))

basis=[]
for role in (0,1):
    for i in range(4):
        a=[ZERO]*4; b=[ZERO]*4
        (a if role==0 else b)[i]=ONE
        basis.append((tuple(a),tuple(b)))

for v in basis:
    assert Q(Q(v[0]))==P(v[0])
    assert Q(Q(v[1]))==P(v[1])
    assert Lam(Lam(v))==(P(v[0]),P(v[1]))
    assert Lam(QQ(Lam(QQ(v))))==v
print('PASS_ARRAY_NORMALIZER_AND_TRANSPORTED_QUERY on 8 Gaussian-rational basis inputs')
