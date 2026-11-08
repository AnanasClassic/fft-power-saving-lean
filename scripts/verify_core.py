"""Independent, exact preflight of algebra/inventory/parameter lemmas.

Uses only the Python standard library; not a substitute for a Lean kernel run.
All polynomial identities are checked in the quotient ring
Q[p,q]/(p^2-1, q^2-p), without sampling p/q values.
"""
from fractions import Fraction as F
from pathlib import Path
import json

ROOT = Path(__file__).resolve().parents[1]
class Poly:
    def __init__(self, terms=None):
        self.d = {k:v for k,v in (terms or {}).items() if v}
    @staticmethod
    def c(x): return Poly({(0,0):F(x)})
    def __add__(self, oth):
        oth = aspoly(oth); out = dict(self.d)
        for k,v in oth.d.items():out[k]=out.get(k,F(0))+v
        return Poly(out)
    __radd__=__add__
    def __neg__(self): return Poly({k:-v for k,v in self.d.items()})
    def __sub__(self,oth):return self+-aspoly(oth)
    def __rsub__(self,oth):return aspoly(oth)+-self
    def __mul__(self,oth):
        oth=aspoly(oth); out={}
        for (a,b),x in self.d.items():
            for (c,d),y in oth.d.items():
                # q^2=p, p^2=1; this rewrite is confluent and defines a finite ring.
                pp=(a+c+(b+d)//2)%2;qq=(b+d)%2
                out[(pp,qq)] = out.get((pp,qq),F(0))+x*y
        return Poly(out)
    __rmul__=__mul__
    def __truediv__(self,n):return self*F(1,n)
    def __eq__(self,other):return self.d==aspoly(other).d
    def __repr__(self):return str(self.d)

def aspoly(x):return x if isinstance(x,Poly) else Poly.c(x)

P=Poly({(1,0):F(1)})
Q=Poly({(0,1):F(1)})
Z=Poly.c(0)
ONE=Poly.c(1)
assert P*P==ONE and Q*Q==P

def mm(a,b):
    return [[sum((a[i][k]*b[k][j] for k in range(len(b))),Z)
             for j in range(len(b[0]))] for i in range(len(a))]

def eye(n): return [[ONE if i==j else Z for j in range(n)] for i in range(n)]

H=[[ONE,ONE],[ONE,-ONE]]
Hi=[[ONE/2,ONE/2],[ONE/2,-ONE/2]]
D=[[ONE,Z],[Z,P]]
J=[[Z,-ONE],[ONE,Z]]
I=eye(2)
L=mm(mm(mm(H,D),Hi),D)
expected=[[ (ONE+P)/2, -(ONE-P)/2],[(ONE-P)/2,(ONE+P)/2]]
assert L==expected, (L,expected)
assert mm(H,Hi)==I and mm(Hi,H)==I
assert mm(L,L)==[[P,Z],[Z,P]]
LQ=mm(L,[[Q,Z],[Z,Q]])
assert mm(LQ,LQ)==I
print('PASS_NORMALIZER_QUOTIENT_RING')

h={1:14,2:8,3:4,4:107,5:14,6:2,7:9,8:19,9:385}
p={1:2216,2:456,3:496,4:98,5:165,6:8,7:9,8:1}
I=lambda a,b:int(a==b)
T={r:2*(18*h.get(r,0)+104*(I(r,1)+I(r,145)+2*sum(I(r,8*j+1) for j in range(1,10)))) for r in range(146)}
B={r:2*(18*p.get(r,0)+104*(3*I(r,1)+2*sum(I(r,8*j) for j in range(1,9)))) for r in range(146)}
T={r:n for r,n in T.items() if n}; B={r:n for r,n in B.items() if n}
assert (sum(T.values()),sum(B.values())) == (24392,128116)
assert (sum(r*n for r,n in T.items()),sum(r*n for r,n in B.items())) == (336224,334704)
assert max(T)==145 and max(B)==64
assert 336224-334704==1520
receipt = json.loads((ROOT/'inventory_receipt.json').read_text())
assert {int(k):v for k,v in receipt['T'].items()}==T
assert {int(k):v for k,v in receipt['P'].items()}==B
print('PASS_INVENTORY_FORMULA_AND_RECEIPT')

C=F(420453,125000000)
eta=F(6727247,2000000000)
delta=F(3363623,1000000000)
assert C-eta == eta-delta == F(1,2000000000)
assert 0<delta<eta<C<1
assert F(1,1)/(1+F(12800,10**10))+2*F(1,2)**32+2*F(1,2)**160 < 1
assert 2*499**400<500**400
assert 2*19**80<20**80
print('PASS_RATIONAL_GAPS_AND_TAILS')
