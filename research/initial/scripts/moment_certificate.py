"""Pure rational, rigorously outward exact-DFT moment bounds.

No float/Decimal, no numerical sampling, no external libraries.  The proof of the
interval enclosure uses the atanh identity and its positive geometric remainder,
plus the alternating-series theorem for exp(-x) at 0 <= x <= 1.

This is a *Python* certificate, not an imported Lean proof.
"""
import json
import math
from fractions import Fraction as F
from pathlib import Path
from hashlib import sha256

ROOT=Path(__file__).resolve().parents[1]
INV=json.loads((ROOT/'inventory_receipt.json').read_text())
T={int(k):v for k,v in INV['T'].items()}
P={int(k):v for k,v in INV['P'].items()}
C=F(420453,125000000)
M=22                  # atanh-series terms per reduced logarithm
K=9                   # alternating exp(-x): 2K and 2K+1 degree bounds
GRID=10**18


def log_1plus_bounds(x):
    """Bounds log(x), x >= 1, via atanh with z=(x-1)/(x+1)."""
    assert 1 <= x <= 2
    z=(x-1)/(x+1)
    assert 0<=z<=F(1,3)
    total=F(0)
    power=z
    for j in range(M):
        total+=2*power/(2*j+1)
        power*=z*z
    tail=2*power/((2*M+1)*(1-z*z))
    return total,total+tail

L2=log_1plus_bounds(F(2))
def log_bounds(r):
    assert isinstance(r,int) and r>=1
    k=r.bit_length()-1
    y=F(r,1<<k)
    l,u=log_1plus_bounds(y)
    return k*L2[0]+l, k*L2[1]+u


def alternating_exp_neg(x, degree):
    """Partial sums of exp(-x), with 0<=x<1."""
    assert F(0)<=x<F(1)
    s=F(1);power=F(1)
    for j in range(1,degree+1):
        power*=(-x)/j
        s+=power
    return s


def pow_1_minus_C_bounds(r):
    if r==1: return F(1),F(1)
    lo,hi=log_bounds(r)
    xlo,xhi=C*lo,C*hi
    assert 0<=xlo<=xhi<F(1)
    down=alternating_exp_neg(xhi,2*K+1)
    up=alternating_exp_neg(xlo,2*K)
    assert 0<down<up<1
    return r*down,r*up


def moment_bounds(hist):
    lo=hi=F(0)
    for r,mult in sorted(hist.items()):
        a,b=pow_1_minus_C_bounds(r)
        lo+=mult*a;hi+=mult*b
    return lo,hi

def floor_grid(x): return (x.numerator*GRID)//x.denominator

def ceil_grid(x): return -((-x.numerator*GRID)//x.denominator)

def bracket(x): return {'lower_num':floor_grid(x[0]),'upper_num':ceil_grid(x[1]),'denominator':GRID}

TL,TU=moment_bounds(T)
PL,PU=moment_bounds(P)
margin=(TL-PU,TU-PL)
assert margin[0]>0
# a = paid moment / target moment, all endpoints positive.
a=(PL/TU,PU/TL)
assert a[1]<1-F(1,10**10)
# 12^(-C) = exp(-C log(12)); exp upper at the lower logarithm endpoint.
log12=log_bounds(12)
exp12lo=alternating_exp_neg(C*log12[1],2*K+1)
exp12hi=alternating_exp_neg(C*log12[0],2*K)
paid_mass=sum(r*n for r,n in P.items())
n_targets=sum(T.values())
g=(paid_mass*exp12lo/TU,paid_mass*exp12hi/TL)
h=(13*n_targets*exp12lo/TU,13*n_targets*exp12hi/TL)
assert g[1]<F(499,500), g[1]-F(499,500)
assert h[1]<F(19,20), h[1]-F(19,20)
assert 2*499**400<500**400 and 2*19**80<20**80
assert F(1,1)/(1+F(12800,10**10)) + 2*F(1,2)**32+2*F(1,2)**160 < 1
receipt={
    'algorithm':'rational atanh enclosure + alternating exponential enclosure',
    'atanh_terms':M,'exp_upper_degree':2*K,'exp_lower_degree':2*K+1,
    'finite_saving_num':C.numerator,'finite_saving_den':C.denominator,
    'grid_denominator':GRID,
    'T_moment':bracket((TL,TU)),
    'P_moment':bracket((PL,PU)),
    'margin':bracket(margin),
    'alpha_ratio':bracket(a),
    'gamma_ratio':bracket(g),
    'completion_ratio':bracket(h),
    'alpha_cap_num_den':[10**10-1,10**10],
    'gamma_cap_num_den':[499,500],
    'completion_cap_num_den':[19,20],
    'strict_positive_margin':margin[0]>0,
    'all_three_ratio_checks':True,
    'tensor_power':12800,'cutoff':12,'floor':13,
    'physical_histogram_sha256':sha256((ROOT/'inventory_receipt.json').read_bytes()).hexdigest(),
}
pth=ROOT/'moment_receipt.json'
pth.write_text(json.dumps(receipt,sort_keys=True,indent=2)+'\n')
for name in ('margin','alpha_ratio','gamma_ratio','completion_ratio'):
    print(name,receipt[name])
print('PASS_RATIONAL_MOMENT_CERTIFICATE',sha256(pth.read_bytes()).hexdigest())
