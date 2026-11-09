#!/usr/bin/env python3
"""Rational enclosures for the all-stage paired-chain invoice frontier.
This proves numerical premises of a written concavity argument. It does not
construct the 17-stage physical controller and does not prove a new DFT bound.
"""
from fractions import Fraction as Q
from functools import lru_cache
from collections import Counter
import json
from pathlib import Path
from verify import H,P,family,need,decimal as decimal_enclosure
def family_coeff(L,R): return family(H,L,R)
SCALE=10**65

def floorq(x):return Q(x.numerator*SCALE//x.denominator,SCALE)
def ceilq(x):return -floorq(-x)

def logunit(x):
    need(1<=x<=2,'log unit range')
    z=(x-1)/(x+1);zz=z*z;v=z;s=Q(0)
    for j in range(72):s+=2*v/(2*j+1);v*=zz
    return s,s+2*v/(145*(1-zz))

@lru_cache(None)
def log_bounds(r):
    k=r.bit_length()-1;a,b=logunit(Q(r,1<<k));l,h=logunit(Q(2))
    return floorq(a+k*l),ceilq(b+k*h)

def expneg(x):
    need(0<=x<=1,'alternating exponential domain')
    s=Q(1);term=Q(1);low=high=None
    for j in range(1,28):
        term*=-x/j;s+=term
        if j==26:high=s
        if j==27:low=s
    return floorq(low),ceilq(high)

def power(r,delta):
    if r==1:return Q(1),Q(1)
    a,b=log_bounds(r);low=expneg(delta*b)[0];high=expneg(delta*a)[1]
    return floorq(r*low),ceilq(r*high)

def margin(c,delta):
    lo=hi=Q(0)
    for r,n in sorted(c.items()):
        if not n:continue
        a,b=power(r,delta);lo+=n*(a if n>0 else b);hi+=n*(b if n>0 else a)
    return lo,hi

def cert():
    low=Q('0.00362461493511114136');high=low+Q(1,10**20)
    c17=family_coeff(8,9);c16=family_coeff(8,8);c18=family_coeff(9,9)
    f17lo=margin(c17,low);f17hi=margin(c17,high)
    need(f17lo[0]>0 and f17hi[1]<0,'frontier signs')
    inc16=Counter(c17);inc16.subtract(c16);inc17=Counter(c18);inc17.subtract(c17)
    def interval_margin(c):
        lo=hi=Q(0)
        for r,n in c.items():
            if not n:continue
            a=power(r,high)[0];b=power(r,low)[1]
            lo+=n*(a if n>0 else b);hi+=n*(b if n>0 else a)
        return lo,hi
    d16=interval_margin(inc16);d17=interval_margin(inc17)
    a={r:H.get(r,0)-P.get(r,0)-(16 if r==8 else 0) for r in set(H)|set(P)}
    need(all(c<=0 for r,c in a.items() if r<=5) and all(c>=0 for r,c in a.items() if r>=6), 'single-crossing native coefficients')
    need(d16[0]>0 and d17[1]<0,'N=17 global discrete maximum')
    return {'root_lower':str(low),'root_upper':str(high),'best_stage_count_in_invoice_family':17,'attaining_lengths_in_model':[8,9],
      'F17_at_lower':[str(v) for v in f17lo], 'F17_at_upper':[str(v) for v in f17hi],
      'increment16_to17_throughout_bracket':decimal_enclosure(d16),'increment17_to18_throughout_bracket':decimal_enclosure(d17),
      'scope':'Exact numerical premises plus the separate all-N discrete-concavity proof. No materialized 17-stage physical circuit, no new DFT theorem, no Lean acceptance.'}
if __name__=='__main__':
    x=cert();p=Path('research/delta005/out/continuation/frontier.json');p.parent.mkdir(parents=True,exist_ok=True);p.write_text(json.dumps(x,indent=2)+'\n');print(json.dumps(x,indent=2));print('PASS_EXACT_ALL_STAGE_FRONTIER; NO_NEW_DFT_THEOREM')
