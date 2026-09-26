#!/usr/bin/env python3
"""No-subdivision checker for the large-angle hand reduction.

It checks:
  * seven source-independent concavity margins;
  * the 128 endpoint values left after the hand concavity reduction.

The endpoint stress formula is imported from the earlier exact certificate.
"""
from fractions import Fraction as F
from itertools import product
from math import factorial

from check_large_candidate_graph_certificate import I as StressI
from check_large_candidate_graph_certificate import Q0, lower


class J:
    def __init__(self, lo, hi=None):
        self.lo=F(lo); self.hi=F(lo if hi is None else hi); assert self.lo<=self.hi
    def __add__(self,o): o=j(o); return J(self.lo+o.lo,self.hi+o.hi)
    __radd__=__add__
    def __neg__(self): return J(-self.hi,-self.lo)
    def __sub__(self,o): return self+(-j(o))
    def __rsub__(self,o): return j(o)-self
    def __mul__(self,o):
        o=j(o); xs=(self.lo*o.lo,self.lo*o.hi,self.hi*o.lo,self.hi*o.hi)
        return J(min(xs),max(xs))
    __rmul__=__mul__


def j(x):
    return x if isinstance(x,J) else J(x)


def sinb(x,n=9):
    x=F(x)
    ts=[F((-1)**k)*x**(2*k+1)/F(factorial(2*k+1)) for k in range(n+2)]
    s=sum(ts[:n+1],F(0)); t=s+ts[n+1]
    return J(min(s,t),max(s,t))


def cosb(x,n=9):
    x=F(x)
    ts=[F((-1)**k)*x**(2*k)/F(factorial(2*k)) for k in range(n+2)]
    s=sum(ts[:n+1],F(0)); t=s+ts[n+1]
    return J(min(s,t),max(s,t))


def positive(name,x):
    assert x.lo>0,(name,x.lo,x.hi)
    print(name,">",float(x.lo))


H=J(F(70710678,10**8),F(70710679,10**8))
a=F(1,6); b=F(1,3)
sa,ca=sinb(a),cosb(a); sb,cb=sinb(b),cosb(b)
sx,cx=sinb(F(1,12)),cosb(F(1,12))
c7=cosb(F(7,12))

TEs=F(167,500)*cb
TEe=F(6847,35000)*sa+F(26263,140500)*cb
TNw=F(84,125)*(sa+cb)
TNn=F(1848,6625)*sa+F(12043,25625)*cb
TSs=F(8003927,9835000)*sa+F(18438,35125)*cb
TSe=F(21714,35125)*sa+F(84,125)*cb
TWw=F(13527,102500)*cb-F(498416,1358125)*sb
TWn=F(668,25625)*sa+F(167,500)*cb
EDW=F(378,500)*H*c7
NW=F(31,125)*(ca-sa)
P=F(97713,197000)*sa
EDS=F(517,1000)*H*(cx-sx)

def min_by_lower(x,y):
    return x if x.lo<=y.lo else y

TE=min_by_lower(TEs,TEe)
TN=min_by_lower(TNw,TNn)
TS=min_by_lower(TSs,TSe)
TW=min_by_lower(TWw,TWn)

positive("te_concavity",TE)
positive("tn_concavity",TN)
positive("tw_concavity",TW+EDW+NW-P)
positive("ts_concavity",TS+EDS-P)
positive("ed_concavity",EDW+EDS)
positive("NW_diagonal_concavity",TN+TW+EDW-P)
positive("ES_diagonal_concavity",TE+TS+EDS-P)

vals=(F(1,6),F(1,3))
eps=(F(-1,4),F(1,4))
best=None

for src5 in ("W","N"):
    for src6 in ("S","E"):
        for te,tn,tw,ts in product(vals,repeat=4):
            for ed in eps:
                box=(StressI(te),StressI(tn),StressI(tw),StressI(ts),StressI(ed))
                out=lower(*box,src5,src6)
                assert out.lo>Q0,(src5,src6,te,tn,tw,ts,ed,out.lo)
                row=(out.lo-Q0,src5,src6,te,tn,tw,ts,ed)
                if best is None or row[0]<best[0]:
                    best=row

print("endpoint minimum margin >",float(best[0]))
print("endpoint argmin",best[1:])
print("large-angle hand checks: PASS")
