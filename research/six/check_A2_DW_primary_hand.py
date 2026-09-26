#!/usr/bin/env python3
"""Exact no-subdivision checker for A2 preparatory lemma P17."""
from fractions import Fraction as F
from math import isqrt

class I:
    __slots__=('lo','hi')
    def __init__(self,lo,hi=None):
        self.lo=F(lo); self.hi=F(lo if hi is None else hi); assert self.lo<=self.hi
    def __add__(self,o): o=iv(o); return I(self.lo+o.lo,self.hi+o.hi)
    __radd__=__add__
    def __neg__(self): return I(-self.hi,-self.lo)
    def __sub__(self,o): return self+(-iv(o))
    def __rsub__(self,o): return iv(o)-self
    def __mul__(self,o):
        o=iv(o); z=(self.lo*o.lo,self.lo*o.hi,self.hi*o.lo,self.hi*o.hi)
        return I(min(z),max(z))
    __rmul__=__mul__
    def inv(self): assert not(self.lo<=0<=self.hi); return I(1/self.hi,1/self.lo)
    def __truediv__(self,o): return self*iv(o).inv()
    def __rtruediv__(self,o): return iv(o)/self
    def abs(self):
        if self.lo<=0<=self.hi:return I(0,max(-self.lo,self.hi))
        return I(min(abs(self.lo),abs(self.hi)),max(abs(self.lo),abs(self.hi))

def iv(x): return x if isinstance(x,I) else I(x)
def sqrt_bounds(x:F,bits=120):
    scale=1<<(2*bits); k=isqrt((x.numerator*scale)//x.denominator)
    while F(k*k,scale)>x:k-=1
    while F((k+1)*(k+1),scale)<=x:k+=1
    return I(F(k,1<<bits),F(k+1,1<<bits))
def sqrtI(x:I): return I(sqrt_bounds(x.lo).lo,sqrt_bounds(x.hi).hi)

Q0=F(142559,50000); R=sqrt_bounds(Q0)
C0=sqrt_bounds(Q0-F(1,4))-F(3,2)
H=1/sqrt_bounds(F(2))
assert R.hi<F(17,10) and C0.hi<F(23,200)
assert H.lo>F(7,10)

# P17-A curvature.
assert F(473,2000) > F(12,25)**2
posA=F(17,10)*(F(9,200)/(2*F(12,25))
               +F(81,40000)/(8*F(12,25)**3))
assert posA<F(9,20)

# P17-B curvature.
P=F(37,80); q=F(11,25)
assert 2*P*F(4,5)-q*(1+F(4,5)**2)>0
assert P-q*F(4,5)>F(33,100)**2
br=q*(1+F(7,10)**2)-2*P*F(7,10)
assert br==F(81,10000)
posB=F(17,10)*q*br/(4*F(33,100)**3)
assert posB<F(6,25)
print('curvature reserves',float(F(9,20)-posA),float(F(6,25)-posB))

def frame(x):
    if x=='0': c=I(1); s=I(0)
    else: c=H; s=H
    return (-c,-s),(s,-c)
def dot(a,b): return a[0]*b[0]+a[1]*b[1]
def add(a,b): return (a[0]+b[0],a[1]+b[1])
def scale(k,a): return (k*a[0],k*a[1])
def norm(a): return sqrtI(dot(a,a))
def hc(a): return (a[0].abs()+a[1].abs())/2
def hs(a,e,f): return (dot(a,e).abs()+dot(a,f).abs())/2
def csup(g):
    assert g[0].lo>=0 and g[1].lo>=0
    return C0*(g[0]+g[1])
def osup(g,e,f): return R*norm(g)-hs(g,e,f)

def gap(w,d,source,sig,abc):
    alpha,beta,mu=map(F,abc)
    eW,fW=frame(w); eD,fD=frame(d)
    axis=eW if source=='eW' else eD
    n=scale(sig,axis)
    GC=add(scale(-alpha,eD),scale(-beta,eW))
    GW=add(scale(beta,eW),scale(-mu,n))
    GD=add(scale(alpha,eD),scale(mu,n))
    T=(alpha*(hc(eD)+F(1,2))
       +beta*(hc(eW)+F(1,2))
       +mu*(hs(n,eW,fW)+hs(n,eD,fD)))
    return T-csup(GC)-osup(GW,eW,fW)-osup(GD,eD,fD)

ROWS=[
 ('+eW','eW',1,(F(1,20),F(1,2),F(9,20))),
 ('-eW','eW',-1,(F(11,20),F(1,20),F(2,5))),
 ('+eD','eD',1,(F(1,20),F(11,20),F(2,5))),
 ('-eD','eD',-1,(F(1,2),F(1,20),F(9,20))),
]
VERTS=[('0','0'),('0','q'),('q','q')]
best=None
for name,src,sig,abc in ROWS:
    rb=None
    for w,d in VERTS:
        z=gap(w,d,src,sig,abc)
        assert z.lo>F(1,10),(name,w,d,z.lo,z.hi)
        row=(z.lo,w,d)
        if rb is None or row[0]<rb[0]: rb=row
        if best is None or row[0]<best[0]: best=(row[0],name,w,d)
    print(name,'min >',float(rb[0]),'at',rb[1:])
print('global min >',float(best[0]),best[1:])
print('A2 D-W primary-axis hand checker PASS')
