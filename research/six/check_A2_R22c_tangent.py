#!/usr/bin/env python3
"""Exact scalar checker for the final R22-c tangent lemma."""
from fractions import Fraction as F
from math import isqrt

class I:
    __slots__=("lo","hi")
    def __init__(self,lo,hi=None):
        self.lo=F(lo); self.hi=F(lo if hi is None else hi); assert self.lo<=self.hi
    def __neg__(self): return I(-self.hi,-self.lo)
    def __add__(self,o): o=iv(o); return I(self.lo+o.lo,self.hi+o.hi)
    __radd__=__add__
    def __sub__(self,o): return self+(-iv(o))
    def __rsub__(self,o): return iv(o)-self
    def __mul__(self,o):
        o=iv(o); z=(self.lo*o.lo,self.lo*o.hi,self.hi*o.lo,self.hi*o.hi)
        return I(min(z),max(z))
    __rmul__=__mul__
    def inv(self):
        assert not(self.lo<=0<=self.hi); return I(1/self.hi,1/self.lo)
    def __truediv__(self,o): return self*iv(o).inv()
    def __rtruediv__(self,o): return iv(o)/self
def iv(x): return x if isinstance(x,I) else I(x)

def sqrt_bounds(x:F,bits=140):
    scale=1<<(2*bits); k=isqrt((x.numerator*scale)//x.denominator)
    while F(k*k,scale)>x:k-=1
    while F((k+1)*(k+1),scale)<=x:k+=1
    return I(F(k,1<<bits),F(k+1,1<<bits))

rt2=sqrt_bounds(F(2)); h=1/rt2
A0=(F(1466)+F(1940)*h)/F(267)
B0=(F(327)+F(432)*h)/F(712)
disc=A0*A0-4*B0
sd=I(sqrt_bounds(disc.lo).lo,sqrt_bounds(disc.hi).hi)
s=2*B0/(A0+sd)
t=(-F(20)+F(30)*h)*s+F(7,2)-F(9,2)*h
d=F(1,2)+h-t
r=(s+F(1,2))/(s+F(3,2))
k=(t+F(1,2))/(F(3,2)-s)
m=(1+r)*k
lam=(1-r)/2
AA=m*d+r/2-2*s
BB=s+t+F(1,2)-m*d-r/2

checks={
    "r>1/3": r.lo-F(1,3),
    "A>3r/2": AA.lo-F(3,2)*r.hi,
    "B>(3r-1)/2": BB.lo-(F(3)*r.hi-F(1))/2,
    "B<lambda": lam.lo-BB.hi,
    "d>h": d.lo-h.hi,
}
for name,z in checks.items():
    assert z>0,(name,z)
    print(name,"margin >",float(z))

strip=F(1,3)-F(17,256)-F(1,4)
assert strip>0
print("1/3-17/256-1/4 >",float(strip))
print("A2.2 R22-c tangent checks: PASS")
