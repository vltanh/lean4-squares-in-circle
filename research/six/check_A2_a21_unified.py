#!/usr/bin/env python3
"""Exact scalar checks for the unified A2.1 central-pattern tangent lemma."""
from fractions import Fraction as F
from math import isqrt
from dataclasses import dataclass

@dataclass(frozen=True)
class QI:
    lo:F; hi:F
    def __post_init__(self): assert self.lo<=self.hi
    def __neg__(self): return QI(-self.hi,-self.lo)
    def __add__(self,o): o=q(o); return QI(self.lo+o.lo,self.hi+o.hi)
    __radd__=__add__
    def __sub__(self,o): return self+(-q(o))
    def __rsub__(self,o): return q(o)-self
    def __mul__(self,o):
        o=q(o); xs=(self.lo*o.lo,self.lo*o.hi,self.hi*o.lo,self.hi*o.hi)
        return QI(min(xs),max(xs))
    __rmul__=__mul__
    def inv(self):
        assert not (self.lo<=0<=self.hi)
        return QI(1/self.hi,1/self.lo)
    def __truediv__(self,o): return self*q(o).inv()
    def __rtruediv__(self,o): return q(o)/self

def q(x): return x if isinstance(x,QI) else QI(F(x),F(x))

def sqrt_bounds(x:F,bits=140):
    scale=1<<(2*bits)
    k=isqrt((x.numerator*scale)//x.denominator)
    lo=F(k,1<<bits)
    while lo*lo>x:
        k-=1; lo=F(k,1<<bits)
    hi=F(k+1,1<<bits)
    while hi*hi<x:
        k+=1; hi=F(k+1,1<<bits)
    return QI(lo,hi)

def candidate_bounds(bits=140):
    rt2=sqrt_bounds(F(2),bits); h=1/rt2
    A=(F(1466)+F(1940)*h)/F(267)
    B=(F(327)+F(432)*h)/F(712)
    disc=A*A-4*B
    sd=QI(sqrt_bounds(disc.lo,bits).lo,sqrt_bounds(disc.hi,bits).hi)
    s=2*B/(A+sd)
    t=(-F(20)+F(30)*h)*s+F(7,2)-F(9,2)*h
    d=F(1,2)+h-t
    return h,s,t,d

h,s,t,d=candidate_bounds()
r=(s+F(1,2))/(s+F(3,2))
k=(t+F(1,2))/(F(3,2)-s)
m=(1+r)*k
L=(s+F(1,2))+(t+F(1,2))-m*d
qq=(s+F(1,2))-(t+F(1,2))*r
c=t-s
Lp=L-c

checks={
    'c=t-s > 0': c.lo,
    'q > 0': qq.lo,
    'r > 1/3': r.lo-F(1,3),
    'L-c > 1/3': Lp.lo-F(1,3),
    '1-(L-c) > 1/3': F(1)-Lp.hi-F(1,3),
    '1+r-(L-c) > 1/3': F(1)+r.lo-Lp.hi-F(1,3),
    '1-q > 1/3': F(1)-qq.hi-F(1,3),
    '(L-c)-q > 11/50': Lp.lo-qq.hi-F(11,50),
}
for name,margin in checks.items():
    assert margin>0,(name,margin)
    print(name,'margin >',float(margin))

PAIR = F(11,50)-F(17,256)
assert PAIR == F(983,6400)
assert PAIR > F(3,20)
print('pairwise strip coercivity =',float(PAIR))
print('pairwise strip coercivity - 3/20 >',float(PAIR-F(3,20)))
print('A2.1 unified central-pattern tangent constants: PASS')
