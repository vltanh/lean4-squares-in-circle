#!/usr/bin/env python3
"""Scalar arithmetic for the hand proof of the second alternate-D branch."""
from fractions import Fraction as F
from math import factorial

class I:
    def __init__(self, lo, hi=None):
        self.lo=F(lo); self.hi=F(lo if hi is None else hi); assert self.lo<=self.hi
    def __add__(self,o): o=iv(o); return I(self.lo+o.lo,self.hi+o.hi)
    __radd__=__add__
    def __neg__(self): return I(-self.hi,-self.lo)
    def __sub__(self,o): return self+(-iv(o))
    def __rsub__(self,o): return iv(o)-self
    def __mul__(self,o):
        o=iv(o); xs=(self.lo*o.lo,self.lo*o.hi,self.hi*o.lo,self.hi*o.hi)
        return I(min(xs),max(xs))
    __rmul__=__mul__
def iv(x): return x if isinstance(x,I) else I(x)
def sinb(x,n=9):
    x=F(x); assert 0<=x<=F(3,4)
    ts=[F((-1)**k)*x**(2*k+1)/F(factorial(2*k+1)) for k in range(n+2)]
    s=sum(ts[:n+1],F(0)); t=s+ts[n+1]; return I(min(s,t),max(s,t))
def cosb(x,n=9):
    x=F(x); assert 0<=x<=F(3,4)
    ts=[F((-1)**k)*x**(2*k)/F(factorial(2*k)) for k in range(n+2)]
    s=sum(ts[:n+1],F(0)); t=s+ts[n+1]; return I(min(s,t),max(s,t))
def pos(name,x): assert x.lo>0,(name,x.lo,x.hi); print(name,">",float(x.lo))
def neg(name,x): assert x.hi<0,(name,x.lo,x.hi); print(name,"<",float(x.hi))

H=I(F(70710678,10**8),F(70710679,10**8))
a=F(1,6); c=F(1,5); d=a+c; half=F(1,2)
r=F(3,50); u=F(1,25); j=F(17,160); const=F(1071,800); Q0=F(142559,50000)
b=F(43,600)*H
A=F(17,5)*H
C=F(2107,600)*H

sa,ca=sinb(a),cosb(a); sc,cc=sinb(c),cosb(c)
sd,cd=sinb(d),cosb(d); sh,ch=sinb(half),cosb(half)
s23,c23=sinb(F(2,3)),cosb(F(2,3)); s2c,c2c=sinb(2*c),cosb(2*c)
s13,c13=sinb(F(1,3)),cosb(F(1,3))

neg("e_second_derivative_upper", b*sd+j-A*c23-C*cd)
pos("e_endpoint_factor_w_nonnegative", -b+j*H+A*sa)
neg("w_nonnegative_derivative_upper", r*sc+b-C*sa)

Bmin=b*sd+r*ch-j*H*(ca+sa)+A*cosb(a+half)+C*cd+u*c2c-const
pos("base_margin",Bmin-Q0)
pos("w_negative_concavity_value_lower",C*cd-b*sd-r)

def base(ncos,wcos,nmwcos,esin,epicos,escos,ewcos):
    return -b*esin+r*ncos+r*ch-r*wcos-j*epicos+A*escos+C*ewcos+u*nmwcos-const

corners=[
    base(cc,1,cc,-sa,H*(ca+sa),cosb(a+half),ca),
    base(cc,cc,c2c,sinb(c-a),H*(ca+sa),cosb(a+half),cosb(c-a)),
    base(cc,1,cc,sa,H*(ca-sa),cosb(half-a),ca),
    base(cc,cc,c2c,sd,H*(ca-sa),c13,cd),
]
for i,x in enumerate(corners): pos(f"w_negative_corner_{i}_above_hard",x-Bmin)

Lwp=F(1,25)+r*(cc-sc)-2*b
Lnp=F(1,25)+r*cc-2*b*(sd+cd)
Lns=-r+r*cc-2*b*sd

pos("Wp_after_comparison",Bmin-Q0+Lwp)
pos("Np_after_comparison",Bmin-Q0+Lnp)
pos("Ns_after_comparison",Bmin-Q0+Lns)
print("second hand scalar checks: PASS")
