#!/usr/bin/env python3
"""Exact no-subdivision checker for A2 preparatory lemma P9."""
from fractions import Fraction as F
from dataclasses import dataclass
from math import factorial,isqrt

@dataclass(frozen=True)
class I:
    lo:F; hi:F
    def __post_init__(self): assert self.lo<=self.hi
    def __neg__(self): return I(-self.hi,-self.lo)
    def __add__(self,o): o=iv(o); return I(self.lo+o.lo,self.hi+o.hi)
    __radd__=__add__
    def __sub__(self,o): return self+(-iv(o))
    def __rsub__(self,o): return iv(o)-self
    def __mul__(self,o):
        o=iv(o); z=(self.lo*o.lo,self.lo*o.hi,self.hi*o.lo,self.hi*o.hi)
        return I(min(z),max(z))
    __rmul__=__mul__
    def inv(self): assert not(self.lo<=0<=self.hi); return I(1/self.hi,1/self.lo)
    def __truediv__(self,o): return self*iv(o).inv()
    def __rtruediv__(self,o): return iv(o)/self
def iv(x): return x if isinstance(x,I) else I(F(x),F(x))

def sqrt_bounds(x:F,bits=120):
    scale=1<<(2*bits); k=isqrt((x.numerator*scale)//x.denominator)
    while F(k*k,scale)>x:k-=1
    while F((k+1)*(k+1),scale)<=x:k+=1
    return I(F(k,1<<bits),F(k+1,1<<bits))
def sqrtI(x:I): return I(sqrt_bounds(x.lo).lo,sqrt_bounds(x.hi).hi)

def atan_inv(m,n):
    s=F(0)
    for k in range(n):
        z=F(1,(2*k+1)*m**(2*k+1)); s += z if k%2==0 else -z
    k=n; z=F(1,(2*k+1)*m**(2*k+1)); z=z if k%2==0 else -z
    return I(min(s,s+z),max(s,s+z))
PI=16*atan_inv(5,24)-4*atan_inv(239,8)

def sin_point(x:F):
    p=F(0)
    for k in range(10):
        p += (F(-1) if k%2 else F(1))*x**(2*k+1)/F(factorial(2*k+1))
    rem=abs(x)**20/F(factorial(20))
    return I(p-rem,p+rem)
def cos_point(x:F):
    p=F(0)
    for k in range(11):
        p += (F(-1) if k%2 else F(1))*x**(2*k)/F(factorial(2*k))
    rem=abs(x)**21/F(factorial(21))
    return I(p-rem,p+rem)
def sinI(x:I):
    a=sin_point(x.lo); b=sin_point(x.hi); return I(a.lo,b.hi)
def cosI(x:I):
    amin=F(0) if x.lo<=0<=x.hi else min(abs(x.lo),abs(x.hi))
    amax=max(abs(x.lo),abs(x.hi))
    return I(cos_point(amax).lo,cos_point(amin).hi)

Q0=F(142559,50000); R=sqrt_bounds(Q0); H=1/sqrt_bounds(F(2))
C0=sqrt_bounds(Q0-F(1,4))-F(3,2); KAP=F(1,2)-C0
assert R.hi<F(17,10)
assert H.lo>F(7,10) and H.hi<F(71,100)
assert C0.hi<F(23,200)
assert cos_point(F(11,15)).lo>F(7,10)
assert sin_point(F(1,6)).lo>F(4,25)
assert sin_point(F(1,2)).hi<F(1,2)
assert cos_point(F(1,2)).lo>F(7,8)
assert cos_point(F(1,3)).lo + sin_point(F(1,3)).lo > F(6,5)
assert PI.hi/F(8)+F(5,12)<F(13,16)
assert sin_point(F(13,16)).hi<F(3,4)

P=F(5,32); Q=F(117,800); YLO=F(36,125); BMAX=F(49997,500000)
assert P-Q/F(2)>YLO*YLO
pos=F(17,10)*Q*BMAX/(4*YLO**3)
neg=F(13,40)*F(7,8)
assert pos<neg
print('J curvature reserve >',float(neg-pos))

def Fw_ds(w):
    c,s=cosI(w),sinI(w)
    return KAP*(c+s) if w.lo>=0 else KAP*c-F(1,2)*s
def Fw_ss(w):
    c,s=cosI(w),sinI(w)
    return KAP*(c+s) if w.lo>=0 else KAP*c-(F(1,2)+C0)*s
def G(z):
    return 2*H*cosI(z)-2*R*sinI(3*PI/F(8)+z/F(2))
def Hds(q):
    if q.lo>=-PI.lo/F(4): return 2*H*cosI(q)
    if q.hi<=-PI.hi/F(4): return -2*H*sinI(q)
    return I(F(1),F(1))
def Hss(q):
    if q.lo>=-PI.lo/F(4):
        return H*(cosI(q)-sinI(q))-2*R*sinI(PI/F(8)-q/F(2))
    if q.hi<=-PI.hi/F(4):
        return -2*H*sinI(q)-2*R*sinI(PI/F(8)-q/F(2))
    return I(F(1),F(1))-2*R*H
def Jss(s):
    a=F(13,40); x=F(9,40); si=sinI(s)
    return a*cosI(s)-R*sqrtI(a*a+x*x-2*a*x*si)
def Phi_ds(w,s,e):
    return F(1,3)*(F(2)-R+Fw_ds(w)+G(e-w)+Hds(e-s))
def Phi_ss(w,s,e):
    a=F(13,40); x=F(9,40)
    const=a/F(2)+3*x-C0*a
    return const+x*Fw_ss(w)+x*G(e-w)+x*Hss(e-s)+Jss(s)

W=[iv(-F(2,5)),iv(0),iv(F(2,5))]
SE=[
    (iv(F(1,6)),iv(-F(1,3))),
    (iv(F(1,6)),iv(-F(1,6))),
    (iv(F(1,2)),iv(-F(1,3))),
    (iv(F(1,2)),iv(-F(1,6))),
    (PI/F(4)-F(1,3),iv(-F(1,3))),
    (iv(F(1,2)),F(1,2)-PI/F(4)),
]
for name,fun,target in [('D-secondary',Phi_ds,F(1,50)),
                        ('S-secondary',Phi_ss,F(7,1000))]:
    best=None
    for w in W:
        for s,e in SE:
            z=fun(w,s,e)
            assert z.lo>target,(name,w,s,e,z)
            if best is None or z.lo<best[0]:best=(z.lo,w,s,e)
    print(name,'min endpoint margin >',float(best[0]),'target',float(target))
print('A2 negative-diagonal tail hand checks: PASS')
