#!/usr/bin/env python3
"""Exact scalar checker for the A2.2 small-s D-primary hand lemma."""
from fractions import Fraction as F
from math import factorial,isqrt

class I:
    __slots__=('lo','hi')
    def __init__(self,lo,hi=None):
        self.lo=F(lo); self.hi=F(lo if hi is None else hi); assert self.lo<=self.hi
    def __add__(self,o):o=iv(o);return I(self.lo+o.lo,self.hi+o.hi)
    __radd__=__add__
    def __neg__(self):return I(-self.hi,-self.lo)
    def __sub__(self,o):return self+(-iv(o))
    def __rsub__(self,o):return iv(o)-self
    def __mul__(self,o):
        o=iv(o);z=(self.lo*o.lo,self.lo*o.hi,self.hi*o.lo,self.hi*o.hi);return I(min(z),max(z))
    __rmul__=__mul__
    def inv(self): assert not(self.lo<=0<=self.hi); return I(1/self.hi,1/self.lo)
    def __truediv__(self,o):return self*iv(o).inv()
    def __rtruediv__(self,o):return iv(o)/self

def iv(x):return x if isinstance(x,I) else I(x)

def sqrt_bounds(x:F,bits=120):
    scale=1<<(2*bits);k=isqrt((x.numerator*scale)//x.denominator)
    while F(k*k,scale)>x:k-=1
    while F((k+1)*(k+1),scale)<=x:k+=1
    return I(F(k,1<<bits),F(k+1,1<<bits))
def sqrtI(x:I):return I(sqrt_bounds(x.lo).lo,sqrt_bounds(x.hi).hi)

def atan_inv(m,n):
    s=F(0)
    for k in range(n):
        z=F(1,(2*k+1)*m**(2*k+1));s += z if k%2==0 else -z
    k=n;z=F(1,(2*k+1)*m**(2*k+1));z=z if k%2==0 else -z
    return I(min(s,s+z),max(s,s+z))
PI=16*atan_inv(5,28)-4*atan_inv(239,8)
assert PI.lo>3

def sin_pos(x,n=14):
    assert 0<=x<=F(3,2)
    z=[(F(-1) if k&1 else F(1))*x**(2*k+1)/F(factorial(2*k+1)) for k in range(n+2)]
    a=sum(z[:n+1],F(0));b=a+z[n+1];return I(min(a,b),max(a,b))
def cos_pos(x,n=14):
    assert 0<=x<=F(3,2)
    z=[(F(-1) if k&1 else F(1))*x**(2*k)/F(factorial(2*k)) for k in range(n+2)]
    a=sum(z[:n+1],F(0));b=a+z[n+1];return I(min(a,b),max(a,b))
def sin_pt(x):return sin_pos(x) if x>=0 else -sin_pos(-x)
def sinI(x:I):
    a=sin_pt(x.lo);b=sin_pt(x.hi);return I(a.lo,b.hi)
def cosI(x:I):
    amin=F(0) if x.lo<=0<=x.hi else min(abs(x.lo),abs(x.hi))
    amax=max(abs(x.lo),abs(x.hi))
    return I(cos_pos(amax).lo,cos_pos(amin).hi)

Q0=F(142559,50000)
R=sqrt_bounds(Q0)
RHO=sqrt_bounds(Q0-F(1,4))-F(1,2)
C0=RHO-F(1)
assert R.hi<F(17,10)
H=1/sqrt_bounds(F(2))
assert H.hi<F(71,100)

b=F(31,50);m=F(19,50)
P=b*b+m*m
Q=2*b*m
D0=PI/F(4)-F(1,4)

assert D0.lo>PI.hi/F(6)
assert PI.lo/F(4)+F(2,5)<PI.lo/F(2)
assert cosI(PI/F(4)+F(2,5)).lo>F(3,8)
assert P-Q*F(71,100)>F(11,25)**2

NMAX=F(5,4)*Q-P
assert NMAX==F(301,5000)
FPP=F(17,10)*Q*NMAX/(4*F(11,25)**3)
assert FPP < m*F(3,8)
print("d-curvature reserve >",float(m*F(3,8)-FPP))

assert b*F(9,10)-m>0
assert m*F(7,10)-b*F(1,6)>0

C=(b+m)/F(2)-C0*b-RHO*m

def Phi(d:I,s:I):
    z=P-Q*sinI(d)
    G=b*cosI(s) if s.lo>=0 else b*(cosI(s)-sinI(s))
    return C-R*sqrtI(z)+G+m*cosI(d-s)

vals=[]
for dname,d in [('d0',D0),('pi/4',PI/F(4))]:
    for s in (F(-2,5),F(0),F(1,6)):
        z=Phi(d,iv(s))
        assert z.lo>F(1,25),(dname,s,z.lo,z.hi)
        vals.append(z.lo)
        print(dname,"s=",s,"margin >",float(z.lo))
print("worst endpoint >",float(min(vals)))
print("A2.2 R22-c D-primary hand checker: PASS")
