#!/usr/bin/env python3
"""No-subdivision exact arithmetic for the A1 hand proof.

This script checks only fixed scalar inequalities and the seven chamber
vertices.  There is no interval subdivision or search tree.
"""
from fractions import Fraction as F
from dataclasses import dataclass
from math import factorial, isqrt

Q0 = F(142559, 50000)

@dataclass(frozen=True)
class I:
    lo: F
    hi: F
    def __post_init__(self): assert self.lo <= self.hi
    def __add__(self,o): o=iv(o); return I(self.lo+o.lo,self.hi+o.hi)
    __radd__=__add__
    def __neg__(self): return I(-self.hi,-self.lo)
    def __sub__(self,o): return self+(-iv(o))
    def __rsub__(self,o): return iv(o)-self
    def __mul__(self,o):
        o=iv(o); z=(self.lo*o.lo,self.lo*o.hi,self.hi*o.lo,self.hi*o.hi)
        return I(min(z),max(z))
    __rmul__=__mul__
    def sq(self):
        if self.lo <= 0 <= self.hi:
            return I(F(0), max(self.lo*self.lo,self.hi*self.hi))
        z=(self.lo*self.lo,self.hi*self.hi)
        return I(min(z),max(z))
    def abs(self):
        if self.lo <= 0 <= self.hi:
            return I(F(0),max(-self.lo,self.hi))
        return I(min(abs(self.lo),abs(self.hi)),max(abs(self.lo),abs(self.hi)))

def iv(x): return x if isinstance(x,I) else I(F(x),F(x))

def sqrt_bounds(x:F,bits=90):
    assert x >= 0
    if x == 0: return I(F(0),F(0))
    scale=1 << (2*bits)
    k=isqrt((x.numerator*scale)//x.denominator)
    while F(k*k,scale) > x: k-=1
    while F((k+1)*(k+1),scale) <= x: k+=1
    return I(F(k,1<<bits),F(k+1,1<<bits))

def sin_pos(x,n=12):
    x=F(x); assert 0 <= x <= F(16,15)
    ts=[(F(-1) if k&1 else F(1))*x**(2*k+1)/F(factorial(2*k+1))
        for k in range(n+2)]
    a=sum(ts[:n+1],F(0)); b=a+ts[n+1]
    return I(min(a,b),max(a,b))

def cos_pos(x,n=12):
    x=F(x); assert 0 <= x <= F(16,15)
    ts=[(F(-1) if k&1 else F(1))*x**(2*k)/F(factorial(2*k))
        for k in range(n+2)]
    a=sum(ts[:n+1],F(0)); b=a+ts[n+1]
    return I(min(a,b),max(a,b))

def sin_point(x): return sin_pos(x) if x>=0 else -sin_pos(-x)

def sinI(x:I):
    a=sin_point(x.lo); b=sin_point(x.hi)
    return I(a.lo,b.hi)

def cosI(x:I):
    amin=F(0) if x.lo<=0<=x.hi else min(abs(x.lo),abs(x.hi))
    amax=max(abs(x.lo),abs(x.hi))
    return I(cos_pos(amax).lo,cos_pos(amin).hi)

def abs_lower(x:I):
    return F(0) if x.lo<=0<=x.hi else min(abs(x.lo),abs(x.hi))

def dot(a,b): return a[0]*b[0]+a[1]*b[1]
def add(a,b): return (a[0]+b[0],a[1]+b[1])
def scale(k,a): return (k*a[0],k*a[1])

def norm_hi(a): return sqrt_bounds((a[0].sq()+a[1].sq()).hi).hi

def frame(t):
    c=cosI(t); s=sinI(t)
    return ((-c,-s),(s,-c))

R=sqrt_bounds(Q0)
RH=sqrt_bounds(Q0-F(1,4))
CMAX=RH-F(3,2)

assert R.hi < F(17,10)
assert CMAX.hi < F(1,8)
assert CMAX.lo > F(1,10)
assert cos_pos(F(2,3)).lo > F(3,4)
assert sin_pos(F(2,3)).hi < F(5,8)
assert cos_pos(F(2,5)).lo > F(9,10)
assert sin_pos(F(2,5)).hi < F(39,100)
assert cos_pos(F(16,15)).lo > F(12,25)
assert sin_pos(F(16,15)).hi < F(9,10)

s23=sin_pos(F(2,3)); c23=cos_pos(F(2,3))
s25=sin_pos(F(2,5)); c25=cos_pos(F(2,5))
amin_lo=F(1,2)+(F(2)-RH.hi)*c23.lo+F(1,2)*s23.lo
rho_hi=RH.hi-F(1,2)
assert amin_lo>rho_hi
cap_25_hi=R.hi-c25.lo-s25.lo
side_depth_lo=F(2)-RH.hi
assert cap_25_hi<side_depth_lo

assert F(1,4)*F(12,25) > F(3,10)*F(39,100)
assert F(3,10)*F(9,10) > F(1,4)*F(9,10)
assert F(56,81) > F(16,25)
assert F(3,4) > F(25,36)
assert F(19,100) > F(169,900)
assert 4*F(53,200)**2-3*F(9,40)**2 > 0
assert 4*F(13,100)**2-3*F(3,25)**2 > 0
assert F(3,5)*F(9,10)-F(3,10) > 0
assert F(1,2)*F(9,10)-F(3,10) > 0

assert F(29,200) > F(19,50)**2
wep_norm = F(17,10)*F(12,625)/(4*F(19,50)**3)
assert wep_norm < F(3,20) < F(27,160)
assert F(91833206) > F(108135819)*F(25,64) + F(91936620)*F(125,512)
assert F(41365283) > (F(34496862)*F(2,5)
                      + F(125136099)*F(4,25)
                      + F(69969420)*F(8,125))
assert F(1739061) > 0
assert F(23,80) > F(53,100)**2
dep_g = F(17,10)*F(363,4000)/(4*F(53,100)**3)
assert dep_g < F(13,50) < F(27,100)
assert F(7,50) > F(37,100)**2
dep_h = F(17,10)*F(5049,1000000)/(4*F(37,100)**3)
assert dep_h < F(1,20) < F(1,5)
dem_h0 = F(17,10)*F(3,50)/F(1,2)
assert dem_h0 < F(21,100) < F(3,10)
P=F(53,200); q=F(9,40)
assert P+q*F(1,2) > F(307,500)**2
assert P+q*F(9,10) > F(17,25)**2
assert P > F(257,500)**2
assert P-q*F(1,2) > F(39,100)**2
num_half=q*q*F(5,4)+P*q
np_half=F(17,10)*num_half/(4*F(307,500)**3)
assert np_half < F(23,100) < F(1,4)
num_9=q*q*(1+F(81,100))+2*P*q*F(9,10)
np_9=F(17,10)*num_9/(4*F(17,25)**3)
assert np_9 < F(27,100) < F(1,3)
nm_0=F(17,10)*(q*q)/(4*F(257,500)**3)
assert nm_0 < F(4,25) < F(1,5)
num_half_m=q*q*F(5,4)-P*q
nm_half=F(17,10)*num_half_m/(4*F(39,100)**3)
assert nm_half < F(3,100) < F(3,25)

WEIGHTS={
    ('We',+1):(F(1,10),F(3,5),F(3,10)),
    ('We',-1):(F(3,5),F(1,10),F(3,10)),
    ('Wf',+1):(F(3,10),F(9,20),F(1,4)),
    ('Wf',-1):(F(3,10),F(9,20),F(1,4)),
    ('De',+1):(F(3,10),F(9,20),F(1,4)),
    ('De',-1):(F(1,2),F(1,5),F(3,10)),
    ('Df',+1):(F(3,10),F(9,20),F(1,4)),
    ('Df',-1):(F(3,10),F(9,20),F(1,4)),
}
VERTICES=[
    (F(-2,3),F(-2,5)),
    (F(-2,5),F(-2,5)),
    (F(-2,3),F(0)),
    (F(0),F(0)),
    (F(-2,3),F(2,5)),
    (F(0),F(2,5)),
    (F(2,5),F(2,5)),
]

def support_upper(G,ang,drop_f=False):
    e,f=frame(ang)
    gain=abs_lower(dot(G,e))
    if not drop_f:
        gain += abs_lower(dot(G,f))
    return R.hi*norm_hi(G)-F(1,2)*gain

def central_upper(G):
    return CMAX.hi*(max(F(0),G[0].hi)+max(F(0),G[1].hi))

def axis_vec(which,t,u):
    eW,fW=frame(t); eD,fD=frame(u)
    return {'We':eW,'Wf':fW,'De':eD,'Df':fD}[which]

def gap_lower_point(t0,u0,which,sgn):
    a,b,m=WEIGHTS[(which,sgn)]
    t=I(t0,t0); u=I(u0,u0)
    ct,st=cosI(t),sinI(t); cu,su=cosI(u),sinI(u)
    HD=I(F(1,2),F(1,2))+F(1,2)*(cu+su.abs())
    HW=I(F(1,2),F(1,2))+F(1,2)*(ct+st.abs())
    d=u-t; cd,sd=cosI(d),sinI(d)
    HP=I(F(1,2),F(1,2))+F(1,2)*(cd+sd)
    lhs=(a*HD+b*HW+m*HP).lo

    nD=(I(-1,-1),I(0,0))
    eW,_=frame(t)
    n=scale(F(sgn),axis_vec(which,t,u))
    GC=add(scale(-a,nD),scale(-b,eW))
    GW=add(scale(b,eW),scale(-m,n))
    GD=add(scale(a,nD),scale(m,n))
    drop=(which in ('We','De'))
    rhs=central_upper(GC)+support_upper(GW,t)+support_upper(GD,u,drop_f=drop)
    return lhs-rhs

TARGET={
    ('We',+1):F(2,25), ('We',-1):F(1,50),
    ('Wf',+1):F(1,500), ('Wf',-1):F(1,100),
    ('De',+1):F(1,50), ('De',-1):F(2,25),
    ('Df',+1):F(1,100), ('Df',-1):F(1,100),
}

mins=[]
for case in WEIGHTS:
    vals=[]
    for v in VERTICES:
        g=gap_lower_point(v[0],v[1],*case)
        assert g>0,(case,v,g)
        vals.append((g,v))
    gm,vm=min(vals,key=lambda z:z[0])
    assert gm > TARGET[case], (case,gm,TARGET[case])
    mins.append((gm,case,vm))
    print(case,'min endpoint margin >',float(gm),'at',vm)

gm,case,vm=min(mins,key=lambda z:z[0])
print('worst endpoint margin >',float(gm),'case',case,'at',vm)
print('A1 hand checker: PASS (no subdivision)')
