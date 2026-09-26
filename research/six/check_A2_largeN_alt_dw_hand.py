#!/usr/bin/env python3
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
    def __truediv__(self,o):
        o=iv(o); assert not(o.lo<=0<=o.hi)
        vals=(self.lo/o.lo,self.lo/o.hi,self.hi/o.lo,self.hi/o.hi)
        return I(min(vals),max(vals))
    def __rtruediv__(self,o): return iv(o)/self
    def sq(self):
        if self.lo<=0<=self.hi:return I(0,max(self.lo*self.lo,self.hi*self.hi))
        return I(min(self.lo*self.lo,self.hi*self.hi),max(self.lo*self.lo,self.hi*self.hi))

def iv(x):return x if isinstance(x,I) else I(x)

def sqrt_bounds(x:F,bits=100):
    scale=1<<(2*bits);k=isqrt((x.numerator*scale)//x.denominator)
    while F(k*k,scale)>x:k-=1
    while F((k+1)*(k+1),scale)<=x:k+=1
    return I(F(k,1<<bits),F(k+1,1<<bits))
RT2=sqrt_bounds(F(2))

def atan_inv(m,n):
    s=F(0)
    for k in range(n):
        t=F(1,(2*k+1)*m**(2*k+1));s += t if k%2==0 else -t
    k=n;t=F(1,(2*k+1)*m**(2*k+1));t=t if k%2==0 else -t
    return I(min(s,s+t),max(s,s+t))
PI=16*atan_inv(5,26)-4*atan_inv(239,8)
assert PI.lo > 3

def sin_pos(x,n=14):
    assert 0<=x<=F(3,2)
    ts=[(F(-1) if k&1 else F(1))*x**(2*k+1)/F(factorial(2*k+1)) for k in range(n+2)]
    a=sum(ts[:n+1],F(0));b=a+ts[n+1];return I(min(a,b),max(a,b))
def cos_pos(x,n=14):
    assert 0<=x<=F(3,2)
    ts=[(F(-1) if k&1 else F(1))*x**(2*k)/F(factorial(2*k)) for k in range(n+2)]
    a=sum(ts[:n+1],F(0));b=a+ts[n+1];return I(min(a,b),max(a,b))
def sin_pt(x): return sin_pos(x) if x>=0 else -sin_pos(-x)
def sinR(x:I):
    a=sin_pt(x.lo);b=sin_pt(x.hi);return I(a.lo,b.hi)
def cosR(x:I):
    amin=F(0) if x.lo<=0<=x.hi else min(abs(x.lo),abs(x.hi))
    amax=max(abs(x.lo),abs(x.hi))
    return I(cos_pos(amax).lo,cos_pos(amin).hi)

N=I(F(1,5),F(2,5)); W=I(-F(1,5),F(1,5))
S=I(F(1,6),F(1,2)); E=I(-F(1,6),F(0))
NW=N-W; EW=E-W; ES=E-S
P4=PI/F(4)
NP=N+P4; NWP=NW+P4; MWNP=(-NW)+P4; ENP=E-N+P4
SP=S+P4; MESP=(-E)+S+P4; ESP=E-S+P4

src={}
src['Wp']=[
 -(F(949,1000)*RT2*sinR(NP)+F(277,1000)*cosR(NW)),
 (F(122498818,261892000)*sinR(W)+F(46935711,261892000)*RT2*sinR(EW)-F(110985165,261892000)*RT2*cosR(EW)-F(72544084,261892000)*cosR(NW)),
 -(F(1789814,1426000)*sinR(S)+F(240219,1426000)*RT2*sinR(ES)+F(1353274,1426000)*cosR(S)+F(1292607,1426000)*RT2*cosR(ES)),
 F(9,21436000)*RT2*(-F(401226)*sinR(ES)+F(426857)*sinR(EW)-F(2158978)*cosR(ES)-F(1009355)*cosR(EW)),
]
src['Ws']=[
 -RT2*(F(1898)*sinR(NP)+F(277)*sinR(NWP)+F(277)*cosR(MWNP))/F(2000),
 (F(46935711,261892000)*RT2*sinR(EW)-F(36272042,261892000)*RT2*sinR(NWP)+F(122498818,261892000)*cosR(W)-F(204856587,261892000)*RT2*cosR(EW)-F(36272042,261892000)*RT2*cosR(MWNP)),
 src['Wp'][2],
 F(9,21436000)*RT2*(-F(401226)*sinR(ES)+F(426857)*sinR(EW)-F(2158978)*cosR(ES)-F(1863069)*cosR(EW)),
]
src['Np']=[
 (-F(62133877)*sinR(N)-F(62133877)*RT2*sinR(NP)-F(18136021)*RT2*sinR(NWP)-F(884468)*cosR(N)-F(46935711)*cosR(ENP)+F(18136021)*RT2*cosR(MWNP))/F(130946000),
 RT2*(-F(277)*sinR(NWP)-F(1206)*cosR(EW)+F(277)*cosR(MWNP))/F(2000),
 -(F(1113177)*sinR(S)+F(676637)*RT2*sinR(SP)+F(1052388)*sinR(MESP)+F(1532826)*sinR(ESP)+F(676637)*cosR(S))/F(1426000),
 -F(9,10718000)*(F(878876)*sinR(MESP)+F(1280102)*sinR(ESP)+F(718106)*RT2*cosR(EW)+F(426857)*cosR(ENP)),
]
src['Ns']=[
 (-F(884468)*sinR(N)-F(62133877)*RT2*sinR(NP)+F(46935711)*sinR(ENP)-F(62133877)*cosR(N)-F(36272042)*cosR(NW))/F(130946000),
 -(F(603,1000)*RT2*cosR(EW)+F(277,1000)*cosR(NW)),
 src['Np'][2],
 F(9,10718000)*(-F(878876)*sinR(MESP)+F(426857)*sinR(ENP)-F(1280102)*sinR(ESP)-F(718106)*RT2*cosR(EW)),
]
CURV_TARGET={
    'Wp':(-F(4,3),-F(3,5),-F(19,10),-F(4,3)),
    'Ws':(-F(4,3),-F(3,4),-F(19,10),-F(9,5)),
    'Np':(-F(9,10),-F(7,10),-F(9,5),-F(9,5)),
    'Ns':(-F(1),-F(1),-F(9,5),-F(13,10)),
}
for name,vals in src.items():
    for z,target in zip(vals,CURV_TARGET[name]):
        assert z.hi < target,(name,z.lo,z.hi,target)

Q0=F(142559,50000); H=I(F(70710678,10**8),F(70710679,10**8))
LN=F(281,1000);LW=F(233,1000);LS=F(279,1000);LD=F(207,1000)
MU1=F(949,1000);MU4=MU1;MU5=F(277,1000);MU7=F(603,1000);MU8=F(738,1000)
def cspt(x): return cosR(I(x)),sinR(I(x))
def vadd(a,b):return a[0]+b[0],a[1]+b[1]
def vsub(a,b):return a[0]-b[0],a[1]-b[1]
def vscale(c,a):return c*a[0],c*a[1]
def vsq(a):return a[0].sq()+a[1].sq()
def lower(n,w,s,e,source):
    cN,sN=cspt(n);cW,sW=cspt(w);cS,sS=cspt(s);cD,sD=cspt(e)
    n1=(I(0),I(1))
    axes={'Wp':(cW,sW),'Ws':(-sW,cW),'Np':(-sN,cN),'Ns':(cN,sN)}
    n5=axes[source]
    n7=(-H*(cD+sD),H*(cD-sD));n8=(cS,sS)
    gN=vadd(vscale(MU1,n1),vscale(MU5,n5))
    gW=vadd(vscale(-MU5,n5),vscale(MU7,n7))
    gS=vadd(vscale(-MU4,n1),vscale(MU8,n8))
    gD=vadd(vscale(-MU7,n7),vscale(-MU8,n8))
    mN=(F(1,2)*(cN-sN),F(1,2)*(sN+cN))
    mW=(F(1,2)*(-cW-sW),F(1,2)*(-sW+cW))
    mS=(F(1,2)*(cS+sS),F(1,2)*(sS-cS));mD=(H*sD,-H*cD)
    h1=I(F(1,2))+F(1,2)*(cN+sN);h4=I(F(1,2))+F(1,2)*(cS+sS)
    c5,s5=cspt(n-w);h5=I(F(1,2))+F(1,2)*(c5+s5)
    c7,_=cspt(e-w);h7=I(F(1,2))+H*c7
    c8,_=cspt(e-s);h8=I(F(1,2))+H*c8
    out=I(F(1,2))+MU1*h1+MU4*h4+MU5*h5+MU7*h7+MU8*h8
    for lam,m,g in ((LN,mN,gN),(LW,mW,gW),(LS,mS,gS),(LD,mD,gD)):
        z=vsub(vscale(2*lam,m),g); out=out-F(1,4)/lam*vsq(z)
    return out

verts=[]
for n in (F(1,5),F(2,5)):
 for w in (-F(1,5),F(1,5)):
  for s in (F(1,6),F(1,2)):
   for e in (-F(1,6),F(0)):
    verts.append((n,w,s,e))
bestall=None
for source in ('Wp','Ws','Np','Ns'):
    best=None
    for v in verts:
        z=lower(*v,source)-Q0
        assert z.lo>0,(source,v,z.lo,z.hi)
        row=(z.lo,v)
        if best is None or row[0]<best[0]:best=row
    print(source,'endpoint min >',float(best[0]),'at',best[1])
    if bestall is None or best[0]<bestall[0]:bestall=(best[0],source,best[1])
assert bestall[0] > F(1,25)
print('worst >',float(bestall[0]),bestall[1:])
print('large-N alternate-DW hand checker PASS')
