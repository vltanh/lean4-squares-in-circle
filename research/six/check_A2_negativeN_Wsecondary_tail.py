#!/usr/bin/env python3
"""Exact fixed-checker for A2 preparatory lemma P16."""
from fractions import Fraction as F
from math import factorial,isqrt

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
    def __truediv__(self,o):
        o=iv(o); assert not(o.lo<=0<=o.hi)
        z=(self.lo/o.lo,self.lo/o.hi,self.hi/o.lo,self.hi/o.hi)
        return I(min(z),max(z))
    def __rtruediv__(self,o): return iv(o)/self
    def sq(self):
        if self.lo<=0<=self.hi:return I(0,max(self.lo*self.lo,self.hi*self.hi))
        return I(min(self.lo*self.lo,self.hi*self.hi),max(self.lo*self.lo,self.hi*self.hi))

def iv(x): return x if isinstance(x,I) else I(x)

def sqrt_bounds(x:F,bits=110):
    scale=1<<(2*bits); k=isqrt((x.numerator*scale)//x.denominator)
    while F(k*k,scale)>x:k-=1
    while F((k+1)*(k+1),scale)<=x:k+=1
    return I(F(k,1<<bits),F(k+1,1<<bits))

H=1/sqrt_bounds(F(2))
Q0=F(142559,50000)
C0=sqrt_bounds(Q0-F(1,4))-F(3,2)

def atan_inv(m,n):
    s=F(0)
    for k in range(n):
        t=F(1,(2*k+1)*m**(2*k+1)); s += t if k%2==0 else -t
    k=n; t=F(1,(2*k+1)*m**(2*k+1)); t=t if k%2==0 else -t
    return I(min(s,s+t),max(s,s+t))

PI=16*atan_inv(5,28)-4*atan_inv(239,8)

def sin_pos(x,n=15):
    assert 0<=x<=F(3,2)
    z=[(F(-1) if k&1 else F(1))*x**(2*k+1)/F(factorial(2*k+1)) for k in range(n+2)]
    a=sum(z[:n+1],F(0)); b=a+z[n+1]; return I(min(a,b),max(a,b))

def cos_pos(x,n=15):
    assert 0<=x<=F(3,2)
    z=[(F(-1) if k&1 else F(1))*x**(2*k)/F(factorial(2*k)) for k in range(n+2)]
    a=sum(z[:n+1],F(0)); b=a+z[n+1]; return I(min(a,b),max(a,b))

def sin_pt(x): return sin_pos(x) if x>=0 else -sin_pos(-x)
def sinR(x):
    x=iv(x); a=sin_pt(x.lo); b=sin_pt(x.hi); return I(a.lo,b.hi)
def cosR(x):
    x=iv(x)
    amin=F(0) if x.lo<=0<=x.hi else min(abs(x.lo),abs(x.hi))
    amax=max(abs(x.lo),abs(x.hi))
    return I(cos_pos(amax).lo,cos_pos(amin).hi)

class J:
    __slots__=('v','d','dd')
    def __init__(self,v,d=0,dd=0): self.v=iv(v); self.d=iv(d); self.dd=iv(dd)
    def __add__(self,o): o=jj(o); return J(self.v+o.v,self.d+o.d,self.dd+o.dd)
    __radd__=__add__
    def __neg__(self): return J(-self.v,-self.d,-self.dd)
    def __sub__(self,o): return self+(-jj(o))
    def __rsub__(self,o): return jj(o)-self
    def __mul__(self,o):
        o=jj(o)
        return J(self.v*o.v,self.d*o.v+self.v*o.d,
                 self.dd*o.v+2*self.d*o.d+self.v*o.dd)
    __rmul__=__mul__
    def __truediv__(self,o):
        o=jj(o); assert o.d.lo==o.d.hi==0 and o.dd.lo==o.dd.hi==0
        return J(self.v/o.v,self.d/o.v,self.dd/o.v)

def jj(x): return x if isinstance(x,J) else J(x)
def jsin(x):
    x=jj(x); s=sinR(x.v); c=cosR(x.v)
    return J(s,c*x.d,(-s)*x.d*x.d+c*x.dd)
def jcos(x):
    x=jj(x); s=sinR(x.v); c=cosR(x.v)
    return J(c,-s*x.d,-c*x.d*x.d-s*x.dd)

def add(a,b): return(a[0]+b[0],a[1]+b[1])
def sc(k,a): return(a[0]*k,a[1]*k)
def sub(a,b): return(a[0]-b[0],a[1]-b[1])
def sq(a): return a[0]*a[0]+a[1]*a[1]

DS={
'Wp':((F(12,1000),F(562,1000),F(195,1000),F(231,1000)),
      (F(29,1000),F(92,1000),F(1545,1000),F(13,1000),F(1088,1000),F(593,1000))),
'Ws':((F(12,1000),F(552,1000),F(198,1000),F(238,1000)),
      (F(0),F(92,1000),F(1531,1000),F(39,1000),F(1113,1000),F(604,1000))),
'Np':((F(12,1000),F(553,1000),F(198,1000),F(237,1000)),
      (F(0),F(93,1000),F(1525,1000),F(36,1000),F(1109,1000),F(603,1000))),
'Ns':((F(12,1000),F(562,1000),F(195,1000),F(231,1000)),
      (F(35,1000),F(91,1000),F(1543,1000),F(18,1000),F(1086,1000),F(591,1000))),
}

SS={
'Wp':((F(195,1000),F(334,1000),F(230,1000),F(241,1000)),
      (F(613,1000),F(708,1000),F(731,1000),F(205,1000),F(632,1000),F(460,1000))),
'Ws':((F(213,1000),F(100,1000),F(366,1000),F(321,1000)),
      (F(53,1000),F(1133,1000),F(288,1000),F(683,1000),F(869,1000),F(765,1000))),
'Np':((F(78,1000),F(310,1000),F(298,1000),F(314,1000)),
      (F(0),F(921,1000),F(775,1000),F(265,1000),F(824,1000),F(600,1000))),
'Ns':((F(222,1000),F(316,1000),F(224,1000),F(238,1000)),
      (F(702,1000),F(702,1000),F(604,1000),F(272,1000),F(614,1000),F(429,1000))),
}
for D in (DS,SS):
    for L,_ in D.values(): assert sum(L)==1

def bound(n,w,s,e,source,graph):
    D=DS if graph=='Ds' else SS
    (LN,LW,LS,LD),(mn,ms,mcw,m5,m7,m8)=D[source]
    cn,sn=jcos(n),jsin(n); cw,sw=jcos(w),jsin(w)
    cs,ss=jcos(s),jsin(s); ce,se=jcos(e),jsin(e)
    ny=(J(0),J(1)); ew=(-cw,-sw)
    n5={'Wp':(cw,sw),'Ws':(-sw,cw),'Np':(-sn,cn),'Ns':(cn,sn)}[source]
    n7=(-sw,cw)
    n8=((ce+se)*H,-(ce-se)*H) if graph=='Ds' else (cs,ss)
    gN=add(sc(mn,ny),sc(m5,n5))
    gW=add(add(sc(mcw,ew),sc(-m5,n5)),sc(m7,n7))
    gS=add(sc(-ms,ny),sc(m8,n8))
    gD=add(sc(-m7,n7),sc(-m8,n8))
    vN=((cn-sn)/2,(sn+cn)/2)
    vW=((-cw-sw)/2,(-sw+cw)/2)
    vS=((cs+ss)/2,(ss-cs)/2)
    vD=(se*H,-ce*H)
    # n<0 and n-w<0 throughout P16.  For Ds we retain the weaker +sin
    # expression used in P14; for Ss the exact negative-sign expressions apply.
    if graph=='Ds':
        hN=F(1,2)+(cn+sn)/2
        h5=F(1,2)+(jcos(n-w)+jsin(n-w))/2
    else:
        hN=F(1,2)+(cn-sn)/2
        h5=F(1,2)+(jcos(n-w)-jsin(n-w))/2
    hS=F(1,2)+(cs+ss)/2
    hW=F(1,2)+(cw+sw)/2
    h7=F(1,2)+jcos(e-w)*H
    h8=F(1,2)+jcos(e-s)*H
    uc=(mcw*(cw+sw)+abs(ms-mn))*C0
    out=J(F(1,2))+mn*hN+ms*hS+mcw*hW+m5*h5+m7*h7+m8*h8-uc
    for L,v,g in ((LN,vN,gN),(LW,vW,gW),(LS,vS,gS),(LD,vD,gD)):
        z=sub(sc(2*L,v),g); out=out-sq(z)/(4*L)
    return out

S=I(F(1,6),F(2,5)); E=I(-F(1,4),0)
N=I(-F(3,10),-F(1,5)); W=I(0,F(1,5))

for src in DS:
    curv=[]; deriv=[]
    for var in ('n','w','s','e'):
        z=bound(J(N,var=='n'),J(W,var=='w'),J(S,var=='s'),J(E,var=='e'),src,'Ds')
        if src=='Np' and var=='n':
            assert z.d.lo>F(1,25)
            deriv.append(z.d.lo)
        else:
            assert z.dd.hi<0,(src,var,z.dd.lo,z.dd.hi)
            curv.append(z.dd.hi)
    if deriv:
        print('Ds',src,'n derivative lower',float(min(deriv)),
              'other maxcurv',float(max(curv)))
    else:
        print('Ds',src,'maxcurv',float(max(curv)))

WSLICES=[(F(k,20),F(k+1,20)) for k in range(15)]+[(F(15,20),PI.hi/F(4))]
for src in SS:
    vals=[]
    for a,b in WSLICES:
        wb=I(a,b)
        for var in ('n','w','s','e'):
            z=bound(J(N,var=='n'),J(wb,var=='w'),J(S,var=='s'),J(E,var=='e'),src,'Ss').dd
            assert z.hi<0,(src,var,a,b,z.lo,z.hi)
            vals.append(z.hi)
    print('Ss',src,'maxcurv',float(max(vals)))

from itertools import product
best=None
for src in DS:
    for n,w,s,e in product((-F(3,10),-F(1,5)),(F(0),F(1,5)),
                           (F(1,6),F(2,5)),(-F(1,4),F(0))):
        z=bound(J(n),J(w),J(s),J(e),src,'Ds').v-Q0
        assert z.lo>0,(src,n,w,s,e,z.lo)
        row=(z.lo,'Ds',src,n,w,s,e)
        if best is None or row[0]<best[0]: best=row

WPI=I(PI.lo/F(4),PI.hi/F(4))
for src in SS:
    for n,s,e in product((-F(3,10),-F(1,5)),(F(1,6),F(2,5)),(-F(1,4),F(0))):
        for wp in (False,True):
            w=J(WPI) if wp else J(F(0))
            z=bound(J(n),w,J(s),J(e),src,'Ss').v-Q0
            assert z.lo>0,(src,n,wp,s,e,z.lo)
            row=(z.lo,'Ss',src,n,'pi/4' if wp else 0,s,e)
            if row[0]<best[0]: best=row

assert best[0]>F(1,100)
print('worst endpoint >',float(best[0]),best[1:])
print('A2 P16 negative-N W-secondary tail: PASS')
