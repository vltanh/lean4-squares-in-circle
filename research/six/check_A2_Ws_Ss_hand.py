#!/usr/bin/env python3
"""No-subdivision checker for A2 P11: W-secondary / S-secondary tail."""
from fractions import Fraction as F
from math import factorial,isqrt

class I:
    __slots__=('lo','hi')
    def __init__(self,lo,hi=None): self.lo=F(lo); self.hi=F(lo if hi is None else hi); assert self.lo<=self.hi
    def __add__(self,o):o=iv(o);return I(self.lo+o.lo,self.hi+o.hi)
    __radd__=__add__
    def __neg__(self):return I(-self.hi,-self.lo)
    def __sub__(self,o):return self+(-iv(o))
    def __rsub__(self,o):return iv(o)-self
    def __mul__(self,o):
        o=iv(o); z=(self.lo*o.lo,self.lo*o.hi,self.hi*o.lo,self.hi*o.hi); return I(min(z),max(z))
    __rmul__=__mul__
    def __truediv__(self,o):
        o=iv(o); assert not(o.lo<=0<=o.hi)
        z=(self.lo/o.lo,self.lo/o.hi,self.hi/o.lo,self.hi/o.hi); return I(min(z),max(z))
    def __rtruediv__(self,o):return iv(o)/self
    def sq(self):
        if self.lo<=0<=self.hi:return I(0,max(self.lo*self.lo,self.hi*self.hi))
        return I(min(self.lo*self.lo,self.hi*self.hi),max(self.lo*self.lo,self.hi*self.hi))
def iv(x):return x if isinstance(x,I) else I(x)

def sqrt_bounds(x:F,bits=110):
    scale=1<<(2*bits);k=isqrt((x.numerator*scale)//x.denominator)
    while F(k*k,scale)>x:k-=1
    while F((k+1)*(k+1),scale)<=x:k+=1
    return I(F(k,1<<bits),F(k+1,1<<bits))
RT2=sqrt_bounds(F(2)); H=1/RT2
Q0=F(142559,50000); C0=sqrt_bounds(Q0-F(1,4))-F(3,2)

def atan_inv(m,n):
    s=F(0)
    for k in range(n):
        t=F(1,(2*k+1)*m**(2*k+1));s += t if k%2==0 else -t
    k=n;t=F(1,(2*k+1)*m**(2*k+1));t=t if k%2==0 else -t
    return I(min(s,s+t),max(s,s+t))
PI=16*atan_inv(5,28)-4*atan_inv(239,8)

def sin_pos(x,n=15):
    z=[(F(-1) if k&1 else F(1))*x**(2*k+1)/F(factorial(2*k+1)) for k in range(n+2)]
    a=sum(z[:n+1],F(0));b=a+z[n+1];return I(min(a,b),max(a,b))
def cos_pos(x,n=15):
    z=[(F(-1) if k&1 else F(1))*x**(2*k)/F(factorial(2*k)) for k in range(n+2)]
    a=sum(z[:n+1],F(0));b=a+z[n+1];return I(min(a,b),max(a,b))
def sin_pt(x):return sin_pos(x) if x>=0 else -sin_pos(-x)
def sinR(x):
    x=iv(x);a=sin_pt(x.lo);b=sin_pt(x.hi);return I(a.lo,b.hi)
def cosR(x):
    x=iv(x);amin=F(0) if x.lo<=0<=x.hi else min(abs(x.lo),abs(x.hi));amax=max(abs(x.lo),abs(x.hi))
    return I(cos_pos(amax).lo,cos_pos(amin).hi)

class J:
    __slots__=('v','d','dd')
    def __init__(self,v,d=0,dd=0):self.v=iv(v);self.d=iv(d);self.dd=iv(dd)
    def __add__(self,o):o=jj(o);return J(self.v+o.v,self.d+o.d,self.dd+o.dd)
    __radd__=__add__
    def __neg__(self):return J(-self.v,-self.d,-self.dd)
    def __sub__(self,o):return self+(-jj(o))
    def __rsub__(self,o):return jj(o)-self
    def __mul__(self,o):
        o=jj(o);return J(self.v*o.v,self.d*o.v+self.v*o.d,self.dd*o.v+2*self.d*o.d+self.v*o.dd)
    __rmul__=__mul__
    def __truediv__(self,o):
        o=jj(o);assert o.d.lo==o.d.hi==0 and o.dd.lo==o.dd.hi==0;return J(self.v/o.v,self.d/o.v,self.dd/o.v)
def jj(x):return x if isinstance(x,J) else J(x)
def jsin(x):
    x=jj(x);s=sinR(x.v);c=cosR(x.v);return J(s,c*x.d,(-s)*x.d*x.d+c*x.dd)
def jcos(x):
    x=jj(x);s=sinR(x.v);c=cosR(x.v);return J(c,(-s)*x.d,(-c)*x.d*x.d-s*x.dd)

def add(a,b):return(a[0]+b[0],a[1]+b[1])
def sc(k,a):return(a[0]*k,a[1]*k)
def sub(a,b):return(a[0]-b[0],a[1]-b[1])
def sq(a):return a[0]*a[0]+a[1]*a[1]

DATA={
'Wp':((F(273,1000),F(275,1000),F(246,1000),F(206,1000)),(F(893,1000),F(803,1000),F(570,1000),F(180,1000),F(519,1000),F(465,1000))),
'Ws':((F(415,1000),F(52,1000),F(300,1000),F(233,1000)),(F(952,1000),F(952,1000),F(152,1000),F(561,1000),F(656,1000),F(638,1000))),
'Np':((F(318,1000),F(199,1000),F(271,1000),F(212,1000)),(F(883,1000),F(868,1000),F(550,1000),F(221,1000),F(578,1000),F(518,1000))),
'Ns':((F(318,1000),F(236,1000),F(246,1000),F(200,1000)),(F(1006,1000),F(815,1000),F(432,1000),F(240,1000),F(503,1000),F(429,1000))),
}

def bound(n,w,s,e,d5,source):
    (LN,LW,LS,LD),(mn,ms,mcw,m5,m7,m8)=DATA[source]
    cn,sn=jcos(n),jsin(n);cw,sw=jcos(w),jsin(w);cs,ss=jcos(s),jsin(s);ce,se=jcos(e),jsin(e)
    ny=(J(0),J(1)); ew=(-cw,-sw)
    n5={'Wp':(cw,sw),'Ws':(-sw,cw),'Np':(-sn,cn),'Ns':(cn,sn)}[source]
    n7=(-sw,cw);n8=(cs,ss)
    gN=add(sc(mn,ny),sc(m5,n5));gW=add(add(sc(mcw,ew),sc(-m5,n5)),sc(m7,n7))
    gS=add(sc(-ms,ny),sc(m8,n8));gD=add(sc(-m7,n7),sc(-m8,n8))
    vN=((cn-sn)/2,(sn+cn)/2);vW=((-cw-sw)/2,(-sw+cw)/2)
    vS=((cs+ss)/2,(ss-cs)/2);vD=(se*H,-ce*H)
    hN=F(1,2)+(cn+sn)/2;hS=F(1,2)+(cs+ss)/2;hW=F(1,2)+(cw+sw)/2
    cd,sd=jcos(d5),jsin(d5); h5=F(1,2)+(cd+(sd if d5.v.lo>=0 else -sd))/2
    h7=F(1,2)+jcos(e-w)*H;h8=F(1,2)+jcos(e-s)*H
    uc=(mcw*(cw+sw)+abs(ms-mn))*C0
    out=J(F(1,2))+mn*hN+ms*hS+mcw*hW+m5*h5+m7*h7+m8*h8-uc
    for L,v,g in ((LN,vN,gN),(LW,vW,gW),(LS,vS,gS),(LD,vD,gD)):
        z=sub(sc(2*L,v),g);out=out-sq(z)/(4*L)
    return out

N=I(F(1,5),F(2,5));S=I(F(1,6),F(2,5));E=I(-F(1,4),0)
SLICES=[
(I(0,F(1,10)),I(0,F(2,5))), (I(F(1,10),F(1,5)),I(0,F(3,10))),
(I(F(1,5),F(3,10)),I(0,F(1,5))), (I(F(3,10),F(2,5)),I(0,F(1,10))),
(I(F(1,5),F(3,10)),I(-F(1,10),0)), (I(F(3,10),F(2,5)),I(-F(1,5),0)),
(I(F(2,5),F(1,2)),I(-F(3,10),0)), (I(F(1,2),F(3,5)),I(-F(2,5),-F(1,10))),
(I(F(3,5),F(7,10)),I(-F(1,2),-F(1,5))), (I(F(7,10),PI.hi/F(4)),I(F(1,5)-PI.hi/F(4),-F(3,10))),
]
for source in DATA:
    vals=[]
    for wbox,dbox in SLICES:
        for var in ('n','w','s','e'):
            n=J(N,var=='n');w=J(wbox,var=='w');s=J(S,var=='s');e=J(E,var=='e')
            d=J(dbox,(var=='n')-(var=='w'));z=bound(n,w,s,e,d,source).dd
            assert z.hi<0,(source,var,wbox.lo,wbox.hi,z.hi);vals.append(z.hi)
    x=J(I(F(1,5),F(2,5)),1);z=bound(x,x,J(S),J(E),J(0),source).dd
    assert z.hi<0;(vals.append(z.hi))
    print(source,'max curvature upper',float(max(vals)))

PAIRS=[(F(1,5),F(0)),(F(1,5),F(1,5)),(F(2,5),F(0)),(F(2,5),F(2,5)),
       (F(1,5),None),(F(2,5),None)]
bestall=None
for source in DATA:
    best=None
    for n0,w0 in PAIRS:
      for s0 in (F(1,6),F(2,5)):
       for e0 in (-F(1,4),F(0)):
        if w0 is None:
            wb=I(PI.lo/F(4),PI.hi/F(4));db=I(n0-PI.hi/F(4),n0-PI.lo/F(4))
        else: wb=I(w0);db=I(n0-w0)
        z=bound(J(n0),J(wb),J(s0),J(e0),J(db),source).v-Q0
        assert z.lo>0,(source,n0,w0,s0,e0,z.lo)
        row=(z.lo,(n0,'pi/4' if w0 is None else w0,s0,e0))
        if best is None or row[0]<best[0]:best=row
    print(source,'endpoint min >',float(best[0]),'at',best[1])
    if bestall is None or best[0]<bestall[0]:bestall=(best[0],source,best[1])
assert bestall[0]>F(2,25)
print('worst >',float(bestall[0]),bestall[1:])
print('A2 P11 hand checker PASS')
