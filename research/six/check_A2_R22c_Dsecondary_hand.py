#!/usr/bin/env python3
"""Exact no-search checker for the A2.2 small-s D-secondary extension."""
from fractions import Fraction as F
from math import factorial,isqrt
from itertools import product

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
        if self.lo<=0<=self.hi: return I(0,max(self.lo*self.lo,self.hi*self.hi))
        return I(min(self.lo*self.lo,self.hi*self.hi),max(self.lo*self.lo,self.hi*self.hi))
def iv(x): return x if isinstance(x,I) else I(x)

def sqrt_bounds(x:F,bits=110):
    scale=1<<(2*bits); k=isqrt((x.numerator*scale)//x.denominator)
    while F(k*k,scale)>x: k-=1
    while F((k+1)*(k+1),scale)<=x: k+=1
    return I(F(k,1<<bits),F(k+1,1<<bits))

H=1/sqrt_bounds(F(2))
Q0=F(142559,50000)
C0=sqrt_bounds(Q0-F(1,4))-F(3,2)

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

def add(a,b): return (a[0]+b[0],a[1]+b[1])
def sc(k,a): return (a[0]*k,a[1]*k)
def sub(a,b): return (a[0]-b[0],a[1]-b[1])
def sq(a): return a[0]*a[0]+a[1]*a[1]

LOW={
'Wp':((F(12,1000),F(561,1000),F(195,1000),F(232,1000)),(F(32,1000),F(91,1000),F(1543,1000),F(14,1000),F(1090,1000),F(593,1000))),
'Ws':((F(203,1000),F(307,1000),F(230,1000),F(260,1000)),(F(0),F(47,1000),F(861,1000),F(697,1000),F(1293,1000),F(745,1000))),
'Np':((F(12,1000),F(552,1000),F(198,1000),F(238,1000)),(F(0),F(91,1000),F(1522,1000),F(40,1000),F(1114,1000),F(604,1000))),
'Ns':((F(12,1000),F(562,1000),F(194,1000),F(232,1000)),(F(36,1000),F(90,1000),F(1542,1000),F(17,1000),F(1089,1000),F(592,1000))),
}
HIGH={
'Wp':((F(99,1000),F(472,1000),F(231,1000),F(198,1000)),(F(316,1000),F(316,1000),F(1193,1000),F(117,1000),F(939,1000),F(531,1000))),
'Ws':((F(437,1000),F(15,1000),F(251,1000),F(297,1000)),(F(0),F(0),F(43,1000),F(1658,1000),F(1682,1000),F(950,1000))),
'Np':((F(361,1000),F(126,1000),F(252,1000),F(261,1000)),(F(3,1000),F(11,1000),F(474,1000),F(1337,1000),F(1537,1000),F(937,1000))),
'Ns':((F(90,1000),F(480,1000),F(224,1000),F(206,1000)),(F(276,1000),F(276,1000),F(1241,1000),F(93,1000),F(969,1000),F(544,1000))),
}
NEG={
'Wp':((F(12,1000),F(562,1000),F(195,1000),F(231,1000)),(F(29,1000),F(92,1000),F(1545,1000),F(13,1000),F(1088,1000),F(593,1000))),
'Ws':((F(12,1000),F(552,1000),F(198,1000),F(238,1000)),(F(0),F(92,1000),F(1531,1000),F(39,1000),F(1113,1000),F(604,1000))),
'Np':((F(12,1000),F(553,1000),F(198,1000),F(237,1000)),(F(0),F(93,1000),F(1525,1000),F(36,1000),F(1109,1000),F(603,1000))),
'Ns':((F(12,1000),F(562,1000),F(195,1000),F(231,1000)),(F(35,1000),F(91,1000),F(1543,1000),F(18,1000),F(1086,1000),F(591,1000))),
}
for D in (LOW,HIGH,NEG):
    for L,_ in D.values(): assert sum(L)==1

def bound(n,w,s,e,source,D):
    (LN,LW,LS,LD),(mn,ms,mcw,m5,m7,m8)=D[source]
    cn,sn=jcos(n),jsin(n); cw,sw=jcos(w),jsin(w)
    cs,ss=jcos(s),jsin(s); ce,se=jcos(e),jsin(e)
    ny=(J(0),J(1)); ew=(-cw,-sw)
    n5={'Wp':(cw,sw),'Ws':(-sw,cw),'Np':(-sn,cn),'Ns':(cn,sn)}[source]
    n7=(-sw,cw); n8=((ce+se)*H,-(ce-se)*H)
    gN=add(sc(mn,ny),sc(m5,n5))
    gW=add(add(sc(mcw,ew),sc(-m5,n5)),sc(m7,n7))
    gS=add(sc(-ms,ny),sc(m8,n8))
    gD=add(sc(-m7,n7),sc(-m8,n8))
    vN=((cn-sn)/2,(sn+cn)/2)
    vW=((-cw-sw)/2,(-sw+cw)/2)
    vS=((cs+ss)/2,(ss-cs)/2)
    vD=(se*H,-ce*H)
    hN=F(1,2)+(cn+sn)/2
    hS=F(1,2)+(cs+ss)/2
    hW=F(1,2)+(cw+sw)/2
    h5=F(1,2)+(jcos(n-w)+jsin(n-w))/2
    h7=F(1,2)+jcos(e-w)*H
    h8=F(1,2)+jcos(e-s)*H
    uc=(mcw*(cw+sw)+abs(ms-mn))*C0
    out=J(F(1,2))+mn*hN+ms*hS+mcw*hW+m5*h5+m7*h7+m8*h8-uc
    for L,v,g in ((LN,vN,gN),(LW,vW,gW),(LS,vS,gS),(LD,vD,gD)):
        z=sub(sc(2*L,v),g); out=out-sq(z)/(4*L)
    return out

W=I(0,F(1,5)); S=I(-F(2,5),F(1,6)); E=I(-F(1,4),0)

# Low-n curvature.
N=I(-F(1,5),F(1,5))
for src in LOW:
    for var in ('w','s','e'):
        z=bound(J(N),J(W,var=='w'),J(S,var=='s'),J(E,var=='e'),src,LOW).dd
        assert z.hi<0,(src,var,z.lo,z.hi)
    if src!='Np':
        z=bound(J(N,1),J(W),J(S),J(E),src,LOW).dd
        assert z.hi<0,(src,'n',z.lo,z.hi)
pts=[-F(1,5),-F(3,20),-F(1,10),-F(1,20),F(0),F(1,20),F(1,10),F(3,20),F(1,5)]
for a,b in zip(pts,pts[1:]):
    z=bound(J(I(a,b),1),J(W),J(S),J(E),'Np',LOW).dd
    assert z.hi<0,('low Np',a,b,z.lo,z.hi)

# High positive n curvature; Ws uses fixed w partition.
N=I(F(1,5),F(2,5))
for src in HIGH:
    for var in ('n','s','e'):
        z=bound(J(N,var=='n'),J(W),J(S,var=='s'),J(E,var=='e'),src,HIGH).dd
        assert z.hi<0,(src,var,z.lo,z.hi)
    if src!='Ws':
        z=bound(J(N),J(W,1),J(S),J(E),src,HIGH).dd
        assert z.hi<0,(src,'w',z.lo,z.hi)
for a,b in zip([F(0),F(1,20),F(1,10),F(3,20),F(1,5)],
               [F(1,20),F(1,10),F(3,20),F(1,5),F(1,5)]):
    if a==b: continue
    z=bound(J(N),J(I(a,b),1),J(S),J(E),'Ws',HIGH).dd
    assert z.hi<0,('high Ws',a,b,z.lo,z.hi)

# Negative large n; Np is strictly increasing.
N=I(-F(2,5),-F(1,5))
for src in NEG:
    for var in ('w','s','e'):
        z=bound(J(N),J(W,var=='w'),J(S,var=='s'),J(E,var=='e'),src,NEG).dd
        assert z.hi<0,(src,var,z.lo,z.hi)
    if src=='Np':
        z=bound(J(N,1),J(W),J(S),J(E),src,NEG)
        assert z.d.lo>F(3,100),(z.d.lo,z.d.hi)
    elif src=='Ns':
        pts=[-F(2,5),-F(7,20),-F(3,10),-F(1,4),-F(1,5)]
        for a,b in zip(pts,pts[1:]):
            z=bound(J(I(a,b),1),J(W),J(S),J(E),src,NEG).dd
            assert z.hi<0,(src,a,b,z.lo,z.hi)
    else:
        z=bound(J(N,1),J(W),J(S),J(E),src,NEG).dd
        assert z.hi<0,(src,'n',z.lo,z.hi)

best=None
def test(D,label,ns_by_src,ws_by_src):
    global best
    for src in D:
        for n,w,s,e in product(ns_by_src(src),ws_by_src(src),
                               [F(-2,5),F(1,6)],[F(-1,4),F(0)]):
            z=bound(J(n),J(w),J(s),J(e),src,D).v-Q0
            assert z.lo>0,(label,src,n,w,s,e,z.lo)
            row=(z.lo,label,src,n,w,s,e)
            if best is None or row[0]<best[0]: best=row

test(LOW,'low',
     lambda src: LOW_N_PTS if src=='Np' else [F(-1,5),F(1,5)],
     lambda src: [F(0),F(1,5)])
test(HIGH,'high',
     lambda src: [F(1,5),F(2,5)],
     lambda src: [F(0),F(1,20),F(1,10),F(3,20),F(1,5)] if src=='Ws' else [F(0),F(1,5)])
test(NEG,'neg',
     lambda src: [F(-2,5)] if src=='Np' else
                 (NEG_NS_PTS if src=='Ns' else [F(-2,5),F(-1,5)]),
     lambda src: [F(0),F(1,5)])

assert best[0]>F(7,1000),best
print('worst endpoint margin >',float(best[0]),best[1:])
print('A2.2 R22-c D-secondary extension: PASS')
