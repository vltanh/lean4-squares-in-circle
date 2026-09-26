#!/usr/bin/env python3
from fractions import Fraction as F
from math import factorial,isqrt
class I:
 __slots__=('lo','hi')
 def __init__(self,lo,hi=None):self.lo=F(lo);self.hi=F(lo if hi is None else hi);assert self.lo<=self.hi
 def __add__(self,o):o=iv(o);return I(self.lo+o.lo,self.hi+o.hi)
 __radd__=__add__
 def __neg__(self):return I(-self.hi,-self.lo)
 def __sub__(self,o):return self+(-iv(o))
 def __rsub__(self,o):return iv(o)-self
 def __mul__(self,o):
  o=iv(o);z=(self.lo*o.lo,self.lo*o.hi,self.hi*o.lo,self.hi*o.hi);return I(min(z),max(z))
 __rmul__=__mul__
 def __truediv__(self,o):
  o=iv(o);assert not(o.lo<=0<=o.hi);z=(self.lo/o.lo,self.lo/o.hi,self.hi/o.lo,self.hi/o.hi);return I(min(z),max(z))
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
H=1/sqrt_bounds(F(2));Q0=F(142559,50000);C0=sqrt_bounds(Q0-F(1,4))-F(3,2)
def atan_inv(m,n):
 s=F(0)
 for k in range(n):
  t=F(1,(2*k+1)*m**(2*k+1));s += t if k%2==0 else -t
 k=n;t=F(1,(2*k+1)*m**(2*k+1));t=t if k%2==0 else -t
 return I(min(s,s+t),max(s,s+t))
PI=16*atan_inv(5,28)-4*atan_inv(239,8)
def sin_pos(x,n=15):
 assert 0<=x<=F(3,2);z=[(F(-1) if k&1 else F(1))*x**(2*k+1)/F(factorial(2*k+1)) for k in range(n+2)];a=sum(z[:n+1],F(0));b=a+z[n+1];return I(min(a,b),max(a,b))
def cos_pos(x,n=15):
 assert 0<=x<=F(3,2);z=[(F(-1) if k&1 else F(1))*x**(2*k)/F(factorial(2*k)) for k in range(n+2)];a=sum(z[:n+1],F(0));b=a+z[n+1];return I(min(a,b),max(a,b))
def sin_pt(x):return sin_pos(x) if x>=0 else -sin_pos(-x)
def sinR(x):x=iv(x);a=sin_pt(x.lo);b=sin_pt(x.hi);return I(a.lo,b.hi)
def cosR(x):
 x=iv(x);amin=F(0) if x.lo<=0<=x.hi else min(abs(x.lo),abs(x.hi));amax=max(abs(x.lo),abs(x.hi));return I(cos_pos(amax).lo,cos_pos(amin).hi)
class J:
 __slots__=('v','d','dd')
 def __init__(self,v,d=0,dd=0):self.v=iv(v);self.d=iv(d);self.dd=iv(dd)
 def __add__(self,o):o=jj(o);return J(self.v+o.v,self.d+o.d,self.dd+o.dd)
 __radd__=__add__
 def __neg__(self):return J(-self.v,-self.d,-self.dd)
 def __sub__(self,o):return self+(-jj(o))
 def __rsub__(self,o):return jj(o)-self
 def __mul__(self,o):o=jj(o);return J(self.v*o.v,self.d*o.v+self.v*o.d,self.dd*o.v+2*self.d*o.d+self.v*o.dd)
 __rmul__=__mul__
 def __truediv__(self,o):o=jj(o);assert o.d.lo==o.d.hi==0 and o.dd.lo==o.dd.hi==0;return J(self.v/o.v,self.d/o.v,self.dd/o.v)
def jj(x):return x if isinstance(x,J) else J(x)
def jsin(x):x=jj(x);s=sinR(x.v);c=cosR(x.v);return J(s,c*x.d,(-s)*x.d*x.d+c*x.dd)
def jcos(x):x=jj(x);s=sinR(x.v);c=cosR(x.v);return J(c,-s*x.d,-c*x.d*x.d-s*x.dd)
def add(a,b):return(a[0]+b[0],a[1]+b[1])
def sc(k,a):return(a[0]*k,a[1]*k)
def sub(a,b):return(a[0]-b[0],a[1]-b[1])
def sq(a):return a[0]*a[0]+a[1]*a[1]

DS={
'Wp':((F(12,1000),F(561,1000),F(195,1000),F(232,1000)),(F(32,1000),F(91,1000),F(1543,1000),F(14,1000),F(1090,1000),F(593,1000))),
'Ws':((F(203,1000),F(307,1000),F(230,1000),F(260,1000)),(F(0),F(47,1000),F(861,1000),F(697,1000),F(1293,1000),F(745,1000))),
'Np':((F(12,1000),F(552,1000),F(198,1000),F(238,1000)),(F(0),F(91,1000),F(1522,1000),F(40,1000),F(1114,1000),F(604,1000))),
'Ns':((F(12,1000),F(562,1000),F(194,1000),F(232,1000)),(F(36,1000),F(90,1000),F(1542,1000),F(17,1000),F(1089,1000),F(592,1000))),
}
SSP={
'Wp':((F(136,1000),F(361,1000),F(242,1000),F(261,1000)),(F(431,1000),F(745,1000),F(869,1000),F(139,1000),F(685,1000),F(484,1000))),
'Ws':((F(103,1000),F(267,1000),F(324,1000),F(306,1000)),(F(41,1000),F(1001,1000),F(761,1000),F(313,1000),F(811,1000),F(664,1000))),
'Np':((F(60,1000),F(326,1000),F(308,1000),F(306,1000)),(F(0),F(949,1000),F(894,1000),F(205,1000),F(806,1000),F(625,1000))),
'Ns':((F(217,1000),F(325,1000),F(223,1000),F(235,1000)),(F(694,1000),F(694,1000),F(668,1000),F(244,1000),F(613,1000),F(438,1000))),
}
SSN={
'Wp':((F(216,1000),F(324,1000),F(225,1000),F(235,1000)),(F(680,1000),F(693,1000),F(683,1000),F(226,1000),F(615,1000),F(451,1000))),
'Ws':((F(293,1000),F(16,1000),F(371,1000),F(320,1000)),(F(180,1000),F(1144,1000),F(46,1000),F(854,1000),F(886,1000),F(777,1000))),
'Np':((F(90,1000),F(291,1000),F(307,1000),F(312,1000)),(F(0),F(948,1000),F(734,1000),F(306,1000),F(824,1000),F(624,1000))),
'Ns':((F(222,1000),F(316,1000),F(224,1000),F(238,1000)),(F(702,1000),F(702,1000),F(604,1000),F(272,1000),F(614,1000),F(429,1000))),
}
for D in (DS,SSP,SSN):
 for L,M in D.values():assert sum(L)==1

def bound(n,w,s,e,source,graph,sign='p'):
 D=DS if graph=='Ds' else (SSP if sign=='p' else SSN);(LN,LW,LS,LD),(mn,ms,mcw,m5,m7,m8)=D[source]
 cn,sn=jcos(n),jsin(n);cw,sw=jcos(w),jsin(w);cs,ss=jcos(s),jsin(s);ce,se=jcos(e),jsin(e)
 ny=(J(0),J(1));ew=(-cw,-sw);n5={'Wp':(cw,sw),'Ws':(-sw,cw),'Np':(-sn,cn),'Ns':(cn,sn)}[source];n7=(-sw,cw)
 n8=((ce+se)*H,-(ce-se)*H) if graph=='Ds' else (cs,ss)
 gN=add(sc(mn,ny),sc(m5,n5));gW=add(add(sc(mcw,ew),sc(-m5,n5)),sc(m7,n7));gS=add(sc(-ms,ny),sc(m8,n8));gD=add(sc(-m7,n7),sc(-m8,n8))
 vN=((cn-sn)/2,(sn+cn)/2);vW=((-cw-sw)/2,(-sw+cw)/2);vS=((cs+ss)/2,(ss-cs)/2);vD=(se*H,-ce*H)
 if graph=='Ds' or sign=='p': hN=F(1,2)+(cn+sn)/2
 else: hN=F(1,2)+(cn-sn)/2
 hS=F(1,2)+(cs+ss)/2;hW=F(1,2)+(cw+sw)/2;d=n-w
 if graph=='Ds' or sign=='p': h5=F(1,2)+(jcos(d)+jsin(d))/2
 else: h5=F(1,2)+(jcos(d)-jsin(d))/2
 h7=F(1,2)+jcos(e-w)*H;h8=F(1,2)+jcos(e-s)*H
 uc=(mcw*(cw+sw)+abs(ms-mn))*C0
 out=J(F(1,2))+mn*hN+ms*hS+mcw*hW+m5*h5+m7*h7+m8*h8-uc
 for L,v,g in ((LN,vN,gN),(LW,vW,gW),(LS,vS,gS),(LD,vD,gD)):
  z=sub(sc(2*L,v),g);out=out-sq(z)/(4*L)
 return out

S=I(F(1,6),F(2,5));E=I(-F(1,4),0)
N=I(-F(1,5),F(1,5));W=I(0,F(1,5))
for src in ('Wp','Ns'):
 vals=[]
 for var in ('n','w','s','e'):
  z=bound(J(N,var=='n'),J(W,var=='w'),J(S,var=='s'),J(E,var=='e'),src,'Ds').dd;assert z.hi<0;vals.append(z.hi)
for src in ('Np','Ws'):
 for var in ('w','s','e'):
  z=bound(J(N),J(W,var=='w'),J(S,var=='s'),J(E,var=='e'),src,'Ds').dd;assert z.hi<0
 ns=[(-F(1,5),-F(3,20)),(-F(3,20),-F(1,10)),(-F(1,10),-F(1,20)),(-F(1,20),0),(0,F(1,5))] if src=='Np' else [(-F(1,5),F(1,5))]
 for a,b in ns:
  assert bound(J(I(a,b),1),J(W),J(S),J(E),src,'Ds').dd.hi<0
for a,b in ((0,F(1,20)),(F(1,20),F(1,10)),(F(1,10),F(3,20)),(F(3,20),F(1,5))):
 assert bound(J(N),J(I(a,b),1),J(S),J(E),'Ws','Ds').dd.hi<0

WSLICES=[(F(k,20),F(k+1,20)) for k in range(15)]+[(F(15,20),PI.hi/F(4))]
for sign,NSLICES in [('p',[(F(k,20),F(k+1,20)) for k in range(4)]),('n',[(F(k,20),F(k+1,20)) for k in range(-4,0)])]:
 for src in SSP:
  for na,nb in NSLICES:
   NN=I(na,nb)
   for a,b in WSLICES:
    wb=I(a,b)
    for var in ('n','w','s','e'):
     z=bound(J(NN,var=='n'),J(wb,var=='w'),J(S,var=='s'),J(E,var=='e'),src,'Ss',sign)
     if sign=='p' and src=='Np' and var=='n': assert z.d.lo>0
     else: assert z.dd.hi<0

def wpi():return I(PI.lo/F(4),PI.hi/F(4))
best=None
from itertools import product
for src in DS:
 for n,w,s,e in product((-F(1,5),F(1,5)),(F(0),F(1,5)),(F(1,6),F(2,5)),(-F(1,4),F(0))):
  z=bound(J(n),J(w),J(s),J(e),src,'Ds').v-Q0;assert z.lo>0
  row=(z.lo,'Ds',src,n,w,s,e);best=row if best is None or row[0]<best[0] else best
for sign,nends in [('p',(F(0),F(1,5))),('n',(-F(1,5),F(0)))]:
 for src in SSP:
  for n,s,e in product(nends,(F(1,6),F(2,5)),(-F(1,4),F(0))):
   for wp in (False,True):
    w=J(wpi()) if wp else J(F(0))
    z=bound(J(n),w,J(s),J(e),src,'Ss',sign).v-Q0;assert z.lo>0
    row=(z.lo,'Ss'+sign,src,n,'pi/4' if wp else 0,s,e);best=row if row[0]<best[0] else best
assert best[0]>F(1,250)
print('worst endpoint >',float(best[0]),best[1:])
print('low-N W-secondary/D-or-S-secondary hand checker PASS')
