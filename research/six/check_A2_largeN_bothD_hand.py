#!/usr/bin/env python3
"""No-subdivision checker for A2 P13: large-N both-D-secondary extension."""
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
 def __mul__(self,o):o=iv(o);z=(self.lo*o.lo,self.lo*o.hi,self.hi*o.lo,self.hi*o.hi);return I(min(z),max(z))
 __rmul__=__mul__
 def __truediv__(self,o):o=iv(o);assert not(o.lo<=0<=o.hi);z=(self.lo/o.lo,self.lo/o.hi,self.hi/o.lo,self.hi/o.hi);return I(min(z),max(z))
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
H=1/sqrt_bounds(F(2));Q0=F(142559,50000)
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
LN=F(1,50);LW=F(12,25);LS=F(12,25);LD=F(1,50)
MU1=F(3,50);MU4=MU1;MU5=F(1,25);MU7=F(43,25);MU8=F(17,10)
def bound(n,w,s,e,src):
 cn,sn=jcos(n),jsin(n);cw,sw=jcos(w),jsin(w);cs,ss=jcos(s),jsin(s);ce,se=jcos(e),jsin(e)
 ny=(J(0),J(1));n5={'Wp':(cw,sw),'Ws':(-sw,cw),'Np':(cn,sn),'Ns':(-sn,cn)}[src]
 n7=(-(ce+se)*H,(ce-se)*H);n8=(-n7[0],-n7[1])
 gN=add(sc(MU1,ny),sc(MU5,n5));gW=add(sc(-MU5,n5),sc(MU7,n7));gS=add(sc(-MU4,ny),sc(MU8,n8));gD=add(sc(-MU7,n7),sc(-MU8,n8))
 mN=((cn-sn)/2,(sn+cn)/2);mW=((-cw-sw)/2,(-sw+cw)/2);mS=((cs+ss)/2,(ss-cs)/2);mD=(se*H,-ce*H)
 h1=F(1,2)+(cn+sn)/2;h4=F(1,2)+(cs+ss)/2;d=n-w;h5=F(1,2)+(jcos(d)+jsin(d))/2
 h7=F(1,2)+jcos(e-w)*H;h8=F(1,2)+jcos(e-s)*H
 out=J(F(1,2))+MU1*h1+MU4*h4+MU5*h5+MU7*h7+MU8*h8
 for L,m,g in ((LN,mN,gN),(LW,mW,gW),(LS,mS,gS),(LD,mD,gD)):
  z=sub(sc(2*L,m),g);out=out-sq(z)/(4*L)
 return out
N=I(F(1,5),F(2,5));W=I(0,F(1,5));S=I(F(1,6),F(2,5));E=I(-F(1,6),0)
for src in ('Wp','Ws','Np','Ns'):
 vals=[]
 for var in ('n','w','s'):
  z=bound(J(N,var=='n'),J(W,var=='w'),J(S,var=='s'),J(E),src).dd
  assert z.hi<0,(src,var,z.lo,z.hi);vals.append(z.hi)
 for a,b in ((-F(1,6),-F(1,12)),(-F(1,12),F(0))):
  z=bound(J(N),J(W),J(S),J(I(a,b),1),src).dd
  assert z.hi<0,(src,'e',a,b,z.lo,z.hi);vals.append(z.hi)
 print(src,'max curvature upper',float(max(vals)))
from itertools import product
bestall=None
for src in ('Wp','Ws','Np','Ns'):
 best=None
 for v in product((F(1,5),F(2,5)),(F(0),F(1,5)),(F(1,6),F(2,5)),(-F(1,6),F(0))):
  z=bound(*(J(x) for x in v),src).v-Q0
  assert z.lo>0,(src,v,z.lo,z.hi)
  row=(z.lo,v)
  if best is None or row[0]<best[0]:best=row
 print(src,'endpoint min >',float(best[0]),'at',best[1])
 if bestall is None or best[0]<bestall[0]:bestall=(best[0],src,best[1])
assert bestall[0]>F(9,50),bestall
print('worst >',float(bestall[0]),bestall[1:])
print('A2 P13 hand checker PASS')
