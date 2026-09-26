#!/usr/bin/env python3
"""Exact no-subdivision checker for A2 preparatory lemma P18."""
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
        o=iv(o);z=(self.lo*o.lo,self.lo*o.hi,self.hi*o.lo,self.hi*o.hi);return I(min(z),max(z))
    __rmul__=__mul__
    def inv(self):assert not(self.lo<=0<=self.hi);return I(1/self.hi,1/self.lo)
    def __truediv__(self,o):return self*iv(o).inv()
    def __rtruediv__(self,o):return iv(o)/self
    def abs(self):
        if self.lo<=0<=self.hi:return I(0,max(-self.lo,self.hi))
        return I(min(abs(self.lo),abs(self.hi)),max(abs(self.lo),abs(self.hi)))
def iv(x):return x if isinstance(x,I) else I(x)
def sqrt_bounds(x:F,bits=120):
    scale=1<<(2*bits);k=isqrt((x.numerator*scale)//x.denominator)
    while F(k*k,scale)>x:k-=1
    while F((k+1)*(k+1),scale)<=x:k+=1
    return I(F(k,1<<bits),F(k+1,1<<bits))
def sqrtI(x:I):return I(sqrt_bounds(x.lo).lo,sqrt_bounds(x.hi).hi)
def sinb(x,n=13):
    x=F(x);z=[(F(-1) if k&1 else F(1))*x**(2*k+1)/F(factorial(2*k+1)) for k in range(n+2)]
    a=sum(z[:n+1],F(0));b=a+z[n+1];return I(min(a,b),max(a,b))
def cosb(x,n=13):
    x=F(x);z=[(F(-1) if k&1 else F(1))*x**(2*k)/F(factorial(2*k)) for k in range(n+2)]
    a=sum(z[:n+1],F(0));b=a+z[n+1];return I(min(a,b),max(a,b))
Q0=F(142559,50000);R=sqrt_bounds(Q0);C0=sqrt_bounds(Q0-F(1,4))-F(3,2)
H=1/sqrt_bounds(F(2));S4=sinb(F(1,4));C4=cosb(F(1,4))
assert R.hi<F(17,10) and C0.hi<F(23,200)
CD0=H*(C4+S4);SD0=H*(C4-S4)
assert SD0.hi<F(13,25)
def low_curv(p,glo):
    m=F(27,100);P=p*p+m*m;q=2*p*m;s=F(13,25)
    assert P>q and P+q*s>glo*glo
    N=F(17,10)*(q*q*(1+s*s)+2*P*q*s)/(4*glo**3)
    assert N<F(23,100)
    return N
Nw=low_curv(F(7,20),F(27,50));Nd=low_curv(F(8,25),F(51,100))
assert F(27,100)-Nw>F(1,25) and F(27,100)-Nd>F(1,25)
p=F(1,8);m=F(1,4);P=p*p+m*m;q=2*p*m;s=F(71,100);g=F(7,20)
assert P+q*s==g*g
Nh=F(17,10)*(q*q*(1+s*s)+2*P*q*s)/(4*g**3)
assert Nh<F(13,100)<m
print('curvature reserves',float(F(27,100)-Nw),float(F(27,100)-Nd),float(m-Nh))
def frame(tag):
    if tag=='0':c=I(1);s=I(0)
    elif tag=='q':c=s=H
    else:c=CD0;s=SD0
    return (-c,-s),(s,-c)
def dot(a,b):return a[0]*b[0]+a[1]*b[1]
def add(a,b):return(a[0]+b[0],a[1]+b[1])
def scale(k,a):return(k*a[0],k*a[1])
def norm(a):return sqrtI(dot(a,a))
def hc(a):return(a[0].abs()+a[1].abs())/2
def hs(a,e,f):return(dot(a,e).abs()+dot(a,f).abs())/2
def csup(g):
    assert g[0].lo>=0 and g[1].lo>=0
    return C0*(g[0]+g[1])
def osup(g,e,f):return R*norm(g)-hs(g,e,f)
def gap(w,d,src,abc):
    alpha,beta,mu=map(F,abc);eW,fW=frame(w);eD,fD=frame(d);n=fW if src=='fW' else fD
    GC=add(scale(-alpha,eD),scale(-beta,eW))
    GW=add(scale(beta,eW),scale(-mu,n));GD=add(scale(alpha,eD),scale(mu,n))
    T=alpha*(hc(eD)+F(1,2))+beta*(hc(eW)+F(1,2))+mu*(hs(n,eW,fW)+hs(n,eD,fD))
    return T-csup(GC)-osup(GW,eW,fW)-osup(GD,eD,fD)
rows=[
 ('low-Wsecondary','fW',(F(7,20),F(19,50),F(27,100)),[('0','0'),('0','d0'),('d0','d0')],F(3,1000)),
 ('low-Dsecondary','fD',(F(41,100),F(8,25),F(27,100)),[('0','0'),('0','d0'),('d0','d0')],F(1,100)),
 ('high-Dsecondary','fD',(F(5,8),F(1,8),F(1,4)),[('0','d0'),('d0','d0'),('0','q'),('q','q')],F(1,100)),
]
best=None
for name,src,abc,verts,target in rows:
    rb=None
    for w,d in verts:
        z=gap(w,d,src,abc);assert z.lo>target,(name,w,d,z.lo,z.hi)
        row=(z.lo,w,d)
        if rb is None or row[0]<rb[0]:rb=row
        if best is None or row[0]<best[0]:best=(row[0],name,w,d)
    print(name,'min >',float(rb[0]),'at',rb[1:])
print('global min >',float(best[0]),best[1:])
print('A2 D-W secondary classification hand checker PASS')
