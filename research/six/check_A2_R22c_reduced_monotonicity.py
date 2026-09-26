#!/usr/bin/env python3
"""Exact fixed checker for the reduced final R22-c monotonicity.

After the pair-envelope reduction, the last S-secondary stress has the form

    Phi(w,s,eps) = a(w)+b(s)+D(w,s,eps),

where a is the W-primary N/W envelope, b is the S-primary envelope for
s<=0 and E-secondary envelope for s>=0, and D is the diagonal-square term.

This checker verifies fixed rational derivative bounds only.  It performs no
adaptive subdivision.
"""
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
    def inv(self):
        assert not(self.lo<=0<=self.hi); return I(1/self.hi,1/self.lo)
    def __truediv__(self,o): return self*iv(o).inv()
    def __rtruediv__(self,o): return iv(o)/self
def iv(x): return x if isinstance(x,I) else I(x)

def sqrt_bounds(x:F,bits=110):
    scale=1<<(2*bits); k=isqrt((x.numerator*scale)//x.denominator)
    while F(k*k,scale)>x:k-=1
    while F((k+1)*(k+1),scale)<=x:k+=1
    return I(F(k,1<<bits),F(k+1,1<<bits))
def sqrtI(x:I): return I(sqrt_bounds(x.lo).lo,sqrt_bounds(x.hi).hi)

def atan_inv(m,n):
    s=F(0)
    for k in range(n):
        t=F(1,(2*k+1)*m**(2*k+1)); s += t if k%2==0 else -t
    k=n; t=F(1,(2*k+1)*m**(2*k+1)); t=t if k%2==0 else -t
    return I(min(s,s+t),max(s,s+t))
PI=16*atan_inv(5,28)-4*atan_inv(239,8)

def sin_pos_pt(x:F,n=14):
    assert 0<=x<=F(3,2)
    z=[(F(-1) if k&1 else F(1))*x**(2*k+1)/F(factorial(2*k+1)) for k in range(n+2)]
    a=sum(z[:n+1],F(0)); b=a+z[n+1]; return I(min(a,b),max(a,b))
def cos_pos_pt(x:F,n=14):
    assert 0<=x<=F(3,2)
    z=[(F(-1) if k&1 else F(1))*x**(2*k)/F(factorial(2*k)) for k in range(n+2)]
    a=sum(z[:n+1],F(0)); b=a+z[n+1]; return I(min(a,b),max(a,b))
def sin_pt(x): return sin_pos_pt(x) if x>=0 else -sin_pos_pt(-x)
def sinR(x:I):
    a=sin_pt(x.lo); b=sin_pt(x.hi); return I(a.lo,b.hi)
def cosR(x:I):
    amin=F(0) if x.lo<=0<=x.hi else min(abs(x.lo),abs(x.hi))
    amax=max(abs(x.lo),abs(x.hi))
    return I(cos_pos_pt(amax).lo,cos_pos_pt(amin).hi)

class J:
    __slots__=('v','d')
    def __init__(self,v,d=0): self.v=iv(v); self.d=iv(d)
    def __add__(self,o): o=jj(o); return J(self.v+o.v,self.d+o.d)
    __radd__=__add__
    def __neg__(self): return J(-self.v,-self.d)
    def __sub__(self,o): return self+(-jj(o))
    def __rsub__(self,o): return jj(o)-self
    def __mul__(self,o): o=jj(o); return J(self.v*o.v,self.d*o.v+self.v*o.d)
    __rmul__=__mul__
    def __truediv__(self,o):
        o=jj(o); return J(self.v/o.v,(self.d*o.v-self.v*o.d)/(o.v*o.v))
    def __rtruediv__(self,o): return jj(o)/self

def jj(x): return x if isinstance(x,J) else J(x)
def jsin(x): x=jj(x); return J(sinR(x.v),cosR(x.v)*x.d)
def jcos(x): x=jj(x); return J(cosR(x.v),-sinR(x.v)*x.d)
def jsqrt(x): x=jj(x); s=sqrtI(x.v); return J(s,x.d/(2*s))
def hullJ(a,b):
    return J(I(min(a.v.lo,b.v.lo),max(a.v.hi,b.v.hi)),
             I(min(a.d.lo,b.d.lo),max(a.d.hi,b.d.hi)))

# Exact candidate constants.
rt2=sqrt_bounds(F(2),140); h=1/rt2
A0=(F(1466)+F(1940)*h)/F(267); B0=(F(327)+F(432)*h)/F(712)
disc=A0*A0-4*B0
sd=I(sqrt_bounds(disc.lo,140).lo,sqrt_bounds(disc.hi,140).hi)
ss=2*B0/(A0+sd)
tt=(-F(20)+F(30)*h)*ss+F(7,2)-F(9,2)*h
q=2*ss*ss+4*ss+F(5,2)
R=sqrtI(q); rho=sqrtI(q-F(1,4))-F(1,2)
r=(ss+F(1,2))/(ss+F(3,2))
k=(tt+F(1,2))/(F(3,2)-ss)
m=(1+r)*k
rt2I=sqrt_bounds(F(2),140)

def support_xy(x,y,signy):
    x=jj(x); y=jj(y)
    yy=y if signy>0 else -y
    assert x.v.lo>0 and yy.v.lo>=0 and x.v.lo>yy.v.hi
    U,V=x,yy
    norm=jsqrt(x*x+y*y)
    cap=U*rho
    vertex=norm*R-(U+V)/2
    sw=2*R*V.v-norm.v
    if sw.hi<=0:return cap
    if sw.lo>=0:return vertex
    return hullJ(cap,vertex)

def a_der(lo,hi):
    w=J(I(lo,hi),1); sw,cw=jsin(w),jcos(w)
    aa=1+sw/cw; bb=1/cw
    H=F(1,2)+(cw+sw)/2
    GNx=aa+sw*r; GNy=-cw*r
    GWx=bb+r; GWy=-m
    out=aa+bb*H+H*r+m/2-support_xy(GNx,GNy,-1)-support_xy(GWx,GWy,-1)
    return out.d

def bneg_der(lo,hi):
    s=J(I(lo,hi),1); sn,cs=jsin(s),jcos(s)
    H=F(1,2)+(cs-sn)/2
    GEx=1-sn*r; GEy=cs*r
    GSx=cs+r; GSy=-sn+m
    out=1+H*(1+r)+m/2-support_xy(GEx,GEy,1)-support_xy(GSx,GSy,1)
    return out.d

def bpos_der(lo,hi):
    s=J(I(lo,hi),1); sn,cs=jsin(s),jcos(s)
    H=F(1,2)+(cs+sn)/2
    GEx=J(1); GEy=J(r)
    GSx=cs*(1+r); GSy=J(m)-sn*(1+r)
    out=1+H*(1+r)+m/2-support_xy(GEx,GEy,1)-support_xy(GSx,GSy,1)
    return out.d

def Dcap_dir(blo,bhi,dlo,dhi,db,dd):
    b=J(I(blo,bhi),db); d=J(I(dlo,dhi),dd)
    cb,sb=jcos(b),jsin(b); cd=jcos(d)
    Q=cb*(1-rho)+sb*rho
    return (cd*Q*(rt2I*m)).d

def Dvert_dir(blo,bhi,dlo,dhi,db,dd):
    b=J(I(blo,bhi),db); d=J(I(dlo,dhi),dd)
    cb,sb=jcos(b),jsin(b); cd,sd=jcos(d),jsin(d)
    qv=cb-sb
    return ((cd*cb-qv*R+qv*(cd-sd)/2)*(rt2I*m)).d

def parts(lo,hi,step):
    out=[]; x=F(lo); hi=F(hi); step=F(step)
    while x<hi:
        y=min(x+step,hi); out.append((x,y)); x=y
    return out

def main():
    # Pair-envelope derivative bounds.
    AP=parts(0,F(157,200),F(1,400)); AP.append((F(157,200),PI.hi/4))
    loA=min(a_der(a,b).lo for a,b in AP)
    assert loA>-F(29,100)
    print("a'(w) >",float(loA))
    
    BN=parts(-F(2,5),0,F(1,400))
    hiBN=max(bneg_der(a,b).hi for a,b in BN)
    assert hiBN<F(2,5)
    print("b_-'(s) <",float(hiBN))
    
    BP=parts(0,F(1,6),F(1,400))
    loBP=min(bpos_der(a,b).lo for a,b in BP)
    assert loBP>1
    print("b_+'(s) >",float(loBP))
    
    # D support branch ranges.
    # If D is on the cap branch then |delta|<31/100:
    # R>5/3 makes 1/(2R)<3/10, while sin(31/100)>3/10.
    # If D is on the vertex branch then delta<-5/17:
    # positive delta is <1/5, while vertex requires |sin delta|>5/17.
    Bcap=parts(-F(1,12),F(3,5),F(1,50))
    Dcap=parts(-F(31,100),F(1,5),F(1,50))
    loW=F(10); loS=F(10); hiS=-F(10)
    for ba,bb in Bcap:
        for da,db in Dcap:
            zw=Dcap_dir(ba,bb,da,db,F(1,2),-F(1,2))
            zs=Dcap_dir(ba,bb,da,db,-F(1,2),-F(1,2))
            loW=min(loW,zw.lo); loS=min(loS,zs.lo); hiS=max(hiS,zs.hi)
    assert loW>F(29,100) and loS>-F(19,20) and hiS<-F(1,2)
    print("cap D_w >",float(loW),"D_s in",float(loS),float(hiS))
    
    Bv=parts(-F(1,12),F(3,5),F(1,200))
    Dv=parts(-F(3,5),-F(5,17),F(1,200))
    loW=F(10)
    for ba,bb in Bv:
        for da,db in Dv:
            loW=min(loW,Dvert_dir(ba,bb,da,db,F(1,2),-F(1,2)).lo)
    assert loW>F(29,100)
    print("vertex D_w >",float(loW))
    
    Bv2=parts(-F(1,12),F(3,5),F(1,50))
    Dv2=parts(-F(3,5),-F(5,17),F(1,50))
    loS=F(10); hiS=-F(10)
    for ba,bb in Bv2:
        for da,db in Dv2:
            z=Dvert_dir(ba,bb,da,db,-F(1,2),-F(1,2))
            loS=min(loS,z.lo); hiS=max(hiS,z.hi)
    assert loS>-F(19,20) and hiS<-F(1,2)
    print("vertex D_s in",float(loS),float(hiS))
    
    print("A2.2 R22-c reduced monotonicity: PASS")
    

if __name__ == "__main__":
    main()
