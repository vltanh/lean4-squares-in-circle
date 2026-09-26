from fractions import Fraction as F
from dataclasses import dataclass
from math import factorial,isqrt

Q0=F(142559,50000)
A=F(3,10); B=F(9,20); M=F(1,4)
TLO=F(-2,3); THI=F(2,5); ULO=F(-2,5); UHI=F(2,5)

@dataclass(frozen=True)
class I:
    lo:F; hi:F
    def __post_init__(self): assert self.lo<=self.hi
    def __add__(self,o): o=iv(o); return I(self.lo+o.lo,self.hi+o.hi)
    __radd__=__add__
    def __neg__(self): return I(-self.hi,-self.lo)
    def __sub__(self,o): return self+(-iv(o))
    def __rsub__(self,o): return iv(o)-self
    def __mul__(self,o):
        o=iv(o); xs=(self.lo*o.lo,self.lo*o.hi,self.hi*o.lo,self.hi*o.hi)
        return I(min(xs),max(xs))
    __rmul__=__mul__
    def sq(self):
        if self.lo<=0<=self.hi: return I(F(0),max(self.lo*self.lo,self.hi*self.hi))
        xs=(self.lo*self.lo,self.hi*self.hi); return I(min(xs),max(xs))
    def abs(self):
        if self.lo<=0<=self.hi:return I(F(0),max(-self.lo,self.hi))
        return I(min(abs(self.lo),abs(self.hi)),max(abs(self.lo),abs(self.hi)))

def iv(x): return x if isinstance(x,I) else I(F(x),F(x))

def sqrt_bounds(x:F,bits=70):
    assert x>=0
    if x==0:return I(F(0),F(0))
    scale=1<<(2*bits); k=isqrt((x.numerator*scale)//x.denominator)
    while F(k*k,scale)>x:k-=1
    lo=F(k,1<<bits); hi=F(k+1,1<<bits)
    while hi*hi<x:
        k+=1; hi=F(k+1,1<<bits)
    return I(lo,hi)

R=sqrt_bounds(Q0)
RH=sqrt_bounds(Q0-F(1,4))
CMAX=RH-F(3,2)

def sin_point_pos(x,n=10):
    assert 0<=x<=F(16,15)
    ts=[(F(-1) if k%2 else F(1))*x**(2*k+1)/F(factorial(2*k+1))
        for k in range(n+2)]
    s=sum(ts[:n+1],F(0)); t=s+ts[n+1]
    return I(min(s,t),max(s,t))

def cos_point_pos(x,n=10):
    assert 0<=x<=F(16,15)
    ts=[(F(-1) if k%2 else F(1))*x**(2*k)/F(factorial(2*k))
        for k in range(n+2)]
    s=sum(ts[:n+1],F(0)); t=s+ts[n+1]
    return I(min(s,t),max(s,t))

def sin_point(x):
    if x>=0:return sin_point_pos(x)
    return -sin_point_pos(-x)

def sinI(x):
    a=sin_point(x.lo); b=sin_point(x.hi)
    return I(a.lo,b.hi)

def cosI(x):
    amin=F(0) if x.lo<=0<=x.hi else min(abs(x.lo),abs(x.hi))
    amax=max(abs(x.lo),abs(x.hi))
    return I(cos_point_pos(amax).lo,cos_point_pos(amin).hi)

def abs_lower(x):
    return F(0) if x.lo<=0<=x.hi else min(abs(x.lo),abs(x.hi))

def dot(a,b): return a[0]*b[0]+a[1]*b[1]
def add(a,b): return (a[0]+b[0],a[1]+b[1])
def scale(k,a): return (k*a[0],k*a[1])

def norm_hi(a):
    q=(a[0].sq()+a[1].sq()).hi
    return sqrt_bounds(q).hi

def frame(t):
    c=cosI(t); s=sinI(t)
    return ((-c,-s),(s,-c))

def support_upper(G,ang):
    e,f=frame(ang)
    return R.hi*norm_hi(G)-F(1,2)*(abs_lower(dot(G,e))+abs_lower(dot(G,f)))

def central_upper(G):
    return CMAX.hi*(max(F(0),G[0].hi)+max(F(0),G[1].hi))

def axis_vec(which,t,u):
    eW,fW=frame(t); eD,fD=frame(u)
    return {'We':eW,'Wf':fW,'De':eD,'Df':fD}[which]

def gap_lower(t,u,which,sgn):
    ct,st=cosI(t),sinI(t); cu,su=cosI(u),sinI(u)
    HD=I(F(1,2),F(1,2))+F(1,2)*(cu+su.abs())
    HW=I(F(1,2),F(1,2))+F(1,2)*(ct+st.abs())
    d=u-t; cd,sd=cosI(d),sinI(d)
    HP=I(F(1,2),F(1,2))+F(1,2)*(cd+sd.abs())
    lhs=(A*HD+B*HW+M*HP).lo

    nD=(I(-1,-1),I(0,0))
    eW,_=frame(t)
    n=scale(F(sgn),axis_vec(which,t,u))
    GC=add(scale(-A,nD),scale(-B,eW))
    GW=add(scale(B,eW),scale(-M,n))
    GD=add(scale(A,nD),scale(M,n))

    rhs=central_upper(GC)+support_upper(GW,t)+support_upper(GD,u)
    return lhs-rhs

# Exact angle-domain checks.
s23=sin_point_pos(F(2,3)); c23=cos_point_pos(F(2,3))
s25=sin_point_pos(F(2,5)); c25=cos_point_pos(F(2,5))
amin_lo=F(1,2)+(F(2)-RH.hi)*c23.lo+F(1,2)*s23.lo
rho_hi=RH.hi-F(1,2)
assert amin_lo>rho_hi
cap_25_hi=R.hi-c25.lo-s25.lo
side_depth_lo=F(2)-RH.hi
assert cap_25_hi<side_depth_lo

CASES=[(w,s) for w in ('We','Wf','De','Df') for s in (1,-1)]

def split(t,u,d):
    if t.hi-t.lo>=u.hi-u.lo:
        m=(t.lo+t.hi)/2
        return [(I(t.lo,m),u,d+1),(I(m,t.hi),u,d+1)]
    m=(u.lo+u.hi)/2
    return [(t,I(u.lo,m),d+1),(t,I(m,u.hi),d+1)]

def replay(which,sgn):
    stack=[(I(TLO,THI),I(ULO,UHI),0)]
    vis=leaves=maxd=0
    while stack:
        t,u,d=stack.pop(); vis+=1; maxd=max(maxd,d)
        if t.lo>u.hi: continue
        g=gap_lower(t,u,which,sgn)
        if g>0:
            leaves+=1
            continue
        assert d<32,(which,sgn,d,g,t,u)
        stack.extend(split(t,u,d))
    return vis,leaves,maxd

if __name__=='__main__':
    print('angle-domain margins',float(amin_lo-rho_hi),float(side_depth_lo-cap_25_hi))
    total=0
    for c in CASES:
        z=replay(*c); total+=z[1]
        print(c,'visited=',z[0],'leaves=',z[1],'depth=',z[2])
    print('TOTAL certified leaves=',total)
