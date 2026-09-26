#!/usr/bin/env python3
"""Fixed endpoint checker for the factorized A2.1 small-box stress.

No subdivision is performed. After the hand chamber reduction still to be
proved in A2.md, the helper angles lie at {-1/6,0,1/6}; the diagonal angle has
the three scalar possibilities from (U19). This script checks all such
noncandidate endpoints for all four W/S central choices and all four WN/SE
source choices.
"""
from fractions import Fraction as F

from n6_exact_intervals import (
    QI, q, sqrt_bounds, sin_point_bounds, cos_point_bounds, candidate_bounds
)

def sqrt_i(x:QI)->QI:
    return QI(sqrt_bounds(x.lo).lo, sqrt_bounds(x.hi).hi)

def trig(x:F):
    x=F(x)
    if x>=0:
        return cos_point_bounds(x), sin_point_bounds(x)
    c=cos_point_bounds(-x); s=sin_point_bounds(-x)
    return c,-s

def hpt(x:F):
    c,s=trig(x)
    return (1+c+(s if x>=0 else -s))/2

def add(a,b): return a[0]+b[0],a[1]+b[1]
def scale(k,a): k=q(k); return k*a[0],k*a[1]
def dot(a,b): return a[0]*b[0]+a[1]*b[1]
def norm(a): return sqrt_i(a[0]*a[0]+a[1]*a[1])

h,sstar,tstar,dstar,qstar=candidate_bounds(120)
R=sqrt_i(qstar)
rho=sqrt_i(qstar-F(1,4))-F(1,2)
r=(sstar+F(1,2))/(sstar+F(3,2))
k=(tstar+F(1,2))/(F(3,2)-sstar)
m=(1+r)*k

def helper_parts(e,n,w,s,Wown,Sown,src5,src6):
    ce,se=trig(e); cn,sn=trig(n); cw,sw=trig(w); cs,ss=trig(s)

    if Wown:
        cd,_=trig(w-n)
        alpha=(cw+sw)/cd
        gamma=(cn-sn)/cd
        qW=(cw,sw)
    else:
        alpha=1/cn
        gamma=1-sn/cn
        qW=(q(1),q(0))

    if Sown:
        beta=1-ss/cs
        delta=1/cs
        qS=(-ss,cs)
    else:
        beta=delta=q(1)
        qS=(q(0),q(1))

    nN=(-sn,cn); ex=(q(1),q(0))
    n5=(cw,sw) if src5=="W" else (cn,sn)
    n6=(-ss,cs) if src6=="S" else (-se,ce)
    n7=(-sw,cw); n8=(cs,ss)

    GE=add(scale(beta,ex),scale(r,n6))
    GN=add(scale(alpha,nN),scale(r,n5))
    GW=add(add(scale(-gamma,qW),scale(-r,n5)),scale(m,n7))
    GS=add(add(scale(-delta,qS),scale(-r,n6)),scale(m,n8))

    fE=((ce,se),(-se,ce))
    fN=((-sn,cn),(-cn,-sn))
    fW=((-cw,-sw),(sw,-cw))
    fS=((ss,-cs),(cs,ss))

    def support(G,fr,sgn):
        gain=sgn[0]*dot(G,fr[0])+sgn[1]*dot(G,fr[1])
        return R*norm(G)-gain/2

    A=(beta*hpt(e)+delta*hpt(s)+r*hpt(e-s)+m/2
       -support(GE,fE,(1,1))-support(GS,fS,(1,1)))
    B=(alpha*hpt(n)+gamma*hpt(w)+r*hpt(n-w)+m/2
       -support(GN,fN,(1,-1))-support(GW,fW,(1,-1)))
    return A,B

def Dterm(w,s,kind):
    b=(w-s)/2
    a=(w+s)/2
    cb,sb=trig(b)
    K=2*h*m  # sqrt(2)*m

    if kind=="zero":
        return K*((1-rho)*cb+rho*sb)

    if kind=="xmax":
        x=F(1,4)+abs(a)
        cx,sx=trig(x)
        test=2*R*sx
        if test.hi<=1:
            return K*((1-rho)*cb+rho*sb)*cx
        assert test.lo>=1,(x,test)
        return K*(((3*cb-sb)/2)*cx+((cb-sb)/2)*sx-R*(cb-sb))

    if kind=="switch":
        sx=1/(2*R)
        cx=sqrt_i(1-sx*sx)
        return K*((1-rho)*cb+rho*sb)*cx

    raise ValueError(kind)

V=(F(-1,6),F(0),F(1,6))
worst=None
checks=0

for Wown in (False,True):
  for Sown in (False,True):
    for src5 in ("W","N"):
      for src6 in ("S","E"):
        for e in V:
          for n in V:
            for w in V:
              for s in V:
                A,B=helper_parts(e,n,w,s,Wown,Sown,src5,src6)
                kinds=["zero","xmax"]
                xmax=F(1,4)+abs((w+s)/2)
                _,sx=trig(xmax)
                tst=2*R*sx
                if tst.lo>=1:
                    kinds.append("switch")
                else:
                    assert tst.hi<=1,(xmax,tst)

                for kind in kinds:
                    out=A+B+Dterm(w,s,kind)
                    checks+=1
                    if (e,n,w,s)==(0,0,0,0):
                        continue
                    assert out.lo>0,(Wown,Sown,src5,src6,e,n,w,s,kind,out)
                    row=(out.lo,Wown,Sown,src5,src6,e,n,w,s,kind)
                    if worst is None or row[0]<worst[0]:
                        worst=row

assert worst is not None
assert worst[0] > F(3,100)
print("fixed evaluations =",checks)
print("worst noncandidate margin >",float(worst[0]))
print("worst case =",worst[1:])
print("A2.1 factorized endpoint checks: PASS")
