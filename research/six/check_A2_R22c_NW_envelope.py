#!/usr/bin/env python3
"""Exact fixed checker for the N/W pair envelope in final R22-c.

It proves, for both equality-source axes W-primary and N-secondary,

    A_u(n,w) >= A_Wp(0,w)

on -2/5<=n<=2/5, 0<=w<=pi/4.

No adaptive subdivision is used.
"""
from fractions import Fraction as F
import check_A2_R22c_reduced_monotonicity as C

I,J=C.I,C.J
r,m,R,rho=C.r,C.m,C.R,C.rho
jsin,jcos,jsqrt=C.jsin,C.jcos,C.jsqrt
hullJ,parts=C.hullJ,C.parts
PI=C.PI

def support_xdom_absy(x,y):
    x=C.jj(x); y=C.jj(y)
    assert x.v.lo>0
    aymax=max(abs(y.v.lo),abs(y.v.hi))
    assert x.v.lo>aymax,(x.v,y.v)

    norm=jsqrt(x*x+y*y)

    def one(V):
        U=x
        cap=U*rho
        vertex=norm*R-(U+V)/2
        sw=2*R*V.v-norm.v
        if sw.hi<=0:return cap
        if sw.lo>=0:return vertex
        return hullJ(cap,vertex)

    if y.v.lo>=0:return one(y)
    if y.v.hi<=0:return one(-y)

    yp=J(I(0,y.v.hi),y.d)
    yn=J(I(0,-y.v.lo),-y.d)
    return hullJ(one(yp),one(yn))

def A_der_n(nlo,nhi,wlo,whi,src):
    n=J(I(nlo,nhi),1)
    w=J(I(wlo,whi),0)
    sn,cn=jsin(n),jcos(n)
    sw,cw=jsin(w),jcos(w)
    q=n-w
    sq,cq=jsin(q),jcos(q)

    aa=1+sw/cw
    bb=1/cw

    # n boxes are one-sided at zero.
    HCN=F(1,2)+(cn+(sn if nlo>=0 else -sn))/2
    HCW=F(1,2)+(cw+sw)/2

    def eval_with_qsign(sgn):
        HWN=F(1,2)+(cq+sgn*sq)/2
        if src=="Wp":
            GNx=aa*cn-sq*r
            GNy=-sn*aa-cq*r
            GWx=bb+r
            GWy=-m
        elif src=="Ns":
            GNx=cn*aa
            GNy=-sn*aa-r
            GWx=bb+cq*r
            GWy=sq*r-m
        else:
            raise KeyError(src)
        out=(aa*HCN+bb*HCW+HWN*r+m/2
             -support_xdom_absy(GNx,GNy)
             -support_xdom_absy(GWx,GWy))
        return out.d

    if q.v.lo>=0:return eval_with_qsign(1)
    if q.v.hi<=0:return eval_with_qsign(-1)
    a=eval_with_qsign(1)
    b=eval_with_qsign(-1)
    return I(min(a.lo,b.lo),max(a.hi,b.hi))

def A_at_n0_wder(wlo,whi,src):
    n=J(I(0),0)
    w=J(I(wlo,whi),1)
    sn,cn=jsin(n),jcos(n)
    sw,cw=jsin(w),jcos(w)
    q=n-w
    sq,cq=jsin(q),jcos(q)

    aa=1+sw/cw
    bb=1/cw
    HCN=J(1)
    HCW=F(1,2)+(cw+sw)/2
    HWN=F(1,2)+(cq-sq)/2

    if src=="Wp":
        GNx=aa*cn-sq*r
        GNy=-sn*aa-cq*r
        GWx=bb+r
        GWy=-m
    elif src=="Ns":
        GNx=cn*aa
        GNy=-sn*aa-r
        GWx=bb+cq*r
        GWy=sq*r-m
    else:
        raise KeyError(src)

    return (aa*HCN+bb*HCW+HWN*r+m/2
            -support_xdom_absy(GNx,GNy)
            -support_xdom_absy(GWx,GWy))

Nneg=parts(-F(2,5),0,F(1,50))
Npos=parts(0,F(2,5),F(1,50))
W=parts(0,F(39,50),F(1,50))
W.append((F(39,50),PI.hi/4))

for src in ("Wp","Ns"):
    hi_neg=-F(10)
    lo_pos=F(10)
    for na,nb in Nneg:
        for wa,wb in W:
            hi_neg=max(hi_neg,A_der_n(na,nb,wa,wb,src).hi)
    for na,nb in Npos:
        for wa,wb in W:
            lo_pos=min(lo_pos,A_der_n(na,nb,wa,wb,src).lo)
    assert hi_neg<0 and lo_pos>0,(src,hi_neg,lo_pos)
    print(src,"n<0 derivative <",float(hi_neg),
          "n>0 derivative >",float(lo_pos))

# At n=0 the W-primary source is the lower equality source.
Wfine=parts(0,F(39,50),F(1,200))
Wfine.append((F(39,50),PI.hi/4))
lo=F(10)
for wa,wb in Wfine:
    z=A_at_n0_wder(wa,wb,"Ns")-A_at_n0_wder(wa,wb,"Wp")
    lo=min(lo,z.d.lo)
assert lo>0
print("d/dw [A_Ns(0,w)-A_Wp(0,w)] >",float(lo))

print("A2.2 R22-c N/W envelope: PASS")
