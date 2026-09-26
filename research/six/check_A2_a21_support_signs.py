#!/usr/bin/env python3
"""Scalar checks for fixed helper-support signs in unified A2.1."""
from fractions import Fraction as F
from math import factorial, isqrt

def sin_bounds(x,n=12):
    x=F(x)
    ts=[(F(-1) if k&1 else F(1))*x**(2*k+1)/F(factorial(2*k+1))
        for k in range(n+2)]
    a=sum(ts[:n+1],F(0)); b=a+ts[n+1]
    return min(a,b),max(a,b)

def cos_bounds(x,n=12):
    x=F(x)
    ts=[(F(-1) if k&1 else F(1))*x**(2*k)/F(factorial(2*k))
        for k in range(n+2)]
    a=sum(ts[:n+1],F(0)); b=a+ts[n+1]
    return min(a,b),max(a,b)

c16_lo,c16_hi=cos_bounds(F(1,6))
s16_lo,s16_hi=sin_bounds(F(1,6))
c13_lo,c13_hi=cos_bounds(F(1,3))
s13_lo,s13_hi=sin_bounds(F(1,3))

assert c16_lo > F(49,50)
assert c13_lo > F(9,10)
assert s16_hi < F(1,6)
assert s13_hi < F(1,3)
assert s16_hi/c16_lo < F(1,5)
assert c16_hi+s16_hi < F(7,6)

# Candidate constants r,m from exact radicals.
def sqrt_bounds(x:F,bits=120):
    scale=1<<(2*bits)
    k=isqrt((x.numerator*scale)//x.denominator)
    while F(k*k,scale)>x:k-=1
    while F((k+1)*(k+1),scale)<=x:k+=1
    return F(k,1<<bits),F(k+1,1<<bits)

rt2_lo,rt2_hi=sqrt_bounds(F(2))
h_lo,h_hi=1/rt2_hi,1/rt2_lo
# directed interval arithmetic for the candidate parameters is unnecessary
# for these coarse signs: evaluate with rational enclosures.
def div_bounds(nlo,nhi,dlo,dhi):
    assert dlo>0
    return nlo/dhi,nhi/dlo

Alo=(F(1466)+F(1940)*h_lo)/F(267)
Ahi=(F(1466)+F(1940)*h_hi)/F(267)
Blo=(F(327)+F(432)*h_lo)/F(712)
Bhi=(F(327)+F(432)*h_hi)/F(712)
disc_lo=Alo*Alo-4*Bhi
disc_hi=Ahi*Ahi-4*Blo
sd_lo,sd_hi=sqrt_bounds(disc_lo)[0],sqrt_bounds(disc_hi)[1]
slo,shi=div_bounds(2*Blo,2*Bhi,Alo+sd_lo,Ahi+sd_hi)
tlo=(-F(20)+F(30)*h_lo)*slo+F(7,2)-F(9,2)*h_hi
thi=(-F(20)+F(30)*h_hi)*shi+F(7,2)-F(9,2)*h_lo
rlo,rhi=div_bounds(slo+F(1,2),shi+F(1,2),slo+F(3,2),shi+F(3,2))
klo,khi=div_bounds(tlo+F(1,2),thi+F(1,2),F(3,2)-shi,F(3,2)-slo)
mlo=(1+rlo)*klo

assert rlo > F(1,3)
assert rhi < F(3,8)
assert mlo > F(4,5)

# Reserve inequalities used in the prose.
assert F(1,3)-F(6,5)*F(1,6) > 0
assert F(18,25)*F(49,50)-F(3,8)*F(1,3) > 0
assert -F(6,5)*F(1,6)+F(1,3)*F(9,10) > 0
assert F(9,10)-F(3,8)*F(1,3) > 0
assert F(4,5)-(F(7,6)*F(1,6)+F(3,8)*F(1,3)) > 0

print("r lower >",float(rlo),"r upper <",float(rhi))
print("m lower >",float(mlo))
print("A2.1 helper-support sign checks: PASS")
