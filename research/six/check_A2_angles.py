#!/usr/bin/env python3
"""Exact endpoint arithmetic for A2 forced-own E/N angle windows."""
from fractions import Fraction as F
from math import factorial

Q0 = F(142559, 50000)
RBAR = F(23, 200)

# rho0-1 = sqrt(Q0-1/4)-3/2 < 23/200.
assert Q0 - F(1,4) < (F(3,2) + RBAR) ** 2

def sin_bounds(x, n=8):
    x=F(x)
    terms=[F((-1)**k)*x**(2*k+1)/F(factorial(2*k+1)) for k in range(n+2)]
    a=sum(terms[:n+1],F(0)); b=a+terms[n+1]
    return min(a,b),max(a,b)

def cos_bounds(x, n=8):
    x=F(x)
    terms=[F((-1)**k)*x**(2*k)/F(factorial(2*k)) for k in range(n+2)]
    a=sum(terms[:n+1],F(0)); b=a+terms[n+1]
    return min(a,b),max(a,b)

def qminus(x):
    slo,_=sin_bounds(x); clo,_=cos_bounds(x)
    A=(F(2)+clo+slo)/2
    return A*A+F(1,4)

def qplus(x):
    slo,_=sin_bounds(x); clo,_=cos_bounds(x)
    A=F(1)+(clo+slo)/2-RBAR*slo
    return A*A+F(1,4)

mminus=qminus(F(3,10))-Q0
mplus=qplus(F(5,12))-Q0
assert mminus>0
assert mplus>0

print("rho slack square comparison: PASS")
print("negative-tail endpoint margin >", float(mminus))
print("positive-tail endpoint margin >", float(mplus))
print("A2 forced-own E/N angle checks: PASS")
