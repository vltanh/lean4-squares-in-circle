#!/usr/bin/env python3
"""Exact scalar arithmetic for the A2 lemma theta_D>0."""
from fractions import Fraction as F
from math import factorial,isqrt

Q0=F(142559,50000)

def sqrt_bounds(x:F,bits=100):
    scale=1<<(2*bits)
    k=isqrt((x.numerator*scale)//x.denominator)
    while F(k*k,scale)>x:k-=1
    while F((k+1)*(k+1),scale)<=x:k+=1
    return F(k,1<<bits),F(k+1,1<<bits)

def sin_bounds(x,n=12):
    x=F(x)
    ts=[(F(-1) if k&1 else F(1))*x**(2*k+1)/F(factorial(2*k+1)) for k in range(n+2)]
    a=sum(ts[:n+1],F(0));b=a+ts[n+1]
    return min(a,b),max(a,b)

def cos_bounds(x,n=12):
    x=F(x)
    ts=[(F(-1) if k&1 else F(1))*x**(2*k)/F(factorial(2*k)) for k in range(n+2)]
    a=sum(ts[:n+1],F(0));b=a+ts[n+1]
    return min(a,b),max(a,b)

rt2_lo,rt2_hi=sqrt_bounds(F(2))
h_lo,h_hi=1/rt2_hi,1/rt2_lo

F0=F(9,10)*h_lo-F(1,2)
assert F0>0

s23_lo,s23_hi=sin_bounds(F(2,3)); c23_lo,c23_hi=cos_bounds(F(2,3))
s13_lo,s13_hi=sin_bounds(F(1,3)); c13_lo,c13_hi=cos_bounds(F(1,3))
tan13_hi=s13_hi/c13_lo
F23=F(9,10)*h_lo*(c23_lo+s23_lo)-F(1,2)-F(9,8)*tan13_hi
assert F23>0

q23_lo=F(9,10)*h_lo*(c23_lo+s23_lo)
B23_lo=q23_lo-F(1,2)
rad=Q0-q23_lo*q23_lo
A23_hi=sqrt_bounds(rad)[1]-F(1,2)
root2m1_hi=rt2_hi-F(1)
last=B23_lo-A23_hi*root2m1_hi
assert last>0

print('F(0) margin >',float(F0))
print('F(2/3) margin >',float(F23))
print('large-v endpoint margin >',float(last))
print('A2 D-own sign lemma: PASS')
