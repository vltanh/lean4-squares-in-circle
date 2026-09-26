#!/usr/bin/env python3
from dataclasses import dataclass
from fractions import Fraction as F
from functools import lru_cache
from math import factorial,isqrt
from n6_exact_intervals import PI as PIQ

BITS=50
S=1<<BITS

def floordiv(a,b):
    assert b>0
    return a//b

def ceildiv(a,b):
    assert b>0
    return -((-a)//b)

@dataclass(frozen=True)
class FI:
    lo:int; hi:int
    def __post_init__(self):
        if self.lo>self.hi:raise ValueError((self.lo,self.hi))
    @staticmethod
    def point_int(n:int):return FI(n*S,n*S)
    @staticmethod
    def frac(x:F):
        return FI(floordiv(x.numerator*S,x.denominator),ceildiv(x.numerator*S,x.denominator))
    @staticmethod
    def bounds_frac(a:F,b:F):
        return FI(floordiv(a.numerator*S,a.denominator),ceildiv(b.numerator*S,b.denominator))
    def __neg__(self):return FI(-self.hi,-self.lo)
    def __add__(self,o):o=fi(o);return FI(self.lo+o.lo,self.hi+o.hi)
    __radd__=__add__
    def __sub__(self,o):return self+(-fi(o))
    def __rsub__(self,o):return fi(o)-self
    def __mul__(self,o):
        o=fi(o); xs=(self.lo*o.lo,self.lo*o.hi,self.hi*o.lo,self.hi*o.hi)
        return FI(floordiv(min(xs),S),ceildiv(max(xs),S))
    __rmul__=__mul__
    def div_int(self,n:int):
        if n<0:return (-self).div_int(-n)
        return FI(floordiv(self.lo,n),ceildiv(self.hi,n))
    def abs(self):
        if self.lo<=0<=self.hi:return FI(0,max(-self.lo,self.hi))
        return FI(min(abs(self.lo),abs(self.hi)),max(abs(self.lo),abs(self.hi)))
    def sq(self):
        a=self.abs();return a*a
    def intersect(self,o):
        o=fi(o);a=max(self.lo,o.lo);b=min(self.hi,o.hi);return None if a>b else FI(a,b)
    def width(self):return self.hi-self.lo
    def f(self):return (self.lo/S,self.hi/S)

def fi(x):
    if isinstance(x,FI):return x
    if isinstance(x,F):return FI.frac(x)
    if isinstance(x,int):return FI.point_int(x)
    return FI.frac(F(str(x)))

ZERO=FI.point_int(0);ONE=FI.point_int(1);PI=FI.bounds_frac(PIQ.lo,PIQ.hi)

def sqrt_fi(x:FI)->FI:
    if x.lo<0:raise ValueError
    lo=isqrt(x.lo*S)
    if lo*lo>x.lo*S:lo-=1
    hi=isqrt(x.hi*S)
    if hi*hi<x.hi*S:hi+=1
    return FI(lo,hi)

def pow_abs_bound(x:FI,n:int)->FI:
    a=x.abs(); y=ONE
    for _ in range(n):y=y*a
    return y

def _remainder_bound(x:FI,n:int)->int:
    p=pow_abs_bound(x,n)
    return ceildiv(p.hi,factorial(n))

@lru_cache(maxsize=1000000)
def sin_point(lo:int,hi:int)->FI:
    x=FI(lo,hi)
    x2=x*x; term=x; total=term
    for k in range(1,21):
        term=(term*x2).div_int((2*k)*(2*k+1))
        total = total-term if k%2 else total+term
    rem=_remainder_bound(x,43)
    return FI(total.lo-rem,total.hi+rem)

@lru_cache(maxsize=1000000)
def cos_point(lo:int,hi:int)->FI:
    x=FI(lo,hi);x2=x*x;term=ONE;total=term
    for k in range(1,22):
        term=(term*x2).div_int((2*k-1)*(2*k))
        total=total-term if k%2 else total+term
    rem=_remainder_bound(x,44)
    return FI(total.lo-rem,total.hi+rem)

def _critical_interval(num:int,den:int)->FI:
    return FI.frac(F(num,den))*PI

def _contains_overlap(x:FI,c:FI)->bool:
    return not (x.hi<c.lo or c.hi<x.lo)

@lru_cache(maxsize=500000)
def sin_interval(lo:int,hi:int)->FI:
    x=FI(lo,hi)
    if x.width()>=2*PI.lo:return FI(-S,S)
    a=sin_point(lo,lo);b=sin_point(hi,hi);L=min(a.lo,b.lo);H=max(a.hi,b.hi)
    for k in range(-4,6):
        c=_critical_interval(1+2*k,2)
        if _contains_overlap(x,c):
            v=S if k%2==0 else -S;L=min(L,v);H=max(H,v)
    return FI(max(-S,L),min(S,H))

@lru_cache(maxsize=500000)
def cos_interval(lo:int,hi:int)->FI:
    x=FI(lo,hi)
    if x.width()>=2*PI.lo:return FI(-S,S)
    a=cos_point(lo,lo);b=cos_point(hi,hi);L=min(a.lo,b.lo);H=max(a.hi,b.hi)
    for k in range(-4,7):
        c=FI.frac(F(k))*PI
        if _contains_overlap(x,c):
            v=S if k%2==0 else -S;L=min(L,v);H=max(H,v)
    return FI(max(-S,L),min(S,H))

def main():
    import math,time
    print('S',S,'pi',PI.f(),'width',PI.width())
    pts=[0,math.pi/12,math.pi/4,math.pi/2,math.pi,5*math.pi/4,7*math.pi/4]
    for z in pts:
        x=FI.frac(F(str(z)))
        a=sin_point(x.lo,x.hi);b=cos_point(x.lo,x.hi)
        print(z,a.f(),math.sin(z),b.f(),math.cos(z))
        assert a.lo/S-1e-15<=math.sin(z)<=a.hi/S+1e-15
        assert b.lo/S-1e-15<=math.cos(z)<=b.hi/S+1e-15
    t=time.time()
    for j in range(10000):
        x=FI.frac(F(j,10000))*PI
        sin_point(x.lo,x.hi);cos_point(x.lo,x.hi)
    print('10k point trig sec',time.time()-t)
if __name__=='__main__':main()
