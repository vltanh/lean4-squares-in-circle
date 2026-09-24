#!/usr/bin/env python3
from __future__ import annotations
from dataclasses import dataclass
from fractions import Fraction as F
from math import isqrt

# Exact rational interval arithmetic for the eventual n=6 replay checker.

@dataclass(frozen=True)
class QI:
    lo: F
    hi: F
    def __post_init__(self):
        if self.lo > self.hi:
            raise ValueError((self.lo,self.hi))
    @staticmethod
    def point(x):
        x=F(x); return QI(x,x)
    def __neg__(self): return QI(-self.hi,-self.lo)
    def __add__(self,o):
        o=q(o); return QI(self.lo+o.lo,self.hi+o.hi)
    __radd__=__add__
    def __sub__(self,o): return self+(-q(o))
    def __rsub__(self,o): return q(o)-self
    def __mul__(self,o):
        o=q(o)
        xs=[self.lo*o.lo,self.lo*o.hi,self.hi*o.lo,self.hi*o.hi]
        return QI(min(xs),max(xs))
    __rmul__=__mul__
    def inv(self):
        if self.lo <= 0 <= self.hi: raise ZeroDivisionError
        return QI(1/self.hi,1/self.lo)
    def __truediv__(self,o): return self*q(o).inv()
    def __rtruediv__(self,o): return q(o)/self
    def abs(self):
        if self.lo <= 0 <= self.hi: return QI(F(0),max(-self.lo,self.hi))
        return QI(min(abs(self.lo),abs(self.hi)),max(abs(self.lo),abs(self.hi)))
    def sq(self):
        a=self.abs(); return QI(a.lo*a.lo,a.hi*a.hi)
    def intersect(self,o):
        o=q(o); lo=max(self.lo,o.lo); hi=min(self.hi,o.hi)
        return None if lo>hi else QI(lo,hi)

def q(x): return x if isinstance(x,QI) else QI.point(x)

def sqrt_bounds(x:F,bits:int=96)->QI:
    if x<0: raise ValueError
    if x==0: return QI.point(0)
    scale=1<<(2*bits)
    k=isqrt((x.numerator*scale)//x.denominator)
    lo=F(k,1<<bits)
    while (lo*lo)>x:
        k-=1; lo=F(k,1<<bits)
    hi=F(k+1,1<<bits)
    while hi*hi < x:
        k+=1; hi=F(k+1,1<<bits)
    return QI(lo,hi)

def atan_inv_bounds(m:int,nterms:int)->QI:
    # Alternating series for atan(1/m), bounded by two consecutive partial sums.
    s=F(0)
    for k in range(nterms):
        term=F(1,(2*k+1)*(m**(2*k+1)))
        s += term if k%2==0 else -term
    k=nterms
    nxt=F(1,(2*k+1)*(m**(2*k+1)))
    nxt = nxt if k%2==0 else -nxt
    t=s+nxt
    return QI(min(s,t),max(s,t))

def pi_bounds()->QI:
    # Machin: pi = 16 atan(1/5) - 4 atan(1/239).
    a=atan_inv_bounds(5,24)
    b=atan_inv_bounds(239,8)
    return 16*a-4*b

PI=pi_bounds()

# Taylor bounds for x in [0, pi/2]. The true value lies between consecutive
# alternating partial sums.
def sin_point_bounds(x:F,n:int=12)->QI:
    s=F(0)
    term=x
    for k in range(n+1):
        if k>0:
            term = -term*x*x/F((2*k)*(2*k+1))
        s += term
    term_next = -term*x*x/F((2*n+2)*(2*n+3))
    t=s+term_next
    return QI(min(s,t),max(s,t))

def cos_point_bounds(x:F,n:int=12)->QI:
    s=F(0); term=F(1)
    for k in range(n+1):
        if k>0:
            term = -term*x*x/F((2*k-1)*(2*k))
        s += term
    term_next = -term*x*x/F((2*n+1)*(2*n+2))
    t=s+term_next
    return QI(min(s,t),max(s,t))

def floor_fraction(x:F)->int:
    return x.numerator//x.denominator

def sincos_pi_point(r:F)->tuple[QI,QI]:
    # Reduce r*pi by exact quarter turns. Let j=floor(2r), u=r-j/2 in [0,1/2).
    j=floor_fraction(2*r)
    u=r-F(j,2)
    xlo=u*PI.lo; xhi=u*PI.hi
    sb_lo=sin_point_bounds(xlo).lo
    sb_hi=sin_point_bounds(xhi).hi
    cb_lo=cos_point_bounds(xhi).lo
    cb_hi=cos_point_bounds(xlo).hi
    s=QI(sb_lo,sb_hi); c=QI(cb_lo,cb_hi)
    k=j%4
    if k==0: return s,c
    if k==1: return c,-s
    if k==2: return -s,-c
    return -c,s

def has_half_integer(a:F,b:F)->list[int]:
    # j such that j/2 in [a,b]
    j0=(2*a.numerator + a.denominator-1)//a.denominator
    j1=(2*b.numerator)//b.denominator
    return list(range(j0,j1+1))

def sin_pi_interval(a:F,b:F)->QI:
    if a>b: raise ValueError
    if b-a>=2: return QI(F(-1),F(1))
    sa,_=sincos_pi_point(a); sb,_=sincos_pi_point(b)
    lo=min(sa.lo,sb.lo); hi=max(sa.hi,sb.hi)
    for j in has_half_integer(a,b):
        if j%2:
            v=F(1) if (j%4)==1 else F(-1)
            lo=min(lo,v); hi=max(hi,v)
    return QI(lo,hi)

def cos_pi_interval(a:F,b:F)->QI:
    if a>b: raise ValueError
    if b-a>=2: return QI(F(-1),F(1))
    _,ca=sincos_pi_point(a); _,cb=sincos_pi_point(b)
    lo=min(ca.lo,cb.lo); hi=max(ca.hi,cb.hi)
    # cos extrema at integer r = j/2 with j even.
    for j in has_half_integer(a,b):
        if j%2==0:
            v=F(1) if (j%4)==0 else F(-1)
            lo=min(lo,v); hi=max(hi,v)
    return QI(lo,hi)

def candidate_bounds(bits=96):
    # Rigorous enclosure of the algebraic candidate from exact formulas.
    rt2=sqrt_bounds(F(2),bits)
    h=1/rt2
    A=(F(1466)+F(1940)*h)/F(267)
    B=(F(327)+F(432)*h)/F(712)
    disc=A*A-4*B
    sd=QI(sqrt_bounds(disc.lo,bits).lo,sqrt_bounds(disc.hi,bits).hi)
    s=2*B/(A+sd)
    t=(-F(20)+F(30)*h)*s+F(7,2)-F(9,2)*h
    d=F(1,2)+h-t
    qstar=2*s*s+4*s+F(5,2)
    return h,s,t,d,qstar

def main():
    print('pi width=', float(PI.hi-PI.lo))
    dec_lo=F(3141592653589793238462643383279,10**30)
    dec_hi=F(3141592653589793238462643383280,10**30)
    print('pi inside decimal sanity bracket?',dec_lo<PI.lo<PI.hi<dec_hi)
    for r in [F(0),F(1,12),F(1,4),F(1,2),F(3,4),F(1),F(5,4),F(7,4)]:
        s,c=sincos_pi_point(r)
        print('r',r,'sin',float(s.lo),float(s.hi),'cos',float(c.lo),float(c.hi))
    h,s,t,d,qstar=candidate_bounds()
    print('h',float(h.lo),float(h.hi))
    print('s',float(s.lo),float(s.hi))
    print('t',float(t.lo),float(t.hi))
    print('d',float(d.lo),float(d.hi))
    print('q',float(qstar.lo),float(qstar.hi),'width',float(qstar.hi-qstar.lo))
    QBAR=F(142559,50000) # 2.85118
    print('qstar < 2.85118?',qstar.hi<QBAR,'margin',float(QBAR-qstar.hi))
    assert dec_lo < PI.lo < PI.hi < dec_hi
    assert qstar.hi<QBAR
    assert sin_pi_interval(F(1,4),F(3,4)).hi==1
    assert cos_pi_interval(F(3,4),F(5,4)).lo==-1
    print('self-test: OK')

if __name__=='__main__': main()
