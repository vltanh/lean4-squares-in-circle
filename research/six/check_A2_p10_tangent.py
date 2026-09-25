#!/usr/bin/env python3
"""Exact scalar checks for the A2.1 pattern-10 tangent coercivity lemma."""
from fractions import Fraction as F

from n6_exact_intervals import candidate_bounds

h,s,t,d,_ = candidate_bounds(bits=120)
r = (s+F(1,2))/(s+F(3,2))
k = (t+F(1,2))/(F(3,2)-s)
m = (1+r)*k
L = (s+F(1,2))+(t+F(1,2))-m*d
q = (s+F(1,2))-(t+F(1,2))*r
c = F(1,3)

checks = {
    "q > 0": q.lo,
    "r > 1/3": r.lo-c,
    "L-r > 0": (L-r).lo,
    "1-L > 0": (1-L).lo,
    "1+r-L > 1/3": (1+r-L).lo-c,
    "1-q > 1/3": (1-q).lo-c,
    "L-q > 1/3": (L-q).lo-c,
}
for name,margin in checks.items():
    assert margin > 0, (name,margin)
    print(name,"margin >",float(margin))

print("A2.1 pattern-10 tangent coercivity checks: PASS")


# Uniform tangent along |eps| <= 1/4.
from n6_exact_intervals import sqrt_bounds
qstar = 2*s*s+4*s+F(5,2)
rad = qstar-F(1,4)
rho_lo = sqrt_bounds(rad.lo,bits=120).lo-F(1,2)
rho_hi = sqrt_bounds(rad.hi,bits=120).hi-F(1,2)
mh = m*h
assert mh.hi < 1
assert rho_lo > 1
assert rho_hi < F(9,8)
assert F(1,3)-F(17,128) > F(1,5)
print("m*h < 1 margin >",float(1-mh.hi))
print("rho in (1,9/8) margins >",float(rho_lo-1),float(F(9,8)-rho_hi))
print("uniform eps-strip tangent constant > 1/5: PASS")
