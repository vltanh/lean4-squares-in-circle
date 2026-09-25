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
