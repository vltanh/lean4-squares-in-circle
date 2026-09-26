#!/usr/bin/env python3
"""
Exact rational checks for the search ceiling Q0 = 2.85118.

The mathematical bridge is:

  h = 1/sqrt(2)
  f_h(x) = x^2 - ((1466+1940h)/267)x + (327+432h)/712.

The candidate parameter s is the small positive root of f_h.  We check:

  * 70710678/1e8 < h < 70710679/1e8;
  * f_h(84246/1e6) < 0, while f_h(0) > 0;
  * q(x)=2x^2+4x+5/2 is increasing for x>0;
  * q(84246/1e6) < 142559/50000.

Hence s < 84246/1e6 and q_* < Q0.

Only Fraction arithmetic is used below.
"""

from fractions import Fraction as F

HLO = F(70710678, 10**8)
HHI = F(70710679, 10**8)
SU = F(84246, 10**6)
Q0 = F(142559, 50000)


def A(h):
    return (F(1466) + F(1940) * h) / F(267)


def B(h):
    return (F(327) + F(432) * h) / F(712)


def poly(x, h):
    return x * x - A(h) * x + B(h)


assert 2 * HLO * HLO < 1
assert 1 < 2 * HHI * HHI

# The coefficient of h in f_h(SU) is negative, so h >= HLO gives
# f_h(SU) <= f_HLO(SU).
h_coeff = -F(1940, 267) * SU + F(432, 712)
assert h_coeff < 0
assert poly(SU, HLO) == F(-190711399, 55625000000000)
assert poly(SU, HLO) < 0
assert B(HLO) > 0

q_upper = 2 * SU * SU + 4 * SU + F(5, 2)
assert q_upper == F(356397347129, 125000000000)
assert Q0 - q_upper == F(152871, 125000000000)
assert q_upper < Q0

print("h bracket: OK")
print("root upper bound s < 84246/1e6: arithmetic checks OK")
print("q_* < 142559/50000 =", float(Q0))
print("rational margin over q(84246/1e6):", Q0 - q_upper)
