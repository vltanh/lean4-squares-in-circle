#!/usr/bin/env python3
"""Exact scalar checks for the hand reduction of the alternate D--W stress.

This replaces a multidimensional interval replay by nine fixed inequalities.
Only fractions.Fraction and alternating Taylor bounds are used.
"""
from fractions import Fraction as F
from math import factorial


class I:
    def __init__(self, lo, hi=None):
        self.lo = F(lo)
        self.hi = F(lo if hi is None else hi)
        assert self.lo <= self.hi

    def __add__(self, other):
        other = iv(other)
        return I(self.lo + other.lo, self.hi + other.hi)

    __radd__ = __add__

    def __neg__(self):
        return I(-self.hi, -self.lo)

    def __sub__(self, other):
        return self + (-iv(other))

    def __rsub__(self, other):
        return iv(other) - self

    def __mul__(self, other):
        other = iv(other)
        xs = (
            self.lo * other.lo,
            self.lo * other.hi,
            self.hi * other.lo,
            self.hi * other.hi,
        )
        return I(min(xs), max(xs))

    __rmul__ = __mul__


def iv(x):
    return x if isinstance(x, I) else I(x)


def sinb(x, n=8):
    x = F(x)
    assert 0 <= x <= F(3, 4)
    terms = [
        F((-1) ** k) * x ** (2 * k + 1) / F(factorial(2 * k + 1))
        for k in range(n + 2)
    ]
    s = sum(terms[: n + 1], F(0))
    t = s + terms[n + 1]
    return I(min(s, t), max(s, t))


def cosb(x, n=8):
    x = F(x)
    assert 0 <= x <= F(3, 4)
    terms = [
        F((-1) ** k) * x ** (2 * k) / F(factorial(2 * k))
        for k in range(n + 2)
    ]
    s = sum(terms[: n + 1], F(0))
    t = s + terms[n + 1]
    return I(min(s, t), max(s, t))


def positive(name, x):
    assert x.lo > 0, (name, x.lo, x.hi)
    print(name, ">", float(x.lo))


def negative(name, x):
    assert x.hi < 0, (name, x.lo, x.hi)
    print(name, "<", float(x.hi))


H = I(F(70710678, 10**8), F(70710679, 10**8))
a = F(1, 6)
b = F(2, 5)
half = F(1, 2)

Q = F(949, 1000)
R = F(277, 1000)
T = F(262873, 562000)
P = F(38909, 31000)

A = F(41697, 23000) * H
B = F(7749, 23000) * H
C = F(78993, 93200) * H
E = F(167031, 466000) * H

K = F(980542331731, 840280482000)
Q0 = F(142559, 50000)

sa, ca = sinb(a), cosb(a)
sb, cb = sinb(b), cosb(b)
sab, cab = sinb(a + b), cosb(a + b)
s23, c23 = sinb(F(2, 3)), cosb(F(2, 3))
s1730, c1730 = sinb(F(17, 30)), cosb(F(17, 30))
sh, ch = sinb(half), cosb(half)

positive("n_positive_derivative", Q * (ca - sa) - R)
positive(
    "n_negative_endpoint_gap",
    Q * (ca - 1) + R * ((cab + sab) - (cb + sb)),
)

positive(
    "e_term_positive",
    A * c23 - B * s23 + C * c1730 - E * s1730,
)
positive("e_endpoint_gap_factor", A * sa + B * ca - E)

negative(
    "w_second_derivative_upper",
    -R * cb + (T - R) * sb - C * cab,
)
negative("w_derivative_at_zero", (R - T) - C * sa + E * ca)

negative(
    "s_second_derivative_upper",
    -A * cosb(a + half) + B * sinb(a + half) - Q * ch,
)


def fs(x):
    return A * cosb(a + x) - B * sinb(a + x) + P * sinb(x) + Q * cosb(x)


positive("s_endpoint_gap", fs(half) - fs(a))

Fend = (
    A * cosb(2 * a)
    - B * sinb(2 * a)
    + C * cosb(a + b)
    + E * sinb(a + b)
    + Q
    + R * (cb + sb)
    + P * sa
    - T * sb
    + Q * ca
    - K
)
positive("final_margin", Fend - Q0)

print("hand scalar checks: PASS")
