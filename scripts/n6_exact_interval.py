#!/usr/bin/env python3
"""
Exact rational arithmetic primitives for the n=6 finite verifier.

This file deliberately avoids libm for every statement intended to be part of
the eventual replayable certificate:

* pi is enclosed by Machin's formula with alternating arctangent series;
* sin/cos at rational points are enclosed by Taylor polynomials with a
  Lagrange remainder;
* interval sin/cos add the only possible critical values using the rational
  pi enclosure;
* the irrational candidate q_* is proved to satisfy q_* < 2.85118 from the
  defining quadratic and a two-sided rational enclosure of 1/sqrt(2).

The fast branch-and-bound driver may still use floating point for discovery.
A final certificate should be replayed through routines of this kind.
"""
from __future__ import annotations

from fractions import Fraction as Q
from math import factorial
from typing import Tuple

Interval = Tuple[Q, Q]


def atan_bounds(x: Q, terms: int = 18) -> Interval:
    """Alternating-series enclosure for atan(x), 0 <= x <= 1."""
    assert 0 <= x <= 1
    s = Q(0)
    for k in range(terms):
        term = x ** (2 * k + 1) / Q(2 * k + 1)
        s += term if k % 2 == 0 else -term
    nxt = x ** (2 * terms + 1) / Q(2 * terms + 1)
    # The next term has positive sign iff terms is even.
    return (s, s + nxt) if terms % 2 == 0 else (s - nxt, s)


def pi_bounds() -> Interval:
    """Machin: pi = 16 atan(1/5) - 4 atan(1/239)."""
    a5 = atan_bounds(Q(1, 5))
    a239 = atan_bounds(Q(1, 239))
    return 16 * a5[0] - 4 * a239[1], 16 * a5[1] - 4 * a239[0]


PI_LO, PI_HI = pi_bounds()


def sin_point_bounds(x: Q, m: int = 24) -> Interval:
    """Taylor enclosure for sin(x), valid for every rational x."""
    s = Q(0)
    for k in range(m + 1):
        term = x ** (2 * k + 1) / Q(factorial(2 * k + 1))
        s += term if k % 2 == 0 else -term
    rem = abs(x) ** (2 * m + 2) / Q(factorial(2 * m + 2))
    return s - rem, s + rem


def cos_point_bounds(x: Q, m: int = 24) -> Interval:
    """Taylor enclosure for cos(x), valid for every rational x."""
    s = Q(0)
    for k in range(m + 1):
        term = x ** (2 * k) / Q(factorial(2 * k))
        s += term if k % 2 == 0 else -term
    rem = abs(x) ** (2 * m + 1) / Q(factorial(2 * m + 1))
    return s - rem, s + rem


def k_pi_over_two(k: int) -> Interval:
    """Rational enclosure for k*pi/2, with sign handled outward."""
    if k >= 0:
        return Q(k, 2) * PI_LO, Q(k, 2) * PI_HI
    return Q(k, 2) * PI_HI, Q(k, 2) * PI_LO


def intersects(a: Interval, b: Interval) -> bool:
    return max(a[0], b[0]) <= min(a[1], b[1])


def sin_interval(x: Interval, m: int = 24) -> Interval:
    """
    Exact rational enclosure of sin on x.

    The intended verifier angles lie in a small fixed range.  The loop below
    covers every odd k with k*pi/2 in [-21*pi/2, 21*pi/2], far beyond that
    range.  Widen this finite loop if the certificate format is ever extended.
    """
    sl = sin_point_bounds(x[0], m)
    su = sin_point_bounds(x[1], m)
    lo, hi = min(sl[0], su[0]), max(sl[1], su[1])
    for k in range(-21, 22, 2):
        critical = k_pi_over_two(k)
        if intersects(x, critical):
            value = Q(1) if k % 4 == 1 else Q(-1)
            lo, hi = min(lo, value), max(hi, value)
    return lo, hi


def cos_interval(x: Interval, m: int = 24) -> Interval:
    """Exact rational enclosure of cos on x."""
    cl = cos_point_bounds(x[0], m)
    cu = cos_point_bounds(x[1], m)
    lo, hi = min(cl[0], cu[0]), max(cl[1], cu[1])
    for j in range(-10, 11):
        k = 2 * j
        critical = k_pi_over_two(k)
        if intersects(x, critical):
            value = Q(1) if j % 2 == 0 else Q(-1)
            lo, hi = min(lo, value), max(hi, value)
    return lo, hi


# ---------------------------------------------------------------------------
# Exact rational bridge from the algebraic candidate to the rational search
# radius Q0 = 2.85118.
# ---------------------------------------------------------------------------

Q0 = Q(142559, 50000)
H_LO = Q(70710678, 10**8)
H_HI = Q(70710679, 10**8)
S_UP = Q(84246, 10**6)


def check_candidate_below_q0() -> dict:
    """
    Verify q_* < Q0 using only rational arithmetic.

    Let h=1/sqrt(2) and
      p(x)=x^2-Ax+B,
      A=(1466+1940h)/267,
      B=(327+432h)/712.
    The candidate s is the smaller root.

    H_LO < h < H_HI follows by squaring.  At r=S_UP, p(r)<0; since
    r<A/2, r lies strictly between the two roots, so s<r.  Finally
    q(s)=2s^2+4s+5/2 is increasing for s>0 and q(r)<Q0.
    """
    assert H_LO * H_LO < Q(1, 2) < H_HI * H_HI

    r = S_UP
    coeff_h = -r * Q(1940, 267) + Q(432, 712)
    const = r * r - r * Q(1466, 267) + Q(327, 712)
    assert coeff_h < 0

    # h > H_LO and coeff_h<0, so p(r) < this rational upper bound.
    p_upper = const + coeff_h * H_LO
    assert p_upper < 0

    # A > 1466/267 > 5, hence r < A/2.
    assert r < Q(5, 2)

    q_r = 2 * r * r + 4 * r + Q(5, 2)
    assert q_r < Q0

    return {
        "pi_width_num": (PI_HI - PI_LO).numerator,
        "pi_width_den": (PI_HI - PI_LO).denominator,
        "h_lower_square_margin": str(Q(1, 2) - H_LO * H_LO),
        "h_upper_square_margin": str(H_HI * H_HI - Q(1, 2)),
        "quadratic_at_s_upper_bound": str(p_upper),
        "q0_minus_q_at_s_upper": str(Q0 - q_r),
    }


def self_test() -> None:
    report = check_candidate_below_q0()

    # A few exact enclosure smoke tests, using only rational input.
    for x in (Q(0), Q(1, 10), Q(1), Q(3), Q(6)):
        s = sin_point_bounds(x)
        c = cos_point_bounds(x)
        assert s[0] <= s[1]
        assert c[0] <= c[1]

    assert PI_LO < Q(22, 7)
    assert PI_HI > Q(333, 106)

    print("exact n=6 interval core: PASS")
    for k, v in report.items():
        print(f"{k}: {v}")


if __name__ == "__main__":
    self_test()
