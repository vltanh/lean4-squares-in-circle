#!/usr/bin/env python3
"""
Exact rational replay for the branch where both D--W and D--S use D's
secondary axis.

This is a terminal certificate for the reduced n=6 verifier, not by itself the
unrestricted theorem.

Reframed angle domain:

    |theta_N| <= 1/5
    |theta_W| <= 1/5
     1/6 <= theta_S <= 1/2
    |eps_D|   <= 1/6

Required axes:

    C -> N : common vertical
    S -> C : common vertical
    D -> W : D secondary, directed northwest
    D -> S : the same unsigned D-secondary axis, directed southeast
    W -> N : any of the four source edge axes

The fixed rational dual is

    lambda_N = 1/50
    lambda_W = 12/25
    lambda_S = 12/25
    lambda_D = 1/50

    mu_CN = mu_SC = 3/50
    mu_WN = 1/25
    mu_DW = 43/25
    mu_DS = 17/10.

All certificate arithmetic uses fractions.Fraction.  The only irrational
constant is 1/sqrt(2), enclosed by the checked rational bracket below.
"""
from fractions import Fraction as F

Q0 = F(142559, 50000)
HLO = F(70710678, 10**8)
HHI = F(70710679, 10**8)
assert 2 * HLO * HLO < 1
assert 1 < 2 * HHI * HHI


class I:
    __slots__ = ("lo", "hi")

    def __init__(self, lo, hi=None):
        self.lo = F(lo)
        self.hi = F(lo if hi is None else hi)
        assert self.lo <= self.hi

    def __add__(self, other):
        other = as_i(other)
        return I(self.lo + other.lo, self.hi + other.hi)

    __radd__ = __add__

    def __neg__(self):
        return I(-self.hi, -self.lo)

    def __sub__(self, other):
        return self + (-as_i(other))

    def __rsub__(self, other):
        return as_i(other) - self

    def __mul__(self, other):
        other = as_i(other)
        xs = (
            self.lo * other.lo,
            self.lo * other.hi,
            self.hi * other.lo,
            self.hi * other.hi,
        )
        return I(min(xs), max(xs))

    __rmul__ = __mul__

    def sq(self):
        if self.lo <= 0 <= self.hi:
            return I(0, max(self.lo * self.lo, self.hi * self.hi))
        return I(
            min(self.lo * self.lo, self.hi * self.hi),
            max(self.lo * self.lo, self.hi * self.hi),
        )

    def abs(self):
        if self.lo <= 0 <= self.hi:
            return I(0, max(-self.lo, self.hi))
        return I(min(abs(self.lo), abs(self.hi)),
                 max(abs(self.lo), abs(self.hi)))


def as_i(x):
    return x if isinstance(x, I) else I(x)


H = I(HLO, HHI)


def sin_point_pos(x):
    x = F(x)
    assert 0 <= x <= F(3, 4)
    lo = x - x**3 / 6 + x**5 / 120 - x**7 / 5040
    hi = x - x**3 / 6 + x**5 / 120
    return lo, hi


def sin_point(x):
    x = F(x)
    if x >= 0:
        return sin_point_pos(x)
    lo, hi = sin_point_pos(-x)
    return -hi, -lo


def cos_point_pos(x):
    x = F(x)
    assert 0 <= x <= F(3, 4)
    lo = 1 - x**2 / 2 + x**4 / 24 - x**6 / 720
    hi = 1 - x**2 / 2 + x**4 / 24
    return lo, hi


def sin_i(x):
    lo, _ = sin_point(x.lo)
    _, hi = sin_point(x.hi)
    return I(lo, hi)


def cos_i(x):
    amin = F(0) if x.lo <= 0 <= x.hi else min(abs(x.lo), abs(x.hi))
    amax = max(abs(x.lo), abs(x.hi))
    lo, _ = cos_point_pos(amax)
    _, hi = cos_point_pos(amin)
    return I(lo, hi)


def cs(x):
    return cos_i(x), sin_i(x)


def vadd(a, b):
    return a[0] + b[0], a[1] + b[1]


def vsub(a, b):
    return a[0] - b[0], a[1] - b[1]


def vscale(c, a):
    return c * a[0], c * a[1]


def vsq(a):
    return a[0].sq() + a[1].sq()


LN = F(1, 50)
LW = F(12, 25)
LS = F(12, 25)
LD = F(1, 50)
assert LN + LW + LS + LD == 1

MU1 = F(3, 50)
MU4 = MU1
MU5 = F(1, 25)
MU7 = F(43, 25)
MU8 = F(17, 10)


def lower_bound(theta_n, theta_w, theta_s, eps_d, source_wn):
    cN, sN = cs(theta_n)
    cW, sW = cs(theta_w)
    cS, sS = cs(theta_s)
    cD, sD = cs(eps_d)

    n1 = (I(0), I(1))
    n4 = n1

    if source_wn == "Wp":
        n5 = (cW, sW)
    elif source_wn == "Ws":
        n5 = (-sW, cW)
    elif source_wn == "Np":
        n5 = (cN, sN)
    elif source_wn == "Ns":
        n5 = (-sN, cN)
    else:
        raise ValueError(source_wn)

    # D secondary directed D -> W.
    n7 = (-H * (cD + sD), H * (cD - sD))
    # Same unsigned axis, opposite direction D -> S.
    n8 = (-n7[0], -n7[1])

    gN = vadd(vscale(MU1, n1), vscale(MU5, n5))
    gW = vadd(vscale(-MU5, n5), vscale(MU7, n7))
    gS = vadd(vscale(-MU4, n4), vscale(MU8, n8))
    gD = vadd(vscale(-MU7, n7), vscale(-MU8, n8))

    mN = (F(1, 2) * (cN - sN), F(1, 2) * (sN + cN))
    mW = (F(1, 2) * (-cW - sW), F(1, 2) * (-sW + cW))
    mS = (F(1, 2) * (cS + sS), F(1, 2) * (sS - cS))
    mD = (H * sD, -H * cD)

    h1 = I(F(1, 2)) + F(1, 2) * (cN + sN.abs())
    h4 = I(F(1, 2)) + F(1, 2) * (cS + sS.abs())

    d5 = theta_n - theta_w
    c5, s5 = cs(d5)
    h5 = I(F(1, 2)) + F(1, 2) * (c5 + s5.abs())

    d7 = eps_d - theta_w
    c7, _ = cs(d7)
    h7 = I(F(1, 2)) + H * c7

    d8 = eps_d - theta_s
    c8, _ = cs(d8)
    h8 = I(F(1, 2)) + H * c8

    out = (
        I(F(1, 2))
        + MU1 * h1
        + MU4 * h4
        + MU5 * h5
        + MU7 * h7
        + MU8 * h8
    )

    for lam, m, g in (
        (LN, mN, gN),
        (LW, mW, gW),
        (LS, mS, gS),
        (LD, mD, gD),
    ):
        z = vsub(vscale(2 * lam, m), g)
        out = out - F(1, 4) / lam * vsq(z)

    return out


ROOT = (
    I(-F(1, 5), F(1, 5)),
    I(-F(1, 5), F(1, 5)),
    I(F(1, 6), F(1, 2)),
    I(-F(1, 6), F(1, 6)),
)


def split_box(box, k):
    x = box[k]
    m = (x.lo + x.hi) / 2
    a = list(box)
    b = list(box)
    a[k] = I(x.lo, m)
    b[k] = I(m, x.hi)
    return tuple(a), tuple(b)


def replay(source_wn):
    stack = [(ROOT, 0)]
    visited = 0
    leaves = 0
    deepest = 0

    while stack:
        box, depth = stack.pop()
        visited += 1
        deepest = max(deepest, depth)

        bound = lower_bound(*box, source_wn)
        if bound.lo > Q0:
            leaves += 1
            continue

        assert depth < 32, (source_wn, depth, bound.lo, box)

        widths = [x.hi - x.lo for x in box]
        k = max(range(4), key=lambda i: widths[i])
        a, b = split_box(box, k)
        stack.append((a, depth + 1))
        stack.append((b, depth + 1))

    return visited, leaves, deepest


def main():
    for source in ("Wp", "Ws", "Np", "Ns"):
        visited, leaves, deepest = replay(source)
        print(
            source,
            "visited=", visited,
            "certified_leaves=", leaves,
            "max_depth=", deepest,
        )


if __name__ == "__main__":
    main()
