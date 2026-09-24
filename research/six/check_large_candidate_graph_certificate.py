#!/usr/bin/env python3
"""
Exact rational replay for the large-angle candidate contact graph.

This terminal certificate covers the region

    1/6 <= theta_E,theta_N,theta_W,theta_S <= 1/3
    |eps_D| <= 1/8,

with the candidate graph of separator axes:

    C -> N : common vertical
    C -> E : common horizontal
    W -> C : common horizontal
    S -> C : common vertical
    W -> N : horizontal supplied by W or N
    S -> E : vertical supplied by S or E
    D -> W : W vertical
    D -> S : S horizontal.

The fixed rational stress is a rounded version of the exact candidate stress.
All replay arithmetic uses fractions.Fraction and elementary alternating
Taylor enclosures.
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


def sin_pos(x):
    x = F(x)
    assert 0 <= x <= F(3, 4)
    return (
        x - x**3 / 6 + x**5 / 120 - x**7 / 5040,
        x - x**3 / 6 + x**5 / 120,
    )


def sin_point(x):
    x = F(x)
    if x >= 0:
        return sin_pos(x)
    a, b = sin_pos(-x)
    return -b, -a


def cos_pos(x):
    x = F(x)
    assert 0 <= x <= F(3, 4)
    return (
        1 - x**2 / 2 + x**4 / 24 - x**6 / 720,
        1 - x**2 / 2 + x**4 / 24,
    )


def sin_i(x):
    a, _ = sin_point(x.lo)
    _, b = sin_point(x.hi)
    return I(a, b)


def cos_i(x):
    mn = F(0) if x.lo <= 0 <= x.hi else min(abs(x.lo), abs(x.hi))
    mx = max(abs(x.lo), abs(x.hi))
    a, _ = cos_pos(mx)
    _, b = cos_pos(mn)
    return I(a, b)


def cs(x):
    return cos_i(x), sin_i(x)


def add(a, b):
    return a[0] + b[0], a[1] + b[1]


def sub(a, b):
    return a[0] - b[0], a[1] - b[1]


def scale(k, a):
    return k * a[0], k * a[1]


def sqv(a):
    return a[0].sq() + a[1].sq()


LE = F(105, 1000)
LN = F(212, 1000)
LW = F(205, 1000)
LS = F(281, 1000)
LD = F(197, 1000)
assert LE + LN + LW + LS + LD == 1

M1 = F(672, 1000)
M2 = F(334, 1000)
M5 = F(248, 1000)
M6 = F(123, 1000)
M7 = F(378, 1000)
M8 = F(517, 1000)


def lower(te, tn, tw, ts, ed, src5, src6):
    ce, se = cs(te)
    cn, sn = cs(tn)
    cw, sw = cs(tw)
    cS, sS = cs(ts)
    cd, sd = cs(ed)

    nx = (I(1), I(0))
    ny = (I(0), I(1))

    n5 = (cw, sw) if src5 == "W" else (cn, sn)
    n6 = (-sS, cS) if src6 == "S" else (-se, ce)
    n7 = (-sw, cw)
    n8 = (cS, sS)

    G = {}
    G["E"] = add(scale(M2, nx), scale(M6, n6))
    G["N"] = add(scale(M1, ny), scale(M5, n5))
    G["W"] = add(scale(-M2, nx), add(scale(-M5, n5), scale(M7, n7)))
    G["S"] = add(scale(-M1, ny), add(scale(-M6, n6), scale(M8, n8)))
    G["D"] = add(scale(-M7, n7), scale(-M8, n8))

    me = (F(1, 2) * (ce - se), F(1, 2) * (se + ce))
    mn = (F(1, 2) * (cn - sn), F(1, 2) * (sn + cn))
    mw = (F(1, 2) * (-cw - sw), F(1, 2) * (-sw + cw))
    ms = (F(1, 2) * (cS + sS), F(1, 2) * (sS - cS))
    md = (H * sd, -H * cd)

    def ch(c, s):
        return I(F(1, 2)) + F(1, 2) * (c + s.abs())

    h1 = ch(cn, sn)
    h2 = ch(ce, se)
    h3 = ch(cw, sw)
    h4 = ch(cS, sS)

    c5, s5 = cs(tn - tw)
    h5 = ch(c5, s5)

    c6, s6 = cs(te - ts)
    h6 = ch(c6, s6)

    c7, _ = cs(ed - tw)
    h7 = I(F(1, 2)) + H * c7

    c8, _ = cs(ed - ts)
    h8 = I(F(1, 2)) + H * c8

    out = (
        I(F(1, 2))
        + M1 * h1
        + M2 * h2
        + M2 * h3
        + M1 * h4
        + M5 * h5
        + M6 * h6
        + M7 * h7
        + M8 * h8
    )

    for lam, m, g in (
        (LE, me, G["E"]),
        (LN, mn, G["N"]),
        (LW, mw, G["W"]),
        (LS, ms, G["S"]),
        (LD, md, G["D"]),
    ):
        z = sub(scale(2 * lam, m), g)
        out = out - F(1, 4) / lam * sqv(z)

    return out


ROOT = (
    I(F(1, 6), F(1, 3)),
    I(F(1, 6), F(1, 3)),
    I(F(1, 6), F(1, 3)),
    I(F(1, 6), F(1, 3)),
    I(-F(1, 8), F(1, 8)),
)


def split(box, k):
    x = box[k]
    m = (x.lo + x.hi) / 2
    a = list(box)
    b = list(box)
    a[k] = I(x.lo, m)
    b[k] = I(m, x.hi)
    return tuple(a), tuple(b)


def replay(src5, src6):
    stack = [(ROOT, 0)]
    visited = 0
    leaves = 0
    deepest = 0

    while stack:
        box, depth = stack.pop()
        visited += 1
        deepest = max(deepest, depth)

        bound = lower(*box, src5, src6)
        if bound.lo > Q0:
            leaves += 1
            continue

        assert depth < 28, (src5, src6, depth, bound.lo, box)

        widths = [x.hi - x.lo for x in box]
        k = max(range(5), key=lambda i: widths[i])
        a, b = split(box, k)
        stack.append((a, depth + 1))
        stack.append((b, depth + 1))

    return visited, leaves, deepest


def main():
    for src5 in ("W", "N"):
        for src6 in ("S", "E"):
            visited, leaves, deepest = replay(src5, src6)
            print(
                src5,
                src6,
                "visited=", visited,
                "certified_leaves=", leaves,
                "max_depth=", deepest,
            )


if __name__ == "__main__":
    main()
