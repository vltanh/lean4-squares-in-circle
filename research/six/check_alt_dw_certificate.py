#!/usr/bin/env python3
"""
Exact rational replay for one alternate n=6 separator branch.

This is NOT the unrestricted n=6 proof.  It certifies one terminal region used
by the reduced verifier.

Geometric hypotheses for this terminal rule (angles are radians):

  |theta_N| <= 1/6
  |theta_W| <= 1/4
   1/6 <= theta_S <= 1/2
  |eps_D|   <= 1/6

where N,W,S are deviations from the common aligned frame and D has frame
pi/4 + eps_D.

Required separating axes:
  C -> N : common vertical axis
  S -> C : common vertical axis
  W -> N : horizontal axis supplied by W OR by N
  D -> W : D's secondary axis (direction 3*pi/4 + eps_D)
  D -> S : S's horizontal axis

No E-square inequality is used.

The fixed rational dual certificate is

  lambda_N = 281/1000
  lambda_W = 233/1000
  lambda_S = 279/1000
  lambda_D = 207/1000

  mu_CN = mu_SC = 949/1000
  mu_WN = 277/1000
  mu_DW = 603/1000
  mu_DS = 738/1000.

The selected containment vertices are
  N : ( 1/2,  1/2)
  W : (-1/2,  1/2)
  S : ( 1/2, -1/2)
  D : the global reference vertex (0,-1/sqrt(2)),
      rotated by eps_D.

For a fixed angle tuple, weighted containment plus the five separator
inequalities gives

  R^2 >= 1/2 + sum_e mu_e H_e
             - sum_i |2 lambda_i m_i - G_i|^2/(4 lambda_i).

All interval arithmetic below is exact Fraction arithmetic.  Trigonometric
enclosures use the standard alternating Taylor bounds on |x| <= 3/4:

  x-x^3/6+x^5/120-x^7/5040 <= sin x
      <= x-x^3/6+x^5/120,

  1-x^2/2+x^4/24-x^6/720 <= cos x
      <= 1-x^2/2+x^4/24.

The replay recursively bisects only rational angle intervals.  It proves that
the displayed lower bound is strictly greater than

  Q0 = 142559/50000 = 2.85118,

for both possible sources of the W--N horizontal separator.
"""

from fractions import Fraction as F

Q0 = F(142559, 50000)

# Exact rational enclosure of 1/sqrt(2).  The two assertions below prove it.
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
    # sin is increasing throughout [-3/4,3/4].
    lo, _ = sin_point(x.lo)
    _, hi = sin_point(x.hi)
    return I(lo, hi)


def cos_i(x):
    # cos is even and decreases with |x| on this domain.
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


LN = F(281, 1000)
LW = F(233, 1000)
LS = F(279, 1000)
LD = F(207, 1000)
assert LN + LW + LS + LD == 1

MU1 = F(949, 1000)  # C -> N
MU4 = MU1           # S -> C, so the force on the unweighted C cancels
MU5 = F(277, 1000)  # W -> N
MU7 = F(603, 1000)  # D -> W
MU8 = F(738, 1000)  # D -> S


def lower_bound(theta_n, theta_w, theta_s, eps_d, source_wn):
    cN, sN = cs(theta_n)
    cW, sW = cs(theta_w)
    cS, sS = cs(theta_s)
    cD, sD = cs(eps_d)

    n1 = (I(0), I(1))
    n4 = n1
    n5 = (cW, sW) if source_wn == "W" else (cN, sN)

    # Direction 3*pi/4 + eps_D.
    n7 = (-H * (cD + sD), H * (cD - sD))
    n8 = (cS, sS)

    gN = vadd(vscale(MU1, n1), vscale(MU5, n5))
    gW = vadd(vscale(-MU5, n5), vscale(MU7, n7))
    gS = vadd(vscale(-MU4, n4), vscale(MU8, n8))
    gD = vadd(vscale(-MU7, n7), vscale(-MU8, n8))

    mN = (F(1, 2) * (cN - sN), F(1, 2) * (sN + cN))
    mW = (F(1, 2) * (-cW - sW), F(1, 2) * (-sW + cW))
    mS = (F(1, 2) * (cS + sS), F(1, 2) * (sS - cS))
    mD = (H * sD, -H * cD)

    # Separator half-width sums.
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
    I(-F(1, 6), F(1, 6)),
    I(-F(1, 4), F(1, 4)),
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

        # This should never be reached with the current certificate.
        assert depth < 30, (source_wn, depth, bound.lo, box)

        widths = [x.hi - x.lo for x in box]
        k = max(range(4), key=lambda i: widths[i])
        a, b = split_box(box, k)
        stack.append((a, depth + 1))
        stack.append((b, depth + 1))

    return visited, leaves, deepest


def main():
    for source in ("W", "N"):
        visited, leaves, deepest = replay(source)
        print(
            source,
            "visited=", visited,
            "certified_leaves=", leaves,
            "max_depth=", deepest,
        )


if __name__ == "__main__":
    main()
