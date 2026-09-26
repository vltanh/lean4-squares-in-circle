#!/usr/bin/env python3
"""Fixed exact 2D checker for source reduction in the final R22-c graph.

No adaptive subdivision is used.  The checker compares only exact one-square
support terms; the pair-separator half-width is source-independent and cancels.
"""
from fractions import Fraction as F

from n6_fixed_core import (
    FI, S, PI, floordiv, ceildiv, sqrt_fi, sin_interval, cos_interval,
)
from n6_exact_intervals import candidate_bounds, sqrt_bounds, QI


def pt(x):
    return x if isinstance(x, FI) else FI.frac(F(x))


def box(a, b):
    a = pt(a); b = pt(b)
    return FI(a.lo, b.hi)


def inv_pos(x):
    assert x.lo > 0
    return FI(floordiv(S*S, x.hi), ceildiv(S*S, x.lo))


def div(a, b):
    return a * inv_pos(b)


def sinI(x):
    return sin_interval(x.lo, x.hi)


def cosI(x):
    return cos_interval(x.lo, x.hi)


def tanI(x):
    return div(sinI(x), cosI(x))


def secI(x):
    return inv_pos(cosI(x))


def imax(a, b):
    return FI(max(a.lo, b.lo), max(a.hi, b.hi))


def imin(a, b):
    return FI(min(a.lo, b.lo), min(a.hi, b.hi))


# Exact candidate enclosures.
h, ss, tt, dd, qstar = candidate_bounds(bits=140)
rr = (ss + F(1,2)) / (ss + F(3,2))
kk = (tt + F(1,2)) / (F(3,2) - ss)
mm = (1 + rr) * kk

rb0 = sqrt_bounds(qstar.lo, bits=140)
rb1 = sqrt_bounds(qstar.hi, bits=140)
R = FI.bounds_frac(rb0.lo, rb1.hi)

rad = qstar - F(1,4)
rh0 = sqrt_bounds(rad.lo, bits=140)
rh1 = sqrt_bounds(rad.hi, bits=140)
rho = FI.bounds_frac(rh0.lo - F(1,2), rh1.hi - F(1,2))

r = FI.bounds_frac(rr.lo, rr.hi)
m = FI.bounds_frac(mm.lo, mm.hi)
ONE = FI.point_int(1)
ZERO = FI.point_int(0)


def support_local(x, y):
    """Exact center-support enclosure from local force components."""
    ax, ay = x.abs(), y.abs()
    U, V = imax(ax, ay), imin(ax, ay)
    norm = sqrt_fi(x*x + y*y)
    cap = rho * U
    vertex = R * norm - (U + V).div_int(2)
    switch = FI.point_int(2) * R * V - norm

    if switch.hi <= 0:
        return cap
    if switch.lo >= 0:
        return vertex
    # A box crossing the exact cap/vertex switch.  Both formulas agree at
    # the switch, so their hull is a rigorous enclosure.
    return FI(min(cap.lo, vertex.lo), max(cap.hi, vertex.hi))


def wn_rel(q, src):
    sq, cq = sinI(q), cosI(q)
    if src == "Wp":
        return -sq, -cq, -ONE, ZERO
    if src == "Ws":
        return cq, -sq, ZERO, -ONE
    if src == "Np":
        return ONE, ZERO, sq, -cq
    if src == "Ns":
        return ZERO, -ONE, -cq, -sq
    raise KeyError(src)


def wn_support(n, w, src):
    cN, sN, cW, sW = wn_rel(n-w, src)
    sn, cn = sinI(n), cosI(n)
    a = ONE + tanI(w)
    b = secI(w)

    # N frame.
    GNx = a*cn + r*cN
    GNy = -a*sn + r*sN

    # W frame.  The D--W edge is W-secondary with multiplier m.
    GWx = b - r*cW
    GWy = -r*sW - m

    return support_local(GNx, GNy) + support_local(GWx, GWy)


def se_rel(q, src):
    sq, cq = sinI(q), cosI(q)
    if src == "Sp":
        return sq, cq, -ONE, ZERO
    if src == "Ss":
        return cq, -sq, ZERO, ONE
    if src == "Ep":
        return ONE, ZERO, -sq, cq
    if src == "Es":
        return ZERO, ONE, -cq, -sq
    raise KeyError(src)


def es_support(e, s, pattern13, src):
    cE, sE, cS, sS = se_rel(e-s, src)
    se, ce = sinI(e), cosI(e)
    ssn, cs = sinI(s), cosI(s)

    if pattern13:
        muE = secI(e)
        muS = ONE + tanI(e)
        GEx = muE + r*cE
        GEy = r*sE
    else:
        muS = ONE
        GEx = ce + r*cE
        GEy = -se + r*sE

    GSx = muS*cs - r*cS
    GSy = -muS*ssn - r*sS + m

    return support_local(GEx, GEy) + support_local(GSx, GSy)


def frange(lo, hi, step):
    out = []
    x = F(lo); hi = F(hi); step = F(step)
    while x < hi:
        y = min(x + step, hi)
        out.append((x, y))
        x = y
    return out


def lower_wn(nb, wb, alt):
    n = box(*nb); w = box(*wb)
    cand = wn_support(n, w, "Wp")
    other = wn_support(n, w, alt)
    return cand.lo - other.hi


def lower_es(eb, sb, pattern13, alt, cand):
    e = box(*eb); s = box(*sb)
    c = es_support(e, s, pattern13, cand)
    a = es_support(e, s, pattern13, alt)
    return c.lo - a.hi


def lower_es_envelope(eb, sb, pattern13, alt):
    e = box(*eb); s = box(*sb)
    a = es_support(e, s, pattern13, alt)
    c1 = es_support(e, s, pattern13, "Sp")
    c2 = es_support(e, s, pattern13, "Es")
    return max(c1.lo, c2.lo) - a.hi


def check_boxes(name, xs, ys, fn, target, skip=None):
    best = None
    count = 0
    for xb in xs:
        for yb in ys:
            if skip is not None and skip(xb, yb):
                continue
            z = fn(xb, yb)
            assert z > target*S, (name, xb, yb, z/S)
            best = z if best is None else min(best, z)
            count += 1
    print(name, "boxes", count, "margin >", best/S)
    return best


# W--N source reduction.
N200 = frange(F(-2,5), F(2,5), F(1,200))
W200 = frange(F(0), F(157,200), F(1,200))
W200.append((F(157,200), PI.div_int(4)))

check_boxes(
    "Ws -> Wp", N200, W200,
    lambda nb,wb: lower_wn(nb,wb,"Ws"), F(3,100),
)

# Np -> Wp: fixed fine rectangle only where the 1/200 enclosure is too wide.
def skip_np(nb, wb):
    return nb[0] >= F(-2,5) and nb[1] <= F(1,4) and wb[0] >= F(133,200)

check_boxes(
    "Np -> Wp coarse", N200, W200,
    lambda nb,wb: lower_wn(nb,wb,"Np"), F(1,100), skip_np,
)
N1000 = frange(F(-2,5), F(1,4), F(1,1000))
W1000 = frange(F(133,200), F(157,200), F(1,1000))
W1000.append((F(157,200), PI.div_int(4)))
check_boxes(
    "Np -> Wp fine", N1000, W1000,
    lambda nb,wb: lower_wn(nb,wb,"Np"), F(1,100),
)

# S--E source reduction, pattern 12.
E12 = frange(F(-2,5), F(2,5), F(1,200))
SS = frange(F(-2,5), F(1,6), F(1,200))

check_boxes(
    "P12 Ss -> Es", E12, SS,
    lambda eb,sb: lower_es(eb,sb,False,"Ss","Es"), F(3,200),
)
check_boxes(
    "P12 Ep -> Sp", E12, SS,
    lambda eb,sb: lower_es(eb,sb,False,"Ep","Sp"), F(1,50),
)

# Pattern 13.
E13 = frange(F(-5,12), F(3,10), F(1,200))

def skip_ss13(eb, sb):
    return eb[0] >= F(-5,12) and eb[1] <= F(-83,300) and sb[0] >= F(-7,200)

check_boxes(
    "P13 Ss -> Es coarse", E13, SS,
    lambda eb,sb: lower_es(eb,sb,True,"Ss","Es"), F(1,2000), skip_ss13,
)
E13f = frange(F(-5,12), F(-83,300), F(1,1000))
S13f = frange(F(-7,200), F(1,6), F(1,1000))
check_boxes(
    "P13 Ss -> Es fine", E13f, S13f,
    lambda eb,sb: lower_es(eb,sb,True,"Ss","Es"), F(1,2000),
)

# For E-primary use the better of the two equality-source supports.  This is
# exactly B_Ep - min(B_Sp,B_Es).
def skip_ep13(eb, sb):
    return eb[0] >= F(5,24) and sb[0] >= F(3,40)

check_boxes(
    "P13 Ep -> equality envelope coarse", E13, SS,
    lambda eb,sb: lower_es_envelope(eb,sb,True,"Ep"), F(3,500), skip_ep13,
)
E13g = frange(F(5,24), F(3,10), F(1,1000))
S13g = frange(F(3,40), F(1,6), F(1,1000))
check_boxes(
    "P13 Ep -> equality envelope fine", E13g, S13g,
    lambda eb,sb: lower_es_envelope(eb,sb,True,"Ep"), F(3,500),
)

print("A2.2 R22-c alternate-source reduction: PASS")
