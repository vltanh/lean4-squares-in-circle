#!/usr/bin/env python3
"""Exact fixed checker for the E/S pair envelope in final R22-c.

For both patterns 12 and 13 it proves, for v in {S-primary,E-secondary},

    B_v(e,s) >= B_Sp(0,s),  s <= 0,
    B_v(e,s) >= B_Es(0,s),  s >= 0.

The proof is by fixed rational derivative boxes.  The only non-monotone
quadrant is S-primary with s>0 and 0<e<s.  There the possible dip has
slope > -9/100, while the exact e=0 source gap has slope > 19/100.
No adaptive subdivision is used.
"""
from fractions import Fraction as F

from n6_fixed_core import (
    FI, S, floordiv, ceildiv, sqrt_fi, sin_interval, cos_interval,
)
from n6_exact_intervals import candidate_bounds, sqrt_bounds


def pt(x):
    if isinstance(x, FI):
        return x
    if isinstance(x, F):
        return FI.frac(x)
    if isinstance(x, int):
        return FI.point_int(x)
    return FI.frac(F(x))


def box(a, b):
    a, b = pt(a), pt(b)
    return FI(a.lo, b.hi)


def hull(a, b):
    return FI(min(a.lo, b.lo), max(a.hi, b.hi))


def inv_pos(x):
    assert x.lo > 0
    return FI(floordiv(S*S, x.hi), ceildiv(S*S, x.lo))


def div(a, b):
    return a * inv_pos(b)


def sinI(x):
    return sin_interval(x.lo, x.hi)


def cosI(x):
    return cos_interval(x.lo, x.hi)


class J:
    __slots__ = ('v', 'd')

    def __init__(self, v, d=0):
        self.v = pt(v)
        self.d = pt(d)

    def __neg__(self):
        return J(-self.v, -self.d)

    def __add__(self, o):
        o = jj(o)
        return J(self.v + o.v, self.d + o.d)

    __radd__ = __add__

    def __sub__(self, o):
        return self + (-jj(o))

    def __rsub__(self, o):
        return jj(o) - self

    def __mul__(self, o):
        o = jj(o)
        return J(self.v * o.v, self.d * o.v + self.v * o.d)

    __rmul__ = __mul__

    def __truediv__(self, o):
        o = jj(o)
        den = o.v * o.v
        return J(div(self.v, o.v), div(self.d*o.v - self.v*o.d, den))

    def __rtruediv__(self, o):
        return jj(o) / self

    def half(self):
        return J(self.v.div_int(2), self.d.div_int(2))


def jj(x):
    return x if isinstance(x, J) else J(x)


def jsin(x):
    x = jj(x)
    return J(sinI(x.v), cosI(x.v) * x.d)


def jcos(x):
    x = jj(x)
    return J(cosI(x.v), -sinI(x.v) * x.d)


def jsqrt(x):
    x = jj(x)
    s = sqrt_fi(x.v)
    return J(s, div(x.d, FI.point_int(2) * s))


def jabs(x):
    x = jj(x)
    if x.v.lo >= 0:
        return x
    if x.v.hi <= 0:
        return -x
    return J(x.v.abs(), hull(x.d, -x.d))


def jhull(a, b):
    return J(hull(a.v, b.v), hull(a.d, b.d))


# Exact candidate constants.
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


def support_E(x, y):
    """E force is rigorously x-dominant on all boxes used below."""
    x, y = jj(x), jj(y)
    ay = jabs(y)
    assert x.v.lo > 0 and x.v.lo > ay.v.hi, (x.v.f(), y.v.f())
    norm = jsqrt(x*x + y*y)
    cap = x * rho
    vertex = norm * R - (x + ay).half()
    switch = FI.point_int(2) * R * ay.v - norm.v
    if switch.hi <= 0:
        return cap
    if switch.lo >= 0:
        return vertex
    return jhull(cap, vertex)


def support_S(x, y):
    """S force is positive-component and rigorously on the vertex branch."""
    x, y = jj(x), jj(y)
    assert x.v.lo > 0 and y.v.lo > 0, (x.v.f(), y.v.f())
    norm = jsqrt(x*x + y*y)
    V = FI(min(x.v.lo, y.v.lo), min(x.v.hi, y.v.hi))
    switch = FI.point_int(2) * R * V - norm.v
    assert switch.lo > 0, switch.f()
    return norm * R - (x + y).half()


def B(e, s, pattern13, src, qsign=None):
    se, ce = jsin(e), jcos(e)
    sn, cs = jsin(s), jcos(s)
    q = e - s
    sq, cq = jsin(q), jcos(q)

    HCE = J(FI.frac(F(1,2))) + (ce + jabs(se)).half()
    HSC = J(FI.frac(F(1,2))) + (cs + jabs(sn)).half()
    aq = jabs(sq) if qsign is None else (sq if qsign > 0 else -sq)
    HSE = J(FI.frac(F(1,2))) + (cq + aq).half()

    if src == 'Sp':
        cE, sE, cS, sS = sq, cq, J(-1), J(0)
    elif src == 'Es':
        cE, sE, cS, sS = J(0), J(1), -cq, -sq
    else:
        raise KeyError(src)

    if pattern13:
        muE = J(1) / ce
        muS = J(1) + se / ce
        GEx = muE + cE*r
        GEy = sE*r
    else:
        muE = J(1)
        muS = J(1)
        GEx = ce + cE*r
        GEy = -se + sE*r

    GSx = muS*cs - cS*r
    GSy = -muS*sn - sS*r + m

    return (muE*HCE + muS*HSC + HSE*r + J(m).half()
            - support_E(GEx, GEy) - support_S(GSx, GSy))


def frange(lo, hi, step):
    out = []
    x, hi, step = F(lo), F(hi), F(step)
    while x < hi:
        y = min(x + step, hi)
        out.append((x, y))
        x = y
    return out


def check_der(name, pattern13, src, ER, SR, step, *, lower=None, upper=None,
              qside=None, skip=None):
    assert (lower is None) != (upper is None)
    best = None
    count = 0
    for ea, eb in frange(*ER, step):
        for sa, sb in frange(*SR, step):
            if skip is not None and skip(ea, eb, sa, sb):
                continue
            if qside == 1 and eb - sa < 0:
                continue
            if qside == -1 and ea - sb > 0:
                continue
            z = B(J(box(ea,eb), 1), J(box(sa,sb), 0), pattern13, src,
                  qsign=qside).d
            if lower is not None:
                assert z.lo > F(lower)*S, (name, ea, eb, sa, sb, z.f())
                best = z.lo if best is None else min(best, z.lo)
            else:
                assert z.hi < F(upper)*S, (name, ea, eb, sa, sb, z.f())
                best = z.hi if best is None else max(best, z.hi)
            count += 1
    op = '>' if lower is not None else '<'
    edge = lower if lower is not None else upper
    print(name, 'boxes', count, 'derivative', op, float(F(edge)),
          'checked edge', best/S)


def check_delta(name, SR, step, lower):
    best = None
    count = 0
    for sa, sb in frange(*SR, step):
        e = J(box(0,0), 0)
        s = J(box(sa,sb), 1)
        z = (B(e,s,False,'Sp') - B(e,s,False,'Es')).d
        assert z.lo > F(lower)*S, (name, sa, sb, z.f())
        best = z.lo if best is None else min(best, z.lo)
        count += 1
    print(name, 'boxes', count, 'Delta derivative >', float(F(lower)),
          'checked edge', best/S)


def main():
    Sneg = (F(-2,5), F(0))
    Spos = (F(0), F(1,6))
    Sall = (F(-2,5), F(1,6))

    # E-secondary is minimized at e=0 for every s.
    check_der('P12 Es e<0', False, 'Es', (F(-2,5),F(0)), Sall,
              F(1,100), upper=0)
    check_der('P12 Es e>0', False, 'Es', (F(0),F(2,5)), Sall,
              F(1,100), lower=0)

    weakE = (F(-61,150), F(-19,60))
    weakS = (F(-2,5), F(-8,25))
    def weak(ea,eb,sa,sb):
        return ea >= weakE[0] and eb <= weakE[1] and sa >= weakS[0] and sb <= weakS[1]
    check_der('P13 Es e<0 coarse', True, 'Es', (F(-5,12),F(0)), Sall,
              F(1,100), upper=0, skip=weak)
    check_der('P13 Es e<0 fixed refinement', True, 'Es', weakE, weakS,
              F(1,800), upper=0)
    check_der('P13 Es e>0', True, 'Es', (F(0),F(3,10)), Sall,
              F(1,100), lower=0)

    # S-primary is likewise minimized at e=0 when s<=0.
    for pat13, emin, emax, tag in (
        (False,F(-2,5),F(2,5),'P12'),
        (True,F(-5,12),F(3,10),'P13')):
        check_der(tag+' Sp s<=0,e<0', pat13, 'Sp', (emin,F(0)), Sneg,
                  F(1,100), upper=0)
        check_der(tag+' Sp s<=0,e>0', pat13, 'Sp', (F(0),emax), Sneg,
                  F(1,100), lower=0, qside=1)

        # For s>=0, the negative-e side still decreases toward e=0.
        check_der(tag+' Sp s>=0,e<0', pat13, 'Sp', (emin,F(0)), Spos,
                  F(1,100), upper=0, qside=-1)

        # The only dip: 0<=e<=s.  A fixed 1/800 cover proves slope > -9/100.
        check_der(tag+' Sp 0<=e<=s dip', pat13, 'Sp', Spos, Spos,
                  F(1,800), lower=-F(9,100), qside=-1)

        # Once e>=s the derivative is strictly positive again.
        check_der(tag+' Sp e>=s', pat13, 'Sp', (F(0),emax), Spos,
                  F(1,100), lower=0, qside=1)

    # At e=0 both patterns coincide.  Delta=B_Sp-B_Es has Delta(0)=0.
    zsp = B(J(box(0,0),0), J(box(0,0),0), False, 'Sp').v
    zes = B(J(box(0,0),0), J(box(0,0),0), False, 'Es').v
    assert zsp == zes

    # Sp is lower at e=0 for s<0; Es is lower for s>0.  On the positive
    # side this margin also pays for the possible Sp dip.
    check_delta('source gap s<0', Sneg, F(1,100), F(1,20))
    check_delta('source gap s>0', Spos, F(1,100), F(19,100))

    print('A2.2 R22-c E/S envelope: PASS')


if __name__ == '__main__':
    main()
