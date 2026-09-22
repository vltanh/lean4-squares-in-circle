#!/usr/bin/env python3
"""
Exact-arithmetic certificate checker for a proposed proof that three
interior-disjoint unit squares need an enclosing disk of radius
5*sqrt(17)/16, with independent rotations allowed.

Only the Python standard library is used. No optimizer, floating-point
arithmetic, numerical tolerance, or external data is used.

The geometric reductions and the dual inequality are given in the
accompanying three_squares_circle_proof.md. This program verifies the
finite case enumeration, coefficient arithmetic, concavity tests,
polygon covers, and vertex inequalities used there.

Run:
    python three_squares_circle_certificate.py
"""
from fractions import Fraction as Q
from functools import lru_cache
from itertools import permutations, product

if not __debug__:
    raise RuntimeError("Run without -O: this verifier uses assertions.")

TARGET = Q(425, 256)
PAIRS = ((0, 1), (0, 2), (1, 2))
DIRECTIONS = ((1, 0), (0, 1), (-1, 0), (0, -1))
VERTICES = ((Q(-1, 2), Q(-1, 2)), (Q(-1, 2), Q(1, 2)),
            (Q(1, 2), Q(-1, 2)), (Q(1, 2), Q(1, 2)))
SOURCES = tuple(product((0, 1), (0, 2), (1, 2)))

# Rows of lambda, multiplied by 64; mu, multiplied by 512.
# Dictionary key is (k_02, k_12); k_01 is always 0.
BASE_DATA = {
    (0, 1): (((13, 13, 0, 0), (0, 0, 19, 0), (0, 0, 0, 19)),
             (247, 247, 304)),
    (0, 3): (((13, 13, 0, 0), (0, 0, 0, 19), (0, 0, 19, 0)),
             (247, 247, 304)),
    (1, 1): (((19, 0, 0, 0), (0, 0, 19, 0), (0, 13, 0, 13)),
             (304, 247, 247)),
    (1, 2): (((19, 0, 0, 0), (0, 0, 13, 13), (0, 19, 0, 0)),
             (247, 304, 247)),
    (3, 2): (((0, 19, 0, 0), (0, 0, 13, 13), (19, 0, 0, 0)),
             (247, 304, 247)),
    (3, 3): (((0, 19, 0, 0), (0, 0, 0, 19), (13, 0, 13, 0)),
             (304, 247, 247)),
}

# Coordinates below are (a/pi, b/pi), not radians.
O = (Q(0), Q(0))
V = (Q(0), Q(1, 4))
W = (Q(1, 6), Q(1, 3))
P = (Q(0), Q(1, 8))
Z = (Q(1, 12), Q(1, 6))  # Z = W/2, called Z in the written proof.
DOMAIN = (O, V, W)

# The five branches needing an additional certificate.
EXCEPTIONS = {
    ((0, 3), (1, 0, 1)): "G",
    ((1, 1), (0, 0, 2)): "H",
    ((1, 1), (1, 0, 2)): "H",
    ((3, 3), (0, 2, 1)): "J",
    ((3, 3), (1, 2, 1)): "J",
}


def dot(x, y):
    return x[0] * y[0] + x[1] * y[1]


def cross(x, y):
    return x[0] * y[1] - x[1] * y[0]


def sub(x, y):
    return (x[0] - y[0], x[1] - y[1])


def weights(pattern, extra=None):
    if extra is None:
        lam0, mu0 = BASE_DATA[pattern]
        return ([[Q(v, 64) for v in row] for row in lam0],
                [Q(v, 512) for v in mu0])
    lam = [[Q(0) for _ in VERTICES] for _ in range(3)]
    if extra == "G":
        lam[0][0], lam[1][3], lam[2][0] = Q(3, 10), Q(2, 5), Q(3, 10)
        mu = [Q(4, 5), Q(0), Q(4, 5)]
    elif extra == "H":
        lam[0][0], lam[1][2], lam[2][3] = Q(5, 16), Q(5, 16), Q(3, 8)
        mu = [Q(1, 2), Q(11, 16), Q(3, 8)]
    elif extra == "J":
        lam[0][1], lam[1][3], lam[2][0] = Q(5, 16), Q(5, 16), Q(3, 8)
        mu = [Q(1, 2), Q(3, 8), Q(11, 16)]
    else:
        raise ValueError("Unknown certificate.")
    return lam, mu


def coefficients(pattern, sources, extra=None):
    """Return (C, A_a,A_b,A_d, B_a,B_b,B_d) for d=b-a."""
    lam, mu = weights(pattern, extra)
    assert all(x >= 0 for row in lam for x in row)
    assert sum(sum(row) for row in lam) == 1
    assert all(x >= 0 for x in mu)
    w = [sum(row) for row in lam]
    assert all(x > 0 for x in w)
    ks = (0,) + pattern

    # For square i, its completed-square vector is
    # sum_p Rot(theta_p) v[i][p].
    v = [[[Q(0), Q(0)] for _ in range(3)] for _ in range(3)]
    for i in range(3):
        for j, vertex in enumerate(VERTICES):
            for z in range(2):
                v[i][i][z] += lam[i][j] * vertex[z]
    for e, (i, j) in enumerate(PAIRS):
        assert sources[e] in (i, j)
        for z in range(2):
            value = mu[e] * DIRECTIONS[ks[e]][z] / 2
            v[i][sources[e]][z] += value
            v[j][sources[e]][z] -= value

    C = Q(1, 2) + sum(mu) / 2
    A = [m / 2 for m in mu]
    B = A.copy()
    for i in range(3):
        for p in range(3):
            C -= dot(v[i][p], v[i][p]) / w[i]
        for e, (p, q) in enumerate(PAIRS):
            A[e] -= 2 * dot(v[i][p], v[i][q]) / w[i]
            B[e] += 2 * cross(v[i][p], v[i][q]) / w[i]
    return (C,) + tuple(A) + tuple(B)


def concavity_tests(coeff):
    """
    On DOMAIN: 0<=a<=pi/6, 0<=b<=pi/3, 0<=d=b-a<=pi/4.
    Thus A*cos(t)+B*sin(t) is bounded below by the rational
    quantity used below. These bounds make -Hessian(F) positive
    definite, as checked by its two diagonal entries and determinant.
    """
    A, B = coeff[1:4], coeff[4:7]
    cos_lower = (Q(6, 7), Q(1, 2), Q(7, 10))
    sin_upper = (Q(1, 2), Q(7, 8), Q(3, 4))
    # Verify the nontrivial elementary square-root bounds.
    assert Q(6, 7) ** 2 < Q(3, 4)
    assert Q(7, 10) ** 2 < Q(1, 2)
    assert Q(7, 8) ** 2 > Q(3, 4)
    assert Q(3, 4) ** 2 > Q(1, 2)
    t = [a * (c if a >= 0 else 1) + min(b, 0) * s
         for a, b, c, s in zip(A, B, cos_lower, sin_upper)]
    tests = (t[0] + t[2], t[1] + t[2],
             t[0] * t[1] + t[0] * t[2] + t[1] * t[2])
    # Stronger than merely nonnegative.
    assert tests[0] > Q(1, 3)
    assert tests[1] > Q(3, 16)
    assert tests[2] > Q(3, 40)
    return tests


def atan_bounds(x, terms=40):
    """Alternating-series rational enclosure of arctan(x), 0<x<1."""
    assert 0 < x < 1
    total = sum(((-1) ** k) * x ** (2 * k + 1) / (2 * k + 1)
                for k in range(terms))
    next_term = ((-1) ** terms) * x ** (2 * terms + 1) / (2 * terms + 1)
    return min(total, total + next_term), max(total, total + next_term)


# Machin's identity: pi = 16*atan(1/5) - 4*atan(1/239).
AT5 = atan_bounds(Q(1, 5))
AT239 = atan_bounds(Q(1, 239))
PI = (16 * AT5[0] - 4 * AT239[1], 16 * AT5[1] - 4 * AT239[0])
assert 3 < PI[0] < PI[1] < Q(22, 7)


def series_bounds(x, sine, terms=18):
    """Alternating-series rational enclosure of sin(x) or cos(x)."""
    assert 0 <= x <= PI[1] / 3
    assert x * x < 2  # All successive series terms decrease in magnitude.
    term = x if sine else Q(1)
    total = Q(0)
    for k in range(terms):
        total += term
        den = ((2 * k + 2) * (2 * k + 3) if sine
               else (2 * k + 1) * (2 * k + 2))
        term = -term * x * x / den
    return min(total, total + term), max(total, total + term)


@lru_cache(None)
def trig_bounds(pi_multiple):
    """Return exact rational enclosures (cos interval, sin interval)."""
    assert 0 <= pi_multiple <= Q(1, 3)
    if pi_multiple == 0:
        return (Q(1), Q(1)), (Q(0), Q(0))
    lo, hi = pi_multiple * PI[0], pi_multiple * PI[1]
    # sin increases and cos decreases throughout this interval.
    sine = (series_bounds(lo, True)[0], series_bounds(hi, True)[1])
    cosine = (series_bounds(hi, False)[0], series_bounds(lo, False)[1])
    return cosine, sine


def interval_scale(q, interval):
    lo, hi = interval
    return (q * lo, q * hi) if q >= 0 else (q * hi, q * lo)


def value_bounds(coeff, point):
    a, b = point
    arguments = (a, b, b - a)
    lo = hi = coeff[0]
    for i, argument in enumerate(arguments):
        cosine, sine = trig_bounds(argument)
        for q, interval in ((coeff[1 + i], cosine), (coeff[4 + i], sine)):
            left, right = interval_scale(q, interval)
            lo += left
            hi += right
    return lo, hi


def signed_area(poly):
    return sum(cross(poly[i], poly[(i + 1) % len(poly)])
               for i in range(len(poly))) / 2


def ccw(poly):
    poly = tuple(poly)
    return poly if signed_area(poly) > 0 else tuple(reversed(poly))


def polygon_intersection(subject, clip):
    """Exact convex polygon clipping; only rational coordinates."""
    result = list(ccw(subject))
    clip = ccw(clip)
    for i, x in enumerate(clip):
        y = clip[(i + 1) % len(clip)]
        edge = sub(y, x)
        old, result = result, []
        if not old:
            break
        p = old[-1]
        dp = cross(edge, sub(p, x))
        for q in old:
            dq = cross(edge, sub(q, x))
            if (dp >= 0) != (dq >= 0):
                t = dp / (dp - dq)
                result.append((p[0] + t * (q[0] - p[0]),
                               p[1] + t * (q[1] - p[1])))
            if dq >= 0:
                result.append(q)
            p, dp = q, dq
    return tuple(result)


def check_cover(polygons):
    """Check an exact one- or two-piece convex cover of DOMAIN."""
    for poly0 in polygons:
        poly = ccw(poly0)
        assert signed_area(poly) > 0
        for a, b in poly:
            assert 0 <= a <= b / 2
            assert 2 * b - a <= Q(1, 2)
        for i in range(len(poly)):
            assert cross(sub(poly[(i + 1) % len(poly)], poly[i]),
                         sub(poly[(i + 2) % len(poly)],
                             poly[(i + 1) % len(poly)])) > 0
    assert sum(abs(signed_area(poly)) for poly in polygons) == abs(signed_area(DOMAIN))
    if len(polygons) == 2:
        overlap = polygon_intersection(*polygons)
        assert len(overlap) < 3 or signed_area(overlap) == 0
    else:
        assert len(polygons) == 1
    # Closed subsets of DOMAIN, disjoint interiors, and full total area
    # give a cover: a missing point would give a relative open gap.


def pieces_for(pattern, sources):
    key = (pattern, sources)
    extra = EXCEPTIONS.get(key)
    if extra is None:
        return [(None, DOMAIN)]
    if extra == "G":
        return [(None, (O, V, Z)), ("G", (V, W, Z))]
    if key == ((3, 3), (1, 2, 1)):
        return [(None, (O, P, Z)), ("J", (P, V, W, Z))]
    return [(None, (O, P, W)), (extra, (P, V, W))]


def verify():
    # Check the complete 16-pattern enumeration.
    for pattern in product(range(4), repeat=2):
        ks = (0,) + pattern
        direction = {}
        for edge, (i, j) in enumerate(PAIRS):
            direction[i, j] = ks[edge]
            direction[j, i] = (ks[edge] + 2) % 4
        has_forbidden_chain = any(
            direction[i, j] == direction[j, k]
            for i, j, k in permutations(range(3)))
        assert has_forbidden_chain == (pattern not in BASE_DATA)

    # Rational ingredients in the analytic forbidden-chain estimate.
    assert Q(5, 3) ** 2 < 3
    assert (Q(5, 8) - Q(93, 176) * Q(22, 21)) == Q(1, 14)

    certificates = 0
    tested_vertices = 0
    branches = 0
    for pattern in BASE_DATA:
        for sources in SOURCES:
            branches += 1
            base = coefficients(pattern, sources)
            assert base[0] + sum(base[1:4]) == TARGET
            pieces = pieces_for(pattern, sources)
            check_cover([poly for _, poly in pieces])
            for extra, poly in pieces:
                coeff = coefficients(pattern, sources, extra)
                concavity_tests(coeff)
                certificates += 1
                for point in poly:
                    lo, hi = value_bounds(coeff, point)
                    if point == O:
                        assert extra is None and lo == hi == TARGET
                    else:
                        assert lo > TARGET + Q(1, 250)
                    tested_vertices += 1

    assert branches == 48
    assert certificates == 53
    print("PASS: all 16 cardinal patterns checked; 10 excluded by the chain lemma.")
    print("PASS: all 48 remaining source/direction branches covered.")
    print("PASS: 53 valid dual certificates have strictly concave angle functions.")
    print("PASS: all angle-domain polygon covers checked using rational arithmetic.")
    print("PASS: every tested nonzero vertex has F - 425/256 > 1/250.")
    print("PASS: at the zero-angle vertex, every base certificate equals 425/256.")
    print("PASS: trigonometric evaluations use rational alternating-series bounds.")
    print(f"Certificate/vertex checks: {certificates}/{tested_vertices}.")
    print("Together with the written geometric reductions, these checks certify")
    print("the lower bound R^2 >= 425/256 for three interior-disjoint unit squares.")


if __name__ == "__main__":
    verify()
