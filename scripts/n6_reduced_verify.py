#!/usr/bin/env python3
"""
Diagnostic branch-and-bound verifier for the reduced n=6 square packing problem.

IMPORTANT:
  * This script is NOT a proof certificate.
  * It uses IEEE-754 interval enclosures with nextafter-expanded elementary
    trig evaluations. The intended final verifier should replace these by
    independently checkable rational/MPFI bounds or emit a replay certificate.
  * The mathematical reductions encoded here are documented in
    research/six/PROGRESS.md.

The script is designed for diagnosis and checkpoint/resume. It searches the
normalized E,N,W,D,S state space at the candidate squared radius q_* and
records which structural branches survive.
"""
from __future__ import annotations

import argparse
import dataclasses
import gzip
import json
import math
import os
import sys
import time
from functools import lru_cache
from decimal import Decimal, getcontext
from typing import List, Sequence, Tuple

getcontext().prec = 80

D2 = Decimal(2)
hD = Decimal(1) / D2.sqrt()
AD = (Decimal(1466) + Decimal(1940) * hD) / Decimal(267)
BD = (Decimal(327) + Decimal(432) * hD) / Decimal(712)
sD = Decimal(2) * BD / (AD + (AD * AD - Decimal(4) * BD).sqrt())
tD = (-Decimal(20) + Decimal(30) * hD) * sD + Decimal(7) / 2 - Decimal(9) * hD / 2
dD = Decimal(1) / 2 + hD - tD
qD = Decimal(2) * sD * sD + Decimal(4) * sD + Decimal(5) / 2

QSTAR = float(qD)
SSTAR = float(sD)
TSTAR = float(tD)
DSTAR = float(dD)
RB = math.sqrt(QSTAR)
RHO = math.sqrt(QSTAR - 0.25) - 0.5
CAPK = RHO - 0.5

PI = math.pi
R_PIN = 0.9
GAP_LO = PI / 3.0
GAP_HI = 2.0 * PI / 3.0

NAMES = ("E", "N", "W", "D", "S")
PIN_GAMMA = {
    "E": 0.0,
    "N": PI / 2.0,
    "W": 11.0 * PI / 12.0,
    "D": 5.0 * PI / 4.0,
    "S": 19.0 * PI / 12.0,
}
PHI0 = {
    "E": 0.0,
    "N": PI / 2.0,
    "W": PI,
    "D": PI,
    "S": 3.0 * PI / 2.0,
}
PHI_CAND = {
    "E": 0.0,
    "N": PI / 2.0,
    "W": PI,
    "D": 5.0 * PI / 4.0,
    "S": 3.0 * PI / 2.0,
}
CENTER_CAND = {
    "E": (SSTAR + 1.0, SSTAR),
    "N": (SSTAR, SSTAR + 1.0),
    "W": (SSTAR - 1.0, TSTAR),
    "D": (-DSTAR, -DSTAR),
    "S": (TSTAR, SSTAR - 1.0),
}

CX, CY = 0, 1
OFF = {name: 2 + 3 * i for i, name in enumerate(NAMES)}
DIM = 17


def down(x: float) -> float:
    return math.nextafter(x, -math.inf)


def up(x: float) -> float:
    return math.nextafter(x, math.inf)


@dataclasses.dataclass(frozen=True)
class I:
    lo: float
    hi: float

    def __post_init__(self):
        if math.isnan(self.lo) or math.isnan(self.hi) or self.lo > self.hi:
            raise ValueError((self.lo, self.hi))

    @property
    def width(self) -> float:
        return self.hi - self.lo

    def intersect(self, other: "I") -> "I | None":
        lo = max(self.lo, other.lo)
        hi = min(self.hi, other.hi)
        return None if lo > hi else I(lo, hi)

    def __neg__(self) -> "I":
        return I(down(-self.hi), up(-self.lo))

    def __add__(self, other: "I | float") -> "I":
        other = asI(other)
        return I(down(self.lo + other.lo), up(self.hi + other.hi))

    __radd__ = __add__

    def __sub__(self, other: "I | float") -> "I":
        return self + (-asI(other))

    def __rsub__(self, other: "I | float") -> "I":
        return asI(other) - self

    def __mul__(self, other: "I | float") -> "I":
        other = asI(other)
        xs = (
            self.lo * other.lo,
            self.lo * other.hi,
            self.hi * other.lo,
            self.hi * other.hi,
        )
        return I(down(min(xs)), up(max(xs)))

    __rmul__ = __mul__

    def abs(self) -> "I":
        if self.lo <= 0.0 <= self.hi:
            return I(0.0, up(max(-self.lo, self.hi)))
        return I(down(min(abs(self.lo), abs(self.hi))),
                 up(max(abs(self.lo), abs(self.hi))))

    def subset(self, lo: float, hi: float) -> bool:
        return lo <= self.lo and self.hi <= hi


def asI(x: I | float) -> I:
    return x if isinstance(x, I) else I(float(x), float(x))


@lru_cache(maxsize=500000)
def trig_interval(x: I, fn: str) -> I:
    """Diagnostic enclosure for sin/cos over x, expanded by one ulp."""
    if x.width >= 2 * PI:
        return I(-1.0, 1.0)
    vals = []
    f = math.sin if fn == "sin" else math.cos
    vals.extend((f(x.lo), f(x.hi)))
    if fn == "sin":
        k0 = math.ceil((x.lo - PI / 2) / PI)
        k1 = math.floor((x.hi - PI / 2) / PI)
        for k in range(k0, k1 + 1):
            vals.append(1.0 if k % 2 == 0 else -1.0)
    else:
        k0 = math.ceil(x.lo / PI)
        k1 = math.floor(x.hi / PI)
        for k in range(k0, k1 + 1):
            vals.append(1.0 if k % 2 == 0 else -1.0)
    return I(down(min(vals)), up(max(vals)))


def sinI(x: I) -> I:
    return trig_interval(x, "sin")


def cosI(x: I) -> I:
    return trig_interval(x, "cos")


@lru_cache(maxsize=500000)
def widthI(phi: I) -> I:
    return 0.5 * (cosI(phi).abs() + sinI(phi).abs())


@dataclasses.dataclass
class Box:
    iv: List[I]
    depth: int = 0

    def copy(self) -> "Box":
        return Box(list(self.iv), self.depth)

    def get(self, name: str) -> Tuple[I, I, I]:
        k = OFF[name]
        return self.iv[k], self.iv[k + 1], self.iv[k + 2]

    def set_outer(self, name: str, phi: I | None = None,
                  a: I | None = None, b: I | None = None) -> None:
        k = OFF[name]
        if phi is not None:
            self.iv[k] = phi
        if a is not None:
            self.iv[k + 1] = a
        if b is not None:
            self.iv[k + 2] = b

    def center(self, name: str) -> Tuple[I, I]:
        phi, a, b = self.get(name)
        c, s = cosI(phi), sinI(phi)
        return a * c - b * s, a * s + b * c

    def nearest(self, name: str) -> Tuple[I, I]:
        phi, a, _ = self.get(name)
        r = a - 0.5
        return r * cosI(phi), r * sinI(phi)

    def marker(self, name: str) -> I:
        phi, _, b = self.get(name)
        return phi + 1.25 * b


def initial_box() -> Box:
    iv = [I(-23/200, 23/200), I(-23/200, 23/200)]
    for name in NAMES:
        center = PHI0[name]
        iv += [
            I(center - PI/4, center + PI/4),
            I(177/200, 223/200),
            I(-117/250, 117/250),
        ]
    return Box(iv, 0)


def min_abs(x: I) -> float:
    if x.lo <= 0.0 <= x.hi:
        return 0.0
    return min(abs(x.lo), abs(x.hi))


def contract_box(box: Box) -> bool:
    cx, cy = box.iv[CX], box.iv[CY]
    cmin = (min_abs(cx) + 0.5) ** 2 + (min_abs(cy) + 0.5) ** 2
    if cmin > QSTAR:
        return False

    for _ in range(3):
        changed = False
        for name in NAMES:
            phi, a, b = box.get(name)
            delta = I(PIN_GAMMA[name], PIN_GAMMA[name]) - phi
            q1 = R_PIN * cosI(delta)
            q2 = R_PIN * sinI(delta)

            na = a.intersect(I(down(q1.lo - 0.5), up(q1.hi + 0.5)))
            nb = b.intersect(I(down(q2.lo - 0.5), up(q2.hi + 0.5)))
            if na is None or nb is None:
                return False

            bmin = min_abs(nb)
            rem = QSTAR - (bmin + 0.5) ** 2
            if rem < 0:
                return False
            ahi = math.sqrt(max(0.0, rem)) - 0.5
            na = na.intersect(I(177/200, up(ahi)))
            if na is None:
                return False

            rem2 = QSTAR - (na.lo + 0.5) ** 2
            if rem2 < 0:
                return False
            babs_hi = max(0.0, math.sqrt(rem2) - 0.5)
            nb = nb.intersect(I(-babs_hi, babs_hi))
            if nb is None:
                return False

            if na != a or nb != b:
                changed = True
                box.set_outer(name, a=na, b=nb)

        if not changed:
            break

    phiW = box.get("W")[0]
    phiD = box.get("D")[0]
    if phiW.lo > phiD.hi:
        return False
    return True


def pin_possible(box: Box, name: str) -> bool:
    phi, a, b = box.get(name)
    delta = I(PIN_GAMMA[name], PIN_GAMMA[name]) - phi
    dx = R_PIN * cosI(delta) - a
    dy = R_PIN * sinI(delta) - b
    return (
        dx.lo < 0.5 and dx.hi > -0.5
        and dy.lo < 0.5 and dy.hi > -0.5
    )


def guaranteed_contains_pin(box: Box, square: str, pin_owner: str) -> bool:
    phi, a, b = box.get(square)
    delta = I(PIN_GAMMA[pin_owner], PIN_GAMMA[pin_owner]) - phi
    dx = R_PIN * cosI(delta) - a
    dy = R_PIN * sinI(delta) - b
    return (
        dx.subset(-0.5 + 1e-15, 0.5 - 1e-15)
        and dy.subset(-0.5 + 1e-15, 0.5 - 1e-15)
    )


def marker_gaps_possible(box: Box) -> bool:
    m = {name: box.marker(name) for name in NAMES}
    gaps = [
        m["N"] - m["E"],
        m["W"] - m["N"],
        m["D"] - m["W"],
        m["S"] - m["D"],
        m["E"] + 2*PI - m["S"],
    ]
    return all(not (g.hi < GAP_LO or g.lo > GAP_HI) for g in gaps)


def foot_constraints_possible(box: Box) -> bool:
    cx, cy = box.iv[CX], box.iv[CY]
    F = {name: box.nearest(name) for name in NAMES}

    if F["E"][0].hi < cx.lo + 0.5:
        return False
    if F["N"][1].hi < cy.lo + 0.5:
        return False

    for name in ("W", "D", "S"):
        fx, fy = F[name]
        if fx.lo >= cx.hi + 0.5:
            return False
        if fy.lo >= cy.hi + 0.5:
            return False
        west_possible = fx.lo <= cx.hi - 0.5
        south_possible = fy.lo <= cy.hi - 0.5
        if not (west_possible or south_possible):
            return False
    return True


def containment_possible(box: Box) -> bool:
    cx, cy = box.iv[CX], box.iv[CY]
    if (min_abs(cx) + 0.5)**2 + (min_abs(cy) + 0.5)**2 > QSTAR:
        return False
    for name in NAMES:
        _, a, b = box.get(name)
        qmin = (a.lo + 0.5)**2 + (min_abs(b) + 0.5)**2
        if qmin > QSTAR:
            return False
    return True


def primary_sep_margin(box: Box, name: str) -> I:
    cx, cy = box.iv[CX], box.iv[CY]
    phi, a, _ = box.get(name)
    c, s = cosI(phi), sinI(phi)
    cdot = cx * c + cy * s
    threshold = 0.5 + widthI(phi)
    return a - cdot - threshold


def cardinal_sep_margin(box: Box, name: str) -> I:
    cx, cy = box.iv[CX], box.iv[CY]
    px, py = box.center(name)
    threshold = 0.5 + widthI(box.get(name)[0])
    if name == "E":
        return px - cx - threshold
    if name == "N":
        return py - cy - threshold
    if name in ("W", "D"):
        return cx - px - threshold
    if name == "S":
        return cy - py - threshold
    raise KeyError(name)


def _point_contract(box: Box, name: str, qx: I, qy: I) -> bool:
    phi, a, b = box.get(name)
    c, s = cosI(phi), sinI(phi)
    along = qx * c + qy * s
    across = qx * (-s) + qy * c
    na = a.intersect(I(along.lo - 0.5, along.hi + 0.5))
    nb = b.intersect(I(across.lo - 0.5, across.hi + 0.5))
    if na is None or nb is None:
        return False
    box.set_outer(name, a=na, b=nb)
    return True


def moving_pin_contract(box: Box, pattern: int) -> bool:
    cx, cy = box.iv[CX], box.iv[CY]
    # Global piercing points for E/N hold for either separator type.
    if not _point_contract(box, "E", cx + 1.0, I(0.0, 0.0)):
        return False
    if not _point_contract(box, "N", I(0.0, 0.0), cy + 1.0):
        return False

    # A cardinal-side assignment gets its cap-piercing point.
    if ((pattern >> 2) & 1) == 0:
        if not _point_contract(box, "W", cx - 1.0, I(0.0, 0.0)):
            return False
    if ((pattern >> 3) & 1) == 0:
        if not _point_contract(box, "D", cx - 1.0, I(0.0, 0.0)):
            return False
    if ((pattern >> 4) & 1) == 0:
        if not _point_contract(box, "S", I(0.0, 0.0), cy - 1.0):
            return False
    return True


def _dev_min(phi: I, target: float) -> float:
    if phi.lo <= target <= phi.hi:
        return 0.0
    return min(abs(phi.lo - target), abs(phi.hi - target))


def _cap_depth(theta: float) -> float:
    if RB * math.sin(theta) <= 0.5:
        return CAPK * math.cos(theta) - 0.5 * math.sin(theta)
    return RB - math.cos(theta) - math.sin(theta)


def _side_depth(box: Box, name: str) -> I:
    cx, cy = box.iv[CX], box.iv[CY]
    if name == "E":
        return cx + 0.5
    if name == "N":
        return cy + 0.5
    if name == "W":
        return 0.5 - cx
    if name == "S":
        return 0.5 - cy
    raise KeyError(name)


def sharp_central_constraints(box: Box, pattern: int) -> bool:
    # W and D are the doubled west-primary category. At most one can actually
    # use C's west side.
    if ((pattern >> 2) & 1) == 0 and ((pattern >> 3) & 1) == 0:
        return False

    # E/N own-primary piercing proof gives deviation < 9/20.
    for name in ("E", "N"):
        i = NAMES.index(name)
        if (pattern >> i) & 1:
            if _dev_min(box.get(name)[0], PHI_CAND[name]) >= 9.0 / 20.0:
                return False

    # Cardinal helpers obey the exact one-square cap-depth profile.
    for name in ("E", "N", "W", "S"):
        i = NAMES.index(name)
        if ((pattern >> i) & 1) == 0:
            dm = _dev_min(box.get(name)[0], PHI_CAND[name])
            if dm >= 2.0 / 5.0:
                return False
            if _side_depth(box, name).lo > _cap_depth(dm) + 3e-15:
                return False

    # Opposite cardinal helper angle sums.
    if ((pattern >> 0) & 1) == 0 and ((pattern >> 2) & 1) == 0:
        if (_dev_min(box.get("E")[0], PHI_CAND["E"])
                + _dev_min(box.get("W")[0], PHI_CAND["W"])
                > 4.0 * (RHO - 1.0) + 3e-15):
            return False
    if ((pattern >> 1) & 1) == 0 and ((pattern >> 4) & 1) == 0:
        if (_dev_min(box.get("N")[0], PHI_CAND["N"])
                + _dev_min(box.get("S")[0], PHI_CAND["S"])
                > 4.0 * (RHO - 1.0) + 3e-15):
            return False
    return True


def central_pattern_possible(box: Box, pattern: int) -> bool:
    if not moving_pin_contract(box, pattern):
        return False
    if not sharp_central_constraints(box, pattern):
        return False

    for i, name in enumerate(NAMES):
        cardinal = cardinal_sep_margin(box, name)
        if (pattern >> i) & 1:
            # Canonical branch assignment: own-primary is used only where the
            # cardinal separator is unavailable. Cardinal ties belong to bit 0.
            if primary_sep_margin(box, name).hi < 0.0:
                return False
            if cardinal.lo >= 0.0:
                return False
        else:
            if cardinal.hi < 0.0:
                return False
    return True


def axis_margin_upper(
    phi_i: I, pi: Tuple[I, I], phi_j: I, pj: Tuple[I, I], axis: I
) -> float:
    dx = pj[0] - pi[0]
    dy = pj[1] - pi[1]
    c, s = cosI(axis), sinI(axis)
    dot = dx * c + dy * s
    rel_i = axis - phi_i
    rel_j = axis - phi_j
    hi = widthI(rel_i)
    hj = widthI(rel_j)
    return dot.abs().hi - (hi.lo + hj.lo)


def pair_overlap_forced(box: Box, ni: str, nj: str) -> bool:
    phi_i = box.get(ni)[0]
    phi_j = box.get(nj)[0]
    pi = box.center(ni)
    pj = box.center(nj)
    axes = [phi_i, phi_i + PI/2, phi_j, phi_j + PI/2]
    return all(axis_margin_upper(phi_i, pi, phi_j, pj, ax) < 0.0 for ax in axes)


def common_axis_guaranteed_separated(box: Box, i: str, j: str) -> bool:
    if i == "C":
        pi = (box.iv[CX], box.iv[CY])
        wi = I(0.5, 0.5)
    else:
        pi = box.center(i)
        wi = widthI(box.get(i)[0])
    if j == "C":
        pj = (box.iv[CX], box.iv[CY])
        wj = I(0.5, 0.5)
    else:
        pj = box.center(j)
        wj = widthI(box.get(j)[0])
    dx = (pj[0] - pi[0]).abs()
    dy = (pj[1] - pi[1]).abs()
    thresh_hi = wi.hi + wj.hi
    return dx.lo >= thresh_hi or dy.lo >= thresh_hi


def potential_oblique_pairs(box: Box) -> int:
    alln = ("C",) + NAMES
    count = 0
    for i in range(len(alln)):
        for j in range(i + 1, len(alln)):
            if not common_axis_guaranteed_separated(box, alln[i], alln[j]):
                count += 1
    return count


def local_candidate_cover(box: Box) -> bool:
    eta = 0.01
    if not box.iv[CX].subset(SSTAR - eta, SSTAR + eta):
        return False
    if not box.iv[CY].subset(SSTAR - eta, SSTAR + eta):
        return False
    for name in NAMES:
        phi = box.get(name)[0]
        if not phi.subset(PHI_CAND[name] - eta, PHI_CAND[name] + eta):
            return False
        px, py = box.center(name)
        tx, ty = CENTER_CAND[name]
        if not px.subset(tx - eta, tx + eta):
            return False
        if not py.subset(ty - eta, ty + eta):
            return False
    return True


def four_side_small_angle_cover(box: Box, pattern: int) -> bool:
    for name in ("E", "N", "W", "S"):
        i = NAMES.index(name)
        if (pattern >> i) & 1:
            return False
    eta = 1.0 / 24.0
    for name in ("E", "N", "W", "S", "D"):
        phi = box.get(name)[0]
        if not phi.subset(PHI_CAND[name] - eta, PHI_CAND[name] + eta):
            return False
    return True


def analytic_cover(box: Box, pattern: int) -> str | None:
    if local_candidate_cover(box):
        return "local-rigidity"
    if potential_oblique_pairs(box) <= 1:
        return "one-oblique-pair"
    if four_side_small_angle_cover(box, pattern):
        return "four-side-small-angle"
    return None


def reject_reason(box: Box, pattern: int) -> str | None:
    # Moving-pin contractions shrink a,b; feed those changes back into
    # containment/marker/foot constraints before subdivision.
    for _ in range(2):
        if not contract_box(box):
            return "contraction"
        if not containment_possible(box):
            return "containment"
        if not central_pattern_possible(box, pattern):
            return "central-separator"
        if not marker_gaps_possible(box):
            return "marker-gap"
        if not foot_constraints_possible(box):
            return "foot-type"

    for name in NAMES:
        if not pin_possible(box, name):
            return "own-pin"

    for i in NAMES:
        for j in NAMES:
            if i != j and guaranteed_contains_pin(box, i, j):
                return "foreign-pin-overlap"

    for i in range(len(NAMES)):
        for j in range(i + 1, len(NAMES)):
            if pair_overlap_forced(box, NAMES[i], NAMES[j]):
                return "outer-overlap"

    return None


SCALES = [0.23, 0.23] + sum(([PI/2, 0.23, 0.94] for _ in NAMES), [])


def _possible_axes(box: Box, a: str, b: str):
    pa = box.get(a)[0]
    pb = box.get(b)[0]
    axes = [pa, pa + PI/2, pb, pb + PI/2]
    out = []
    for axis in axes:
        u = axis_margin_upper(box.get(a)[0], box.center(a),
                              box.get(b)[0], box.center(b), axis)
        if u >= 0.0:
            out.append((axis, u))
    return out


def split_box(box: Box) -> Tuple[Box, Box]:
    scores = [iv.width / sc for iv, sc in zip(box.iv, SCALES)]
    for name in NAMES:
        scores[OFF[name]] *= 1.25

    # Search-order heuristic only: when a stress-graph pair has a unique
    # possible separating axis, resolve the variables on that pair first.
    for a, b in (("W", "N"), ("S", "E"), ("D", "W"), ("D", "S")):
        if len(_possible_axes(box, a, b)) == 1:
            for name in (a, b):
                k0 = OFF[name]
                scores[k0] *= 3.0
                scores[k0 + 1] *= 2.0
                scores[k0 + 2] *= 2.0

    k = max(range(DIM), key=scores.__getitem__)
    iv = box.iv[k]
    mid = (iv.lo + iv.hi) / 2.0
    a = box.copy()
    b = box.copy()
    a.iv[k] = I(iv.lo, mid)
    b.iv[k] = I(mid, iv.hi)
    a.depth = b.depth = box.depth + 1
    return a, b


def box_to_json(box: Box):
    return {"depth": box.depth, "iv": [[x.lo, x.hi] for x in box.iv]}


def box_from_json(o) -> Box:
    return Box([I(*x) for x in o["iv"]], int(o["depth"]))


def save_checkpoint(path: str, queue: Sequence[Box], stats: dict, pattern: int) -> None:
    tmp = path + ".tmp"
    payload = {
        "version": 1,
        "pattern": pattern,
        "qstar": QSTAR,
        "stats": stats,
        "queue": [box_to_json(x) for x in queue],
    }
    with gzip.open(tmp, "wt", encoding="utf-8") as f:
        json.dump(payload, f, separators=(",", ":"))
    os.replace(tmp, path)


def load_checkpoint(path: str):
    with gzip.open(path, "rt", encoding="utf-8") as f:
        o = json.load(f)
    return int(o["pattern"]), [box_from_json(x) for x in o["queue"]], dict(o["stats"])


def run_pattern(pattern: int, args) -> dict:
    if args.resume:
        p0, queue, stats = load_checkpoint(args.resume)
        if p0 != pattern:
            raise SystemExit(f"checkpoint pattern {p0} != requested pattern {pattern}")
    else:
        queue = [initial_box()]
        stats = {
            "visited": 0,
            "split": 0,
            "survivors": 0,
            "max_depth": 0,
            "rejected": {},
            "covered": {},
        }

    start = time.time()
    last_ckpt = stats["visited"]
    survivor_out = open(args.survivors, "a", encoding="utf-8") if args.survivors else None

    try:
        while queue and stats["visited"] < args.max_nodes:
            box = queue.pop()
            stats["visited"] += 1
            stats["max_depth"] = max(stats["max_depth"], box.depth)

            rr = reject_reason(box, pattern)
            if rr is not None:
                stats["rejected"][rr] = stats["rejected"].get(rr, 0) + 1
                continue

            cover = analytic_cover(box, pattern)
            if cover is not None:
                stats["covered"][cover] = stats["covered"].get(cover, 0) + 1
                continue

            if box.depth >= args.max_depth:
                stats["survivors"] += 1
                if survivor_out:
                    survivor_out.write(json.dumps({
                        "pattern": pattern,
                        **box_to_json(box),
                    }, separators=(",", ":")) + "\n")
                continue

            left, right = split_box(box)
            queue.append(left)
            queue.append(right)
            stats["split"] += 1

            if args.checkpoint and stats["visited"] - last_ckpt >= args.checkpoint_every:
                save_checkpoint(args.checkpoint, queue, stats, pattern)
                last_ckpt = stats["visited"]

            if args.report_every and stats["visited"] % args.report_every == 0:
                elapsed = max(time.time() - start, 1e-9)
                print(json.dumps({
                    "pattern": pattern,
                    "visited": stats["visited"],
                    "queue": len(queue),
                    "survivors": stats["survivors"],
                    "rate": stats["visited"] / elapsed,
                    "depth": stats["max_depth"],
                    "rejected": stats["rejected"],
                    "covered": stats["covered"],
                }), flush=True)
    finally:
        if survivor_out:
            survivor_out.close()
        if args.checkpoint:
            save_checkpoint(args.checkpoint, queue, stats, pattern)

    stats["remaining_queue"] = len(queue)
    stats["complete"] = not queue and stats["survivors"] == 0
    return stats


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument(
        "--branch",
        default="all",
        help="central separator pattern 0..31; bit i=1 means own-primary separator",
    )
    ap.add_argument("--max-nodes", type=int, default=1_000_000)
    ap.add_argument("--max-depth", type=int, default=48)
    ap.add_argument("--checkpoint", help="gzip JSON checkpoint path (single branch only)")
    ap.add_argument("--resume", help="resume from checkpoint (single branch only)")
    ap.add_argument("--checkpoint-every", type=int, default=100_000)
    ap.add_argument("--report-every", type=int, default=100_000)
    ap.add_argument("--survivors", help="append unresolved max-depth boxes as JSONL")
    args = ap.parse_args()

    print(json.dumps({
        "qstar": QSTAR,
        "s": SSTAR,
        "t": TSTAR,
        "d": DSTAR,
        "warning": "diagnostic IEEE-754 interval search; NOT a proof certificate",
    }))

    if args.branch == "all":
        if args.checkpoint or args.resume:
            raise SystemExit("--checkpoint/--resume require a single --branch")
        results = {}
        for p in range(32):
            print(f"# branch {p:02d} bits={p:05b}", flush=True)
            results[p] = run_pattern(p, args)
            print(json.dumps({"pattern": p, **results[p]}, sort_keys=True), flush=True)
        print(json.dumps({"all_results": results}, sort_keys=True))
    else:
        p = int(args.branch, 0)
        if not (0 <= p < 32):
            raise SystemExit("branch must be in 0..31")
        stats = run_pattern(p, args)
        print(json.dumps({"pattern": p, **stats}, sort_keys=True))


if __name__ == "__main__":
    main()
