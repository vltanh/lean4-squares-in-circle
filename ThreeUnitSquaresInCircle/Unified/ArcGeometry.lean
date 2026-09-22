import ThreeUnitSquaresInCircle.Unified.SafePieces
import ThreeUnitSquaresInCircle.Unified.ScalarArcs

/-!
# Geometric realization obligations for the unified proof

STATUS: SIX EXPLICIT ADMISSIONS REMAIN IN THIS FILE.
They are not compiler fixes. They are the unfinished geometric formalization.
No other new file declares an axiom or deliberately admits a theorem.

The exact theorem statements below are used by `Cases.lean`. Proof sketches and
source locations in the accompanying mathematical note are supplied separately.
Do not describe any new endpoint depending on this file as kernel verified.
-/

noncomputable section
namespace ThreeUnitSquaresInCircle.Unified
open Set Filter
open scoped Topology

/-- G3-E: normalize by rotations/reflections, then use the clipped cap formula.
In sorted local coordinates, x=a-1/2 and v=1/2-b. The exact angular measure is
min(capLength r3 x, threeTruncatedLength r3 x v). The strict scalar bound has
already been drafted as `three_exterior_scalar`. -/
theorem exterior_three_mass (S : UnitSquare) (o : Point)
    (hP : CenterBody P3Strict S o) (hout : ¬ openSquare S o) :
    2*Real.pi/3 < occupied S o r3 := by
  sorry

/-- The terminal cap case has an explicit rational intersection point. This
record does NOT assume that point is in either square: its membership follows
from the four identities and the bounds, via `near_caps_point`. -/
structure NearCaps (S T : UnitSquare) where
  point : Point
  a₁ a₂ b₁ b₂ C D : ℝ
  a₁_lower : 1/2 ≤ a₁
  a₁_upper : a₁ ≤ 11/16
  a₂_lower : 1/2 ≤ a₂
  a₂_upper : a₂ ≤ 11/16
  b₁_bound : |b₁| < 1/16
  b₂_bound : |b₂| < 1/16
  C_lower : 1/2 ≤ C
  C_upper : C < 3/5
  D_lower : 4/5 < D
  unit : C^2+D^2=1
  first_x : localX S point = 1/5-a₁
  first_y : localY S point = 2/5-b₁
  second_x : localX T point = -C/5+2*D/5-a₂
  second_y : localY T point = -D/5-2*C/5-b₂

lemma NearCaps.overlap {S T : UnitSquare} (h : NearCaps S T) :
    openSquare S h.point ∧ openSquare T h.point := by
  have hp := near_caps_point h.a₁_lower h.a₁_upper h.a₂_lower h.a₂_upper
    h.b₁_bound h.b₂_bound h.C_lower h.C_upper h.D_lower h.unit
  exact ⟨⟨by simpa [h.first_x] using hp.1,
           by simpa [h.first_y] using hp.2.1⟩,
          ⟨by simpa [h.second_x] using hp.2.2.1,
           by simpa [h.second_y] using hp.2.2.2⟩⟩

/-- G3-I: the containing-square compensation argument.

This is the largest remaining obligation. The intended proof uses:
* p,q>0 with p+q≥39/232 and containing arc π/2+asin(p/r3)+asin(q/r3);
* δ<1/12 (`three_deficit_margin`);
* strict midpoint Jensen (`arcsin_midpoint_strict`) to exclude a clipped neighbor;
* full caps for both neighbors; x>11/64, hence the small transverse coordinates;
* ordering the caps in the complement of the containing arc, giving a separation
  between 2π/3 and 2π/3+δ;
* reframe the two squares and transport the point (1/5,2/5).

The reframing is necessary: the ORIGINAL cosine/sine fields need not point along
the radial cap normals. `SameSquare` transports the intersection back afterward.
-/
theorem containing_three_caps (S : Fin 3 → UnitSquare) (o : Point)
    (hd : Nonoverlapping S) (hP : ∀ i, CenterBody P3Strict (S i) o)
    (i₀ : Fin 3) (hin : openSquare (S i₀) o) :
    ∃ (j k : Fin 3) (U V : UnitSquare), j ≠ k ∧
      Cert.SameSquare U (S j) ∧ Cert.SameSquare V (S k) ∧ Nonempty (NearCaps U V) := by
  sorry

/-- G4-E: a LEFT-HAND radius perturbation avoids the diamond equality families.

At r4, L1 is strictly greater than π/2. L2 is at least π/2 and is strict unless
b=0. For b=0, at r<r4 sufficiently close to r4, L2=2*asin(1/(2*r))>π/2.
All other strict inequalities persist by continuity. No assertion that the block
is the only diamond-tight configuration is used. -/
theorem exterior_four_eventually (S : UnitSquare) (o : Point)
    (hP : CenterBody P4Strict S o) (hout : ¬ openSquare S o) :
    ∀ᶠ r in 𝓝[<] r4, Real.pi/2 < occupied S o r := by
  sorry

/-- G4-I: an origin-containing square's radial extension contains a closed
quarter-arc at r4. If its center is on a local coordinate axis, equality can occur
at r4, so shrinking the auxiliary radius is essential. Since O is interior to
the square and the extension is convex, radial contraction sends this compact
quarter-arc into the interior; openness then gives a strictly longer arc. -/
theorem extension_four_eventually (S : UnitSquare) (o : Point)
    (hin : openSquare S o) (hc : S.center ≠ o) :
    ∀ᶠ r in 𝓝[<] r4,
      Real.pi/2 < angularMass (interior (RadialExtension S o)) o r := by
  sorry

/-- G5-E: the dodecagon exterior-arc lemma.

In normalized coordinates 1/2≤a, 0≤b≤a, 3a+b≤3, a+b≤√5-1.
The exact length is min(L1,L2), with
 L1=π/2-asin((a-1/2)/r5)-asin((b-1/2)/r5),
 L2=asin((b+1/2)/r5)-asin((b-1/2)/r5).
L2>2π/5 follows from midpoint Jensen and 5/14>sin(π/5)^2.
For L1, maximize the two-arcsine sum over the three upper-boundary segments.
Its maximum is at A=(4-√5)/2, B=(3√5-6)/2. The radical margins are in ScalarArcs.
Both inequalities are STRICT even for the CLOSED dodecagon. -/
theorem exterior_five_mass (S : UnitSquare) (o : Point)
    (hP : CenterBody P5 S o) (hout : ¬ openSquare S o) :
    2*Real.pi/5 < occupied S o r5 := by
  sorry

/-- G5-I: the extension contains an open radius-1/2 disk centered at
O+w/√2, w=(center-O)/|center-O|. Its intersection with the auxiliary circle
contains a CLOSED 72-degree arc strictly inside the disk, by
`five_extension_radical_margin`. Thus openness gives angular mass STRICTLY
larger than 72 degrees. This is slightly stronger than the nonstrict version
needed in the original written proof. -/
theorem extension_five_mass (S : UnitSquare) (o : Point)
    (hin : openSquare S o) (hc : S.center ≠ o) :
    2*Real.pi/5 < angularMass (interior (RadialExtension S o)) o r5 := by
  sorry

end ThreeUnitSquaresInCircle.Unified
