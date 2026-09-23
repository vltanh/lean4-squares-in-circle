import SquaresInCircles.Common.RectangleArcs
import SquaresInCircles.Three.Tangents

/-!
# Three-square exterior arcs

On the circle of radius `3/8`, a square that does not contain the tested point
holds a cap of length `min (2A) (A+V)`. Under the closed contact 16-gon the cap
is at least 120 degrees, with equality only at the two contact types; under the
strict 16-gon it is longer. If the tested point lies in none of the three open
squares, the strict caps exceed the angular budget, so a strict contact-polygon
configuration must have the tested point inside one square;
`Three/Containing.lean` refutes that alternative.
-/
noncomputable section
open Set
namespace SquaresInCircles

def auxThree : ℝ := 3/8

def threeCapA (a : ℝ) : ℝ := Real.arccos ((a-1/2)/auxThree)
def threeCapV (b : ℝ) : ℝ := Real.arcsin ((1/2-b)/auxThree)
def threeCapLength (a b : ℝ) : ℝ :=
  min (2*threeCapA a) (threeCapA a+threeCapV b)

lemma arcsin_le_sixth {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1/2) :
    Real.arcsin u ≤ Real.pi/6 := by
  apply (Real.arcsin_le_iff_le_sin ⟨by linarith,by linarith⟩
    ⟨by linarith [Real.pi_pos],by linarith [Real.pi_pos]⟩).mpr
  simpa only [Real.sin_pi_div_six] using hu1

/-- The clipped cap is at least 120 degrees, with equality only at `u = 0`,
`v = 1/2`. -/
lemma three_truncated_gap {u v : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1/2)
    (hv : 1/2+(16/13)*u ≤ v) :
    2*Real.pi/3 ≤ Real.arccos u+Real.arcsin v ∧
      (Real.arccos u+Real.arcsin v ≤ 2*Real.pi/3 → u=0 ∧ v=1/2) := by
  have hA := arcsin_le_sixth hu0 hu1
  have hA0 := Real.arcsin_nonneg.mpr hu0
  have hsin : Real.sin (Real.arcsin u+Real.pi/6) ≤ 1/2+u := by
    rw [Real.sin_add,Real.sin_arcsin (by linarith) (by linarith),Real.sin_pi_div_six]
    have hp := mul_nonneg hu0 (sub_nonneg.mpr (Real.cos_le_one (Real.pi/6)))
    linarith [Real.cos_le_one (Real.arcsin u)]
  have hdom : Real.arcsin u+Real.pi/6 ∈ Ioc (-(Real.pi/2)) (Real.pi/2) := by
    constructor <;> linarith [Real.pi_pos]
  have hle := (Real.le_arcsin_iff_sin_le' (y := v) hdom).mpr (hsin.trans (by linarith))
  refine ⟨by dsimp [Real.arccos]; linarith,?_⟩
  intro hbudget
  have hu : u=0 := by
    by_contra hn
    have hu' : 0 < u := lt_of_le_of_ne hu0 (Ne.symm hn)
    have hlt : Real.sin (Real.arcsin u+Real.pi/6) < v := hsin.trans_lt (by linarith)
    have hh := (Real.lt_arcsin_iff_sin_lt'
      ⟨hdom.1.le,by linarith [Real.pi_pos]⟩).mpr hlt
    dsimp [Real.arccos] at hbudget
    linarith
  subst u
  have he : Real.arcsin v=Real.pi/6 := by
    simp only [Real.arccos_zero,Real.arcsin_zero] at hbudget hle
    linarith
  have hv' := (Real.arcsin_eq_iff_eq_sin
    (show Real.pi/6 ∈ Ioo (-(Real.pi/2)) (Real.pi/2) by
      constructor <;> linarith [Real.pi_pos])).mp he
  exact ⟨rfl,by simpa only [Real.sin_pi_div_six] using hv'⟩

lemma three_cap_data {a b : ℝ} (ha : 1/2 ≤ a) (hb : 0 ≤ b) (hp : P3 a b) :
    0 ≤ (a-1/2)/auxThree ∧ (a-1/2)/auxThree ≤ 1/2 ∧
    1/2+(16/13)*((a-1/2)/auxThree) ≤ (1/2-b)/auxThree ∧
    Real.pi/3 ≤ threeCapA a ∧ threeCapA a ≤ Real.pi/2 ∧
    2*Real.pi/3 ≤ threeCapLength a b := by
  have hx0 : 0 ≤ (a-1/2)/auxThree := by dsimp [auxThree]; linarith
  have hx1 : (a-1/2)/auxThree ≤ 1/2 := by dsimp [auxThree]; linarith [hp.2.2.1]
  have hv : 1/2+(16/13)*((a-1/2)/auxThree) ≤ (1/2-b)/auxThree := by
    dsimp [auxThree]; linarith [hp.1]
  have hAsmall := arcsin_le_sixth hx0 hx1
  have hA0 := Real.arcsin_nonneg.mpr hx0
  have hA : Real.pi/3 ≤ threeCapA a := by dsimp [threeCapA,Real.arccos]; linarith
  have hAp : threeCapA a ≤ Real.pi/2 := by dsimp [threeCapA,Real.arccos]; linarith
  exact ⟨hx0,hx1,hv,hA,hAp,le_min (by linarith) (three_truncated_gap hx0 hx1 hv).1⟩

/-- Equality in the exterior arc bound identifies exactly the two contact types. -/
lemma three_cap_contact_types {a b : ℝ} (ha : 1/2 ≤ a) (hb : 0 ≤ b)
    (hp : P3 a b) (hlen : threeCapLength a b ≤ 2*Real.pi/3) :
    (a=11/16 ∧ b=0) ∨ (a=1/2 ∧ b=5/16) := by
  obtain ⟨hx0,hx1,hv,hA,hAp,hgap⟩ := three_cap_data ha hb hp
  by_cases h : 2*threeCapA a ≤ threeCapA a+threeCapV b
  · have he : threeCapA a=Real.pi/3 := by
      rw [threeCapLength,min_eq_left h] at hlen
      linarith
    have hu := Real.cos_arccos (show -1 ≤ (a-1/2)/auxThree by linarith)
      (show (a-1/2)/auxThree ≤ 1 by linarith)
    change Real.cos (threeCapA a)=(a-1/2)/auxThree at hu
    rw [he,Real.cos_pi_div_three] at hu
    have ha' : a=11/16 := by dsimp [auxThree] at hu; linarith
    exact Or.inl ⟨ha',by linarith [hp.2.2.1]⟩
  · rw [threeCapLength,min_eq_right (by linarith)] at hlen
    obtain ⟨hu,hv'⟩ := (three_truncated_gap hx0 hx1 hv).2 hlen
    dsimp [auxThree] at hu hv'
    exact Or.inr ⟨by linarith,by linarith⟩

lemma three_cap_arc_formula {S : UnitSquare} {o : Point} (C : SquareChart S o)
    (ha : 1/2 ≤ C.a) (hp : P3 C.a C.b) :
    ∃ B : OpenArc o auxThree {z | openSquare S z},
      2*B.halfWidth=threeCapLength C.a C.b ∧
      (threeCapA C.a ≤ threeCapV C.b → B.center=C.phase) :=
  C.cap_arc (by norm_num [auxThree]) (by norm_num [auxThree]) ha
    (by dsimp [auxThree]; linarith [hp.2.2.1,C.nonneg.2]) (by linarith [hp.1])

lemma three_exterior_arc (S : UnitSquare) (o : Point)
    (hp : P3Strict (alpha S o) (beta S o)) (hout : ¬ openSquare S o) :
    ∃ A : OpenArc o auxThree {p | openSquare S p}, Real.pi/3 < A.halfWidth := by
  obtain ⟨C,hsort⟩ := sorted_square_chart S o
  have hC := C.transfer P3Strict p3Strict_swap hp
  have ha := C.exterior hsort hout
  obtain ⟨A,hA,-⟩ := three_cap_arc_formula C ha (p3Strict_to_p3 hC)
  refine ⟨A,?_⟩
  rcases lt_or_eq_of_le (three_cap_data ha C.nonneg.2 (p3Strict_to_p3 hC)).2.2.2.2.2
    with h | h
  · linarith
  · rcases three_cap_contact_types ha C.nonneg.2 (p3Strict_to_p3 hC) h.ge
      with ⟨h1,h2⟩ | ⟨h1,h2⟩
    · have h := hC.2.2.1; rw [h1,h2] at h; norm_num at h
    · have h := hC.1; rw [h1,h2] at h; norm_num at h

/-- The exterior-only case of the three-square polygon theorem. -/
theorem three_exterior_reduction (S : Fin 3 → UnitSquare) (o : Point)
    (hd : InteriorDisjoint S) (hp : ∀ i, P3Strict (alpha (S i) o) (beta (S i) o)) :
    ∃ i, openSquare (S i) o := by
  by_contra hn
  push Not at hn
  choose A hA using (fun i => three_exterior_arc (S i) o (hp i) (hn i))
  exact uniform_arc_excess (n := 3) (by decide) A hd.pairwise (fun i => (hA i).le) ⟨0,hA 0⟩

end SquaresInCircles
