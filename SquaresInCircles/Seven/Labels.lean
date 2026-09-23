import Mathlib
import SquaresInCircles.Common.Charts
import SquaresInCircles.Common.Tangents

/-!
# Canonical states and the affine angular labels for seven squares

`Admissible` is precisely the local coordinate region used in the analytical
manuscript. It contains no support or separation conclusion. All marker values
below are computed explicitly from coordinates.
-/
noncomputable section
namespace SquaresInCircles.Seven

def targetSq : ℝ := 13 / 4
def gap : ℝ := Real.pi / 3
def axial (u : ℝ) : ℝ := 5 * u / 4
def side (a u : ℝ) : ℝ := Real.pi / 6 + (u - 1/2) / 3 + 3 * (1-a) / 4
def label (a u : ℝ) : ℝ := min (min (axial u) (side a u)) (Real.pi / 4)
def remainder (a u : ℝ) : ℝ := 4 - 3*a - 2*u

def Admissible (a u : ℝ) : Prop :=
  0 ≤ u ∧ u ≤ a ∧ 1/2 ≤ a ∧ phi a u ≤ targetSq

def StrictlyAdmissible (a u : ℝ) : Prop :=
  0 ≤ u ∧ u ≤ a ∧ 1/2 ≤ a ∧ phi a u < targetSq

lemma StrictlyAdmissible.admissible {a u : ℝ} (h : StrictlyAdmissible a u) :
    Admissible a u := ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.le⟩

lemma remainder_identity (a u : ℝ) :
    remainder a u = (a-1)^2 + (u-1/2)^2 + targetSq - phi a u := by
  unfold remainder targetSq phi
  ring

lemma side_identity_transverse (a u : ℝ) :
    side a u = Real.pi/6 + (5/6)*(u-1/2) + remainder a u/4 := by
  unfold side remainder
  ring

lemma side_identity_radial (a u : ℝ) :
    side a u = Real.pi/6 - (5/4)*(a-1) - remainder a u/6 := by
  unfold side remainder
  ring

namespace Admissible
variable {a u : ℝ} (h : Admissible a u)
include h

lemma a_nonneg : 0 ≤ a := by linarith [h.2.2.1]
lemma slack_nonneg : 0 ≤ targetSq - phi a u := sub_nonneg.mpr h.2.2.2

lemma remainder_nonneg : 0 ≤ remainder a u := by
  rw [remainder_identity]
  nlinarith [sq_nonneg (a-1), sq_nonneg (u-1/2), h.slack_nonneg]

lemma tangent : 3*a + 2*u ≤ 4 := by
  have hw := h.remainder_nonneg
  dsimp [remainder] at hw
  linarith

lemma a_lt_five_fourths : a < 5/4 := by
  have hp := h.2.2.2
  dsimp [phi, targetSq] at hp
  nlinarith [h.1, h.2.2.1, sq_nonneg u]

lemma a_le_sqrt_three : a ≤ Real.sqrt 3 - 1/2 := by
  have hp := h.2.2.2
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
  have hn := Real.sqrt_nonneg (3 : ℝ)
  dsimp [phi, targetSq] at hp
  nlinarith [h.1, h.2.2.1, sq_nonneg u]

lemma sum_lt : a+u < 31/20 := by
  have hp := h.2.2.2
  dsimp [phi, targetSq] at hp
  nlinarith [h.1, h.2.2.1, sq_nonneg (a-u)]

lemma u_lt : u < 31/40 := by linarith [h.sum_lt, h.2.1]

lemma side_pos : 0 < side a u := by
  have ha := h.a_lt_five_fourths
  have hp := Real.pi_gt_d2
  dsimp [side]
  linarith [h.1]

lemma label_nonneg : 0 ≤ label a u := by
  have hu := h.1
  unfold label
  exact le_min (le_min (by dsimp [axial]; positivity) h.side_pos.le)
    (by positivity)

lemma label_le_axial : label a u ≤ axial u :=
  (min_le_left _ _).trans (min_le_left _ _)

lemma label_le_side : label a u ≤ side a u :=
  (min_le_left _ _).trans (min_le_right _ _)

lemma label_le_quarter : label a u ≤ Real.pi/4 := min_le_right _ _

lemma label_pos (hu : 0 < u) : 0 < label a u := by
  unfold label axial
  exact lt_min (lt_min (by positivity) h.side_pos) (by positivity)

lemma label_zero_iff : label a u = 0 ↔ u = 0 := by
  constructor
  · intro hl
    by_contra hu
    have hu' : 0 < u := by
      rcases lt_or_eq_of_le h.1 with hpos | hz
      · exact hpos
      · exact False.elim (hu hz.symm)
    have hp := h.label_pos hu'
    rw [hl] at hp
    exact (lt_irrefl (0 : ℝ)) hp
  · intro hu
    subst u
    apply le_antisymm
    · simpa only [axial, mul_zero, zero_div] using h.label_le_axial
    · exact h.label_nonneg

lemma radial_label_bound : a ≤ 1 + 2*Real.pi/15 - (4/5)*label a u := by
  have ht := h.label_le_side
  rw [side_identity_radial] at ht
  linarith [h.remainder_nonneg]

lemma selected : label a u = axial u ∨ label a u = side a u ∨
    label a u = Real.pi/4 := by
  by_cases hA : axial u ≤ side a u
  · by_cases hc : axial u ≤ Real.pi/4
    · exact Or.inl (by simp [label, min_eq_left hA, min_eq_left hc])
    · exact Or.inr (Or.inr (by
        simp [label, min_eq_left hA, min_eq_right (le_of_not_ge hc)]))
  · by_cases hc : side a u ≤ Real.pi/4
    · exact Or.inr (Or.inl (by
        simp [label, min_eq_right (le_of_not_ge hA), min_eq_left hc]))
    · exact Or.inr (Or.inr (by
        simp [label, min_eq_right (le_of_not_ge hA), min_eq_right (le_of_not_ge hc)]))
end Admissible

lemma StrictlyAdmissible.remainder_pos {a u : ℝ} (h : StrictlyAdmissible a u) :
    0 < remainder a u := by
  rw [remainder_identity]
  nlinarith [h.2.2.2, sq_nonneg (a-1), sq_nonneg (u-1/2)]

lemma StrictlyAdmissible.tangent {a u : ℝ} (h : StrictlyAdmissible a u) :
    3*a + 2*u < 4 := by
  have hh := h.remainder_pos
  dsimp [remainder] at hh
  linarith

lemma side_selected_gt_twelfth {a u : ℝ} (h : Admissible a u)
    (hsel : label a u = side a u) : Real.pi/12 < side a u := by
  have hle := h.label_le_axial
  rw [hsel] at hle
  have ha := h.a_lt_five_fourths
  have hpi := Real.pi_gt_d2
  have hu : 7/40 < u := by dsimp [side, axial] at hle; linarith
  have ha' : a < 6/5 := by
    have hp := h.2.2.2
    dsimp [phi, targetSq] at hp
    by_contra hn
    have hm := mul_nonneg (show 0 ≤ a-6/5 by linarith)
      (show 0 ≤ a+11/5 by linarith [h.a_nonneg])
    have hm' := mul_nonneg (show 0 ≤ u-7/40 by linarith)
      (show 0 ≤ u+47/40 by linarith [h.1])
    nlinarith
  dsimp [side]
  linarith

lemma side_selected_a_lt {a u : ℝ} (h : Admissible a u)
    (hsel : label a u = side a u) : a < 9/8 := by
  have hle := h.label_le_axial
  rw [hsel] at hle
  have hlin : 332/25 < 9*a+11*u := by
    have hp := Real.pi_gt_d2
    dsimp [side, axial] at hle
    linarith
  have hp := h.2.2.2
  dsimp [phi, targetSq] at hp
  by_contra hn
  have hda : 0 ≤ a-9/8 := by linarith
  have hx := sq_nonneg (a-9/8)
  have hy := sq_nonneg (u-631/2200)
  nlinarith

/-- Signed transverse coordinates without any orientation normalization assumption. -/
def signedLabel (a b : ℝ) : ℝ := if b < 0 then -label a |b| else label a |b|

lemma signedLabel_neg {a b : ℝ} (h : Admissible a |b|) :
    signedLabel a (-b) = -signedLabel a b := by
  by_cases hb : b = 0
  · subst b
    have hz := h.label_zero_iff.mpr (show |(0 : ℝ)| = 0 by simp)
    simp [signedLabel, hz]
  · by_cases hn : b < 0
    · simp [signedLabel, hn, show ¬ -b < 0 by linarith, abs_neg]
    · have hbpos : 0 < b := by
        by_contra hle
        exact hb (le_antisymm (le_of_not_gt hle) (le_of_not_gt hn))
      simp [signedLabel, hn, show -b < 0 by linarith, abs_neg]

lemma abs_signedLabel_le {a b : ℝ} (h : Admissible a |b|) :
    |signedLabel a b| ≤ Real.pi/4 := by
  unfold signedLabel
  split_ifs <;> simp only [abs_neg, abs_of_nonneg h.label_nonneg] <;>
    exact h.label_le_quarter

/-- The marker in an existing square chart. Reflections are not lost. -/
def chartMarker {S : UnitSquare} {o : Point} (C : SquareChart S o) : Direction :=
  chartAngle C.phase C.reversed (label C.a C.b)

lemma chart_admissible {S : UnitSquare} {o : Point} (C : SquareChart S o)
    (hsort : C.b ≤ C.a) (hout : ¬ openSquare S o)
    (hp : phi (alpha S o) (beta S o) ≤ targetSq) : Admissible C.a C.b :=
  ⟨C.nonneg.2, hsort, C.exterior hsort hout, chart_phi C hp⟩

lemma chart_strictlyAdmissible {S : UnitSquare} {o : Point} (C : SquareChart S o)
    (hsort : C.b ≤ C.a) (hout : ¬ openSquare S o)
    (hp : phi (alpha S o) (beta S o) < targetSq) : StrictlyAdmissible C.a C.b := by
  refine ⟨C.nonneg.2, hsort, C.exterior hsort hout, ?_⟩
  exact C.transfer (fun a b => phi a b < targetSq)
    (fun h => by unfold phi at *; linarith) hp

end SquaresInCircles.Seven
