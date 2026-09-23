import SquaresInCircles.Common.RectangleArcs
import SquaresInCircles.Four.Tangents

/-! Four squares: on the circle of radius `1/2`, every exterior square in the
closed disk of radius `sqrt 2` holds an arc of at least 90 degrees, strictly
more unless its centre is on the edge of the contact diamond. -/
noncomputable section
open Set
namespace SquaresInCircles

/-- On the circle of radius `1/2` an exterior square holds an arc of at least
90 degrees, and more unless its centre is on the diamond's edge `a + b = 1`. -/
lemma four_exterior_arc {S : UnitSquare} {o : Point} (C : SquareChart S o)
    (hsort : C.b ≤ C.a) (hout : ¬ openSquare S o) (hφ : phi C.a C.b ≤ 2) :
    ∃ A : OpenArc o (1/2) {p | openSquare S p}, Real.pi/4 ≤ A.halfWidth ∧
      (C.a+C.b < 1 → Real.pi/4 < A.halfWidth) := by
  have ha := C.exterior hsort hout
  have hb := C.nonneg.2
  have hsum : C.a+C.b ≤ 1 := p4_of_phi_le hφ
  have ha' : C.a < 5/6 := by
    dsimp [phi] at hφ
    by_contra hn
    linarith [sq_nonneg (C.a-5/6),sq_nonneg C.b]
  obtain ⟨W,hW,-⟩ := C.cap_arc (r := 1/2) (by norm_num) le_rfl ha (by linarith) (by linarith)
  rw [show (C.a-1/2)/(1/2)=2*C.a-1 by ring,show (1/2-C.b)/(1/2)=1-2*C.b by ring] at hW
  have hA : Real.pi/4 < Real.arccos (2*C.a-1) := by
    have huC : 2*C.a-1 < Real.cos (Real.pi/4) := by
      rw [Real.cos_pi_div_four]
      nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num),Real.sqrt_nonneg 2]
    have hh := Real.arccos_lt_arccos (show -1 ≤ 2*C.a-1 by linarith) huC (Real.cos_le_one _)
    rwa [Real.arccos_cos (by positivity) (by linarith [Real.pi_pos])] at hh
  rw [Real.arccos_eq_pi_div_two_sub_arcsin] at hA hW
  refine ⟨W,?_,fun hs => ?_⟩
  · have hV := Real.arcsin_le_arcsin (show 2*C.a-1 ≤ 1-2*C.b by linarith)
    have h := min_le_iff.mp hW.ge
    rcases h with h | h <;> linarith
  · have hV := Real.arcsin_lt_arcsin (show -1 ≤ 2*C.a-1 by linarith)
      (show 2*C.a-1 < 1-2*C.b by linarith) (show 1-2*C.b ≤ 1 by linarith)
    have h := min_le_iff.mp hW.ge
    rcases h with h | h <;> linarith

end SquaresInCircles
