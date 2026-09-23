import SquaresInCircles.Two.Construction
import SquaresInCircles.Common.Contacts

/-!
# Two unit squares

The smallest disk containing two non-overlapping unit squares has radius
`sqrt 5 / 2`, half the diagonal of a 2 × 1 rectangle, and the squares then form
that rectangle, centred at the disk centre.

A square whose farthest vertex is strictly within `sqrt 5 / 2` of the disk
centre has its own centre strictly within `1/2`. Two such centres are less than
1 apart, but centres of interior-disjoint unit squares are at least 1 apart.
-/
noncomputable section
namespace SquaresInCircles

lemma center_near_of_phi_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (h : phi a b ≤ 5/4) : a^2+b^2 ≤ 1/4 := by
  unfold phi at h
  by_contra hn
  have hs : 1/2 < a+b := by nlinarith [mul_nonneg ha hb]
  linarith

lemma center_near_of_phi_lt {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (h : phi a b < 5/4) : a^2+b^2 < 1/4 := by
  unfold phi at h
  by_contra hn
  have hs : 1/2 ≤ a+b := by nlinarith [mul_nonneg ha hb]
  linarith

/-- The parallelogram law, with the disk centre `o` as the common origin. -/
lemma normSq_parallelogram (c d o : Point) :
    normSq (sub c d)+normSq (sub (add c d) (scale 2 o)) =
      2*normSq (sub c o)+2*normSq (sub d o) := by
  simp only [normSq,sub,add,scale]
  ring

theorem Two.squared_lower (S : Fin 2 → UnitSquare) (o : Point) (R : ℝ)
    (hp : Packing S o R) : (5:ℝ)/4 ≤ R^2 := by
  by_contra hn
  have hsmall : R^2 < 5/4 := lt_of_not_ge hn
  have hnear (i : Fin 2) : normSq (sub (S i).center o) < 1/4 := by
    rw [local_center_norm]
    exact center_near_of_phi_lt (alpha_nonneg _ _) (beta_nonneg _ _)
      ((hp.phi_le i).trans_lt hsmall)
  have hfar := centers_distance_sq_ge_one (S 0) (S 1) (hp.2.2 0 1 (by decide))
  have hpar := normSq_parallelogram (S 1).center (S 0).center o
  have hmid := normSq_nonneg (sub (add (S 1).center (S 0).center) (scale 2 o))
  linarith [hnear 0,hnear 1]

theorem Two.optimality (S : Fin 2 → UnitSquare) (o : Point) (R : ℝ)
    (hp : Packing S o R) : Two.radius ≤ R :=
  le_of_sq_le_sq (by rw [Two.radius_sq]; exact Two.squared_lower S o R hp) hp.1

end SquaresInCircles
