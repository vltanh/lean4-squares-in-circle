import ThreeUnitSquaresInCircle.RealBounds
import ThreeUnitSquaresInCircle.AngleDomain
import ThreeUnitSquaresInCircle.Certificates
import ThreeUnitSquaresInCircle.Arithmetic

/-! Real semantics for the rational certificates. Compiles against Lean 4.34.0 / mathlib v4.34.0. -/
noncomputable section
open scoped BigOperators
namespace ThreeUnitSquaresInCircle.Cert
open RatData

def cornerPoint : Corner → Point
  | .O => AngleDomain.O
  | .V => AngleDomain.V
  | .W => AngleDomain.W
  | .P => AngleDomain.P
  | .Z => AngleDomain.Z

/-- Coordinates of x are fractions of pi, as in AngleDomain. -/
def arguments (x : Point) : Fin 3 → ℝ :=
  ![Real.pi * x.1, Real.pi * x.2, Real.pi * x.2 - Real.pi * x.1]

def polynomial (c : Certificate) (x : Point) : ℝ :=
  (c.coeff 0 : ℝ) + ∑ e,
    ((A c e : ℝ) * Real.cos (arguments x e) +
     (B c e : ℝ) * Real.sin (arguments x e))

lemma arguments_corner (p : Corner) (e : Fin 3) :
    arguments (cornerPoint p) e = angleReal (cornerAngles p e) := by
  cases p <;> fin_cases e <;>
    norm_num [arguments, cornerPoint, cornerAngles, angleReal,
      AngleDomain.O, AngleDomain.V, AngleDomain.W, AngleDomain.P, AngleDomain.Z] <;> ring

theorem valueLower_sound (c : Certificate) (p : Corner) :
    (valueLower c p : ℝ) ≤ polynomial c (cornerPoint p) := by
  unfold valueLower polynomial
  push_cast
  gcongr ?_ + ?_
  · exact le_refl _
  apply Finset.sum_le_sum
  intro e _
  rw [arguments_corner]
  exact add_le_add
    (termLower_sound _ _ _ (cosInterval_sound _))
    (termLower_sound _ _ _ (sinInterval_sound _))

theorem checked_corner_lower (c : Certificate) (hc : arithmeticValid c)
    (p : Corner) (hp : p ∈ c.corners) :
    targetSq ≤ polynomial c (cornerPoint p) := by
  have hall := hc.2.2.2.2.2.2.2.2.2.2
  have hok : cornerOK c p := by
    have ht := List.all_eq_true.mp hall p hp
    exact of_decide_eq_true ht
  have hv : (425 / 256 : ℚ) ≤ valueLower c p := by
    unfold cornerOK at hok
    split_ifs at hok with ho
    · exact le_of_eq hok.2.symm
    · linarith
  have hv' : targetSq ≤ (valueLower c p : ℝ) := by
    unfold targetSq
    have := (Rat.cast_le (K := ℝ)).mpr hv
    push_cast at this ⊢
    linarith
  exact hv'.trans (valueLower_sound c p)

/-- The three domain inequalities imply all needed angle ranges. -/
lemma argument_ranges {x : Point} (hx : AngleDomain.Domain x.1 x.2) :
    ∀ e : Fin 3, 0 ≤ arguments x e ∧
      arguments x e ≤ (![Real.pi/6, Real.pi/3, Real.pi/4] : Fin 3 → ℝ) e := by
  rcases hx with ⟨h0,h1,h2⟩
  have hpi := Real.pi_pos
  have ha : x.1 ≤ 1/6 := by linarith
  have hb0 : 0 ≤ x.2 := by linarith
  have hb : x.2 ≤ 1/3 := by linarith
  have hd0 : 0 ≤ x.2-x.1 := by linarith
  have hd : x.2-x.1 ≤ 1/4 := by linarith
  intro e
  fin_cases e <;> norm_num [arguments]
  · constructor <;> nlinarith
  · constructor <;> nlinarith
  · constructor <;> nlinarith

/-- Coarse real sine/cosine ranges used in the Hessian certificate. -/
lemma trig_ranges {x : Point} (hx : AngleDomain.Domain x.1 x.2) (e : Fin 3) :
    (((![6/7,1/2,7/10] : Fin 3 → ℚ) e : ℝ) ≤ Real.cos (arguments x e)) ∧
    Real.cos (arguments x e) ≤ 1 ∧
    0 ≤ Real.sin (arguments x e) ∧
    Real.sin (arguments x e) ≤ ((![1/2,7/8,3/4] : Fin 3 → ℚ) e : ℝ) := by
  have hr := argument_ranges hx e
  have hp := Real.pi_pos
  have h2 := sqrt_two_bounds
  have h3 := sqrt_three_bounds
  let u := (![Real.pi/6, Real.pi/3, Real.pi/4] : Fin 3 → ℝ) e
  have hu : 0 ≤ u ∧ u ≤ Real.pi/2 := by
    fin_cases e <;> norm_num [u] <;> constructor <;> linarith
  have hc : Real.cos u ≤ Real.cos (arguments x e) :=
    Real.antitoneOn_cos ⟨hr.1, by linarith [hr.2]⟩
      ⟨hu.1, by linarith⟩ hr.2
  have hs : Real.sin (arguments x e) ≤ Real.sin u :=
    Real.monotoneOn_sin ⟨by linarith [hr.1], by linarith [hr.2]⟩
      ⟨by linarith [hu.1], hu.2⟩ hr.2
  have hs0 := Real.sin_nonneg_of_nonneg_of_le_pi hr.1
    (show arguments x e ≤ Real.pi by linarith [hr.2])
  have hc1 := Real.cos_le_one (arguments x e)
  fin_cases e <;>
    norm_num [u, Real.cos_pi_div_six, Real.cos_pi_div_three,
      Real.cos_pi_div_four, Real.sin_pi_div_six,
      Real.sin_pi_div_three, Real.sin_pi_div_four] at * <;>
    exact ⟨by linarith, hc1, hs0, by linarith⟩

def curvature (c : Certificate) (x : Point) (e : Fin 3) : ℝ :=
  (A c e : ℝ) * Real.cos (arguments x e) +
  (B c e : ℝ) * Real.sin (arguments x e)

lemma curvatureLower_sound (c : Certificate) {x : Point}
    (hx : AngleDomain.Domain x.1 x.2) (e : Fin 3) :
    (curvatureLower c e : ℝ) ≤ curvature c x e := by
  rcases trig_ranges hx e with ⟨hc0,hc1,hs0,hs1⟩
  let l : ℚ := (![6/7,1/2,7/10] : Fin 3 → ℚ) e
  let u : ℚ := (![1/2,7/8,3/4] : Fin 3 → ℚ) e
  have heq : curvatureLower c e =
      termLower (A c e) (l,1) + termLower (B c e) (0,u) := by
    unfold curvatureLower termLower
    by_cases ha : 0 ≤ A c e <;> by_cases hb : 0 ≤ B c e
    · simp [ha, hb, l]
    · simp [ha, hb, min_eq_left (le_of_lt (lt_of_not_ge hb)), l, u]
    · simp [ha, hb]
    · simp [ha, hb, min_eq_left (le_of_lt (lt_of_not_ge hb)), u]
  rw [heq]
  push_cast
  exact add_le_add
    (termLower_sound (A c e) (l,1) _ ⟨hc0, by simpa using hc1⟩)
    (termLower_sound (B c e) (0,u) _ ⟨by simpa using hs0, hs1⟩)

lemma curvature_form_nonneg (c : Certificate) (hc : arithmeticValid c)
    {x : Point} (hx : AngleDomain.Domain x.1 x.2) (u v : ℝ) :
    0 ≤ curvature c x 0 * u^2 + curvature c x 1 * v^2 +
      curvature c x 2 * (v-u)^2 := by
  have hAq := hc.2.2.2.2.2.2.2.1
  have hDq := hc.2.2.2.2.2.2.2.2.2.1
  have hA : (0 : ℝ) < (curvatureLower c 0 : ℝ) + (curvatureLower c 2 : ℝ) := by
    have h : (0 : ℚ) < curvatureLower c 0 + curvatureLower c 2 := by linarith
    exact_mod_cast h
  have hD : (0 : ℝ) < (curvatureLower c 0 : ℝ) * (curvatureLower c 1 : ℝ) +
      (curvatureLower c 0 : ℝ) * (curvatureLower c 2 : ℝ) +
      (curvatureLower c 1 : ℝ) * (curvatureLower c 2 : ℝ) := by
    have h : (0 : ℚ) < curvatureLower c 0 * curvatureLower c 1 +
        curvatureLower c 0 * curvatureLower c 2 + curvatureLower c 1 * curvatureLower c 2 := by linarith
    exact_mod_cast h
  exact hessian_nonneg _ _ _ _ _ _ u v
    (curvatureLower_sound c hx 0) (curvatureLower_sound c hx 1)
    (curvatureLower_sound c hx 2) hA hD

end ThreeUnitSquaresInCircle.Cert
