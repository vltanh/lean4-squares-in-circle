import SquaresInCircles.Seven.Labels
import SquaresInCircles.Seven.Construction

/-!
# Elementary support lemmas for the affine markers

The support expression is the actual support of the canonical unit square.
Marker-point membership is distinguished from the full marker-arc theorem.
-/
noncomputable section
namespace SquaresInCircles.Seven

def support (a b z : ℝ) : ℝ :=
  a*Real.cos z+b*Real.sin z+(|Real.cos z|+|Real.sin z|)/2

lemma label_ge_sixth {a u : ℝ} (h : Admissible a u) (hu : 1/2 ≤ u) :
    Real.pi/6 ≤ label a u := by
  have hpi := Real.pi_lt_d4
  have hA : Real.pi/6 ≤ axial u := by dsimp [axial]; linarith
  have hT : Real.pi/6 ≤ side a u := by
    rw [side_identity_transverse]
    linarith [h.remainder_nonneg]
  unfold label
  exact le_min (le_min hA hT) (by linarith [Real.pi_pos])

/-- The marker point itself is in the canonical closed square. -/
theorem marker_point_magnitude {a u : ℝ} (h : Admissible a u) :
    |Real.cos (label a u)-a| ≤ 1/2 ∧
    |Real.sin (label a u)-u| ≤ 1/2 := by
  let t := label a u
  have ht0 : 0 ≤ t := h.label_nonneg
  have htq : t ≤ Real.pi/4 := h.label_le_quarter
  have hpi := Real.pi_lt_d4
  have ht8 : t ≤ 4/5 := by linarith
  have hquad := Real.one_sub_sq_div_two_le_cos (x := t)
  have hcos := Real.cos_le_one t
  have hprod := mul_nonneg ht0 (show 0 ≤ 4/5-t by linarith)
  have ha := h.radial_label_bound
  change a ≤ 1+2*Real.pi/15-(4/5)*t at ha
  have hc0 : -1/2 ≤ Real.cos t-a := by nlinarith
  have hc1 : Real.cos t-a ≤ 1/2 := by linarith [h.2.2.1]
  have hs0 := Real.sin_nonneg_of_nonneg_of_le_pi ht0
    (show t ≤ Real.pi by linarith [Real.pi_pos])
  have hs1 := Real.sin_le ht0
  have htA : t ≤ 5*u/4 := h.label_le_axial
  have hy1 : Real.sin t-u ≤ 1/2 := by linarith [h.u_lt]
  have hy0 : -1/2 ≤ Real.sin t-u := by
    by_cases hu : u ≤ 1/2
    · linarith
    · have ht6 : Real.pi/6 ≤ t := label_ge_sixth h (le_of_not_ge hu)
      have hmon := Real.strictMonoOn_sin.monotoneOn
        (show Real.pi/6 ∈ Set.Icc (-(Real.pi/2)) (Real.pi/2) by
          constructor <;> linarith [Real.pi_pos])
        (show t ∈ Set.Icc (-(Real.pi/2)) (Real.pi/2) by
          constructor <;> linarith [Real.pi_pos]) ht6
      rw [Real.sin_pi_div_six] at hmon
      linarith [h.u_lt]
  exact ⟨abs_le.mpr ⟨by linarith,hc1⟩,abs_le.mpr ⟨by linarith,hy1⟩⟩

lemma marker_point_signed {a b : ℝ} (h : Admissible a |b|) :
    |Real.cos (signedLabel a b)-a| ≤ 1/2 ∧
    |Real.sin (signedLabel a b)-b| ≤ 1/2 := by
  have hh := marker_point_magnitude h
  by_cases hb : b < 0
  · simp only [signedLabel, if_pos hb, Real.cos_neg, Real.sin_neg]
    refine ⟨hh.1,?_⟩
    have hid : -Real.sin (label a |b|)-b = -(Real.sin (label a |b|)-|b|) := by
      rw [abs_of_neg hb]
      ring
    rw [hid,abs_neg]
    exact hh.2
  · simpa only [signedLabel, if_neg hb, abs_of_nonneg (le_of_not_gt hb)] using hh

lemma point_le_support {a b x y : ℝ}
    (hx : |x-a| ≤ 1/2) (hy : |y-b| ≤ 1/2) (z : ℝ) :
    x*Real.cos z+y*Real.sin z ≤ support a b z := by
  have hx0 : (x-a)*Real.cos z ≤ (1/2)*|Real.cos z| := by
    calc
      _ ≤ |(x-a)*Real.cos z| := le_abs_self _
      _ = |x-a| * |Real.cos z| := abs_mul _ _
      _ ≤ _ := mul_le_mul_of_nonneg_right hx (abs_nonneg _)
  have hy0 : (y-b)*Real.sin z ≤ (1/2)*|Real.sin z| := by
    calc
      _ ≤ |(y-b)*Real.sin z| := le_abs_self _
      _ = |y-b| * |Real.sin z| := abs_mul _ _
      _ ≤ _ := mul_le_mul_of_nonneg_right hy (abs_nonneg _)
  dsimp [support]
  nlinarith

lemma marker_support_lower {a b : ℝ} (h : Admissible a |b|) (z : ℝ) :
    Real.cos (z-signedLabel a b) ≤ support a b z := by
  have hp := marker_point_signed h
  have hh := point_le_support hp.1 hp.2 z
  simpa only [Real.cos_sub, mul_comm] using hh

lemma center_norm_bound {a u : ℝ} (h : Admissible a u) :
    a^2+u^2 ≤ (Real.sqrt 3-1/2)^2 := by
  let d := Real.sqrt (a^2+u^2)
  have hd0 : 0 ≤ d := Real.sqrt_nonneg _
  have hd2 : d^2 = a^2+u^2 := Real.sq_sqrt (by positivity)
  have hs : d ≤ a+u := by nlinarith [h.a_nonneg,h.1,mul_nonneg h.a_nonneg h.1]
  have hp := h.2.2.2
  have hr := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
  have hr0 := Real.sqrt_nonneg (3 : ℝ)
  dsimp [phi,targetSq] at hp
  have hle : d ≤ Real.sqrt 3-1/2 := by nlinarith
  have hprod := mul_nonneg (sub_nonneg.mpr hle)
    (show 0 ≤ Real.sqrt 3-1/2+d by nlinarith)
  nlinarith

lemma direction_width_ge_one (z : ℝ) : 1 ≤ |Real.cos z|+|Real.sin z| := by
  have he : |Real.cos z|^2+|Real.sin z|^2=1 := by
    simp only [sq_abs]
    nlinarith [Real.sin_sq_add_cos_sq z]
  have hmul := mul_nonneg (abs_nonneg (Real.cos z)) (abs_nonneg (Real.sin z))
  have h0 := abs_nonneg (Real.cos z)
  have h1 := abs_nonneg (Real.sin z)
  nlinarith

lemma support_lower {a b : ℝ} (h : Admissible a |b|) (z : ℝ) :
    1-Real.sqrt 3 ≤ support a b z := by
  have hn : a^2+b^2 ≤ (Real.sqrt 3-1/2)^2 := by
    simpa only [sq_abs] using center_norm_bound h
  have hid : (a*Real.cos z+b*Real.sin z)^2+
      (a*Real.sin z-b*Real.cos z)^2 = a^2+b^2 := by
    calc
      _ = (a^2+b^2)*(Real.sin z^2+Real.cos z^2) := by ring
      _ = _ := by rw [Real.sin_sq_add_cos_sq]; ring
  have hsq := sq_nonneg (a*Real.sin z-b*Real.cos z)
  have hr := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
  have hr0 := Real.sqrt_nonneg (3 : ℝ)
  have hd2 : (a*Real.cos z+b*Real.sin z)^2 ≤ (Real.sqrt 3-1/2)^2 := by
    nlinarith only [hid,hn,hsq]
  have hdot : -(Real.sqrt 3-1/2) ≤ a*Real.cos z+b*Real.sin z := by
    generalize a*Real.cos z+b*Real.sin z = D at hd2 ⊢
    nlinarith only [hd2,hr,hr0]
  have hw := direction_width_ge_one z
  dsimp [support]
  linarith

lemma outward_support_pos {a b A B : ℝ}
    (ha : 1/2 ≤ a) (hB : Admissible A |B|) (z : ℝ) :
    0 < a+1/2+support A B z := by
  have hlow := support_lower hB z
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
  have hroot : Real.sqrt 3 < 2 := by nlinarith [Real.sqrt_nonneg (3 : ℝ)]
  linarith

lemma dot_lower_candidate {X Y p r : ℝ} (hXY : X^2+Y^2 ≤ targetSq) :
    -radius * Real.sqrt (p^2+r^2) ≤ p*X+r*Y := by
  have hid : (p*X+r*Y)^2+(p*Y-r*X)^2=(p^2+r^2)*(X^2+Y^2) := by ring
  have hm := mul_le_mul_of_nonneg_left hXY (show 0 ≤ p^2+r^2 by positivity)
  have hs := Real.sq_sqrt (show 0 ≤ p^2+r^2 by positivity)
  have hn : 0 ≤ radius*Real.sqrt (p^2+r^2) := by
    exact mul_nonneg radius_nonneg (Real.sqrt_nonneg _)
  have he : (radius*Real.sqrt (p^2+r^2))^2=targetSq*(p^2+r^2) := by
    rw [mul_pow, radius_sq, hs]
    rfl
  nlinarith [sq_nonneg (p*Y-r*X)]

end SquaresInCircles.Seven
