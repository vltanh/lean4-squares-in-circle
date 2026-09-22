import ThreeUnitSquaresInCircle.Unified.Tangents

/-!
# Scalar inequalities for clipped circular arcs

These statements concern actual real sine/arcsine functions, not intervals whose
relationship with the real functions is assumed. All numeric inequalities below
are stated over ℝ and discharged by proof-producing arithmetic tactics.
-/

noncomputable section
namespace ThreeUnitSquaresInCircle.Unified
open Set Filter
open scoped Topology

abbrev r3 : ℝ := 3/8
abbrev r4 : ℝ := Real.sqrt 2 / 2
abbrev r5 : ℝ := Real.sqrt (7/10)

lemma r4_pos : 0 < r4 := by positivity
lemma r4_sq : r4^2 = 1/2 := by
  have h := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  dsimp [r4]
  nlinarith
lemma half_lt_r4 : (1/2 : ℝ) < r4 := by nlinarith [r4_pos, r4_sq]
lemma r4_lt_one : r4 < 1 := by nlinarith [r4_pos, r4_sq]
lemma r5_pos : 0 < r5 := by positivity
lemma r5_sq : r5^2 = 7/10 := Real.sq_sqrt (by norm_num)
lemma half_lt_r5 : (1/2 : ℝ) < r5 := by nlinarith [r5_pos, r5_sq]
lemma r5_lt_one : r5 < 1 := by nlinarith [r5_pos, r5_sq]

lemma arcsin_half : Real.arcsin (1/2) = Real.pi/6 := by
  have h := Real.arcsin_sin
    (show -(Real.pi/2) ≤ Real.pi/6 by linarith [Real.pi_pos])
    (show Real.pi/6 ≤ Real.pi/2 by linarith [Real.pi_pos])
  simpa only [Real.sin_pi_div_six] using h

lemma arccos_half : Real.arccos (1/2) = Real.pi/3 := by
  rw [Real.arccos_eq_pi_div_two_sub_arcsin, arcsin_half]
  ring

/-- Jensen at the midpoint, proved by a sine addition identity. -/
lemma arcsin_midpoint {x y : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    2*Real.arcsin ((x+y)/2) ≤ Real.arcsin x + Real.arcsin y := by
  let A := Real.arcsin x
  let B := Real.arcsin y
  let M := (A+B)/2
  let D := (A-B)/2
  have hA0 : 0 ≤ A := Real.arcsin_nonneg.2 hx0
  have hB0 : 0 ≤ B := Real.arcsin_nonneg.2 hy0
  have hA1 : A ≤ Real.pi/2 := Real.arcsin_le_pi_div_two _
  have hB1 : B ≤ Real.pi/2 := Real.arcsin_le_pi_div_two _
  have hM0 : 0 ≤ M := by dsimp [M]; linarith
  have hM1 : M ≤ Real.pi/2 := by dsimp [M]; linarith
  have he : x+y = 2*Real.sin M*Real.cos D := by
    have ha : A = M+D := by dsimp [M,D]; ring
    have hb : B = M-D := by dsimp [M,D]; ring
    have hsA : Real.sin A = x := Real.sin_arcsin (by linarith) hx1
    have hsB : Real.sin B = y := Real.sin_arcsin (by linarith) hy1
    rw [ha, Real.sin_add] at hsA
    rw [hb, Real.sin_sub] at hsB
    nlinarith
  have hsM : 0 ≤ Real.sin M :=
    Real.sin_nonneg_of_nonneg_of_le_pi hM0 (by linarith [Real.pi_pos])
  have hmean : (x+y)/2 ≤ Real.sin M := by
    nlinarith [mul_nonneg hsM (sub_nonneg.2 (Real.cos_le_one D))]
  have hmono := Real.arcsin_le_arcsin hmean
  rw [Real.arcsin_sin (by linarith [Real.pi_pos]) hM1] at hmono
  dsimp [M,A,B] at hmono
  linarith

/-- Strict midpoint Jensen; this is the strict compensation used for n=3. -/
lemma arcsin_midpoint_strict {x y : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hy0 : 0 ≤ y) (hy1 : y ≤ 1) (hxy : x ≠ y) :
    2*Real.arcsin ((x+y)/2) < Real.arcsin x + Real.arcsin y := by
  let A := Real.arcsin x
  let B := Real.arcsin y
  let M := (A+B)/2
  let D := (A-B)/2
  have hA0 : 0 ≤ A := Real.arcsin_nonneg.2 hx0
  have hB0 : 0 ≤ B := Real.arcsin_nonneg.2 hy0
  have hA1 : A ≤ Real.pi/2 := Real.arcsin_le_pi_div_two _
  have hB1 : B ≤ Real.pi/2 := Real.arcsin_le_pi_div_two _
  have hAB : A ≠ B := by
    intro h
    apply hxy
    have hh := congrArg Real.sin h
    simpa [A,B,Real.sin_arcsin (by linarith : -1 ≤ x) hx1,
      Real.sin_arcsin (by linarith : -1 ≤ y) hy1] using hh
  have hM0 : 0 < M := by
    dsimp [M]
    by_contra hh
    have : A = B := by linarith
    exact hAB this
  have hM1 : M ≤ Real.pi/2 := by dsimp [M]; linarith
  have hDne : D ≠ 0 := by dsimp [D]; intro h; apply hAB; linarith
  have hDpi : |D| ≤ Real.pi := by
    rw [abs_le]
    dsimp [D]
    constructor <;> linarith [Real.pi_pos]
  have hc : Real.cos D < 1 := by
    have hh := Real.cos_lt_cos_of_nonneg_of_le_pi
      (show (0 : ℝ) ≤ 0 by norm_num) hDpi (abs_pos.2 hDne)
    simpa only [Real.cos_abs, Real.cos_zero] using hh
  have hsM : 0 < Real.sin M := Real.sin_pos_of_pos_of_lt_pi hM0
    (by linarith [Real.pi_pos])
  have he : x+y = 2*Real.sin M*Real.cos D := by
    have ha : A = M+D := by dsimp [M,D]; ring
    have hb : B = M-D := by dsimp [M,D]; ring
    have hsA : Real.sin A = x := Real.sin_arcsin (by linarith) hx1
    have hsB : Real.sin B = y := Real.sin_arcsin (by linarith) hy1
    rw [ha, Real.sin_add] at hsA
    rw [hb, Real.sin_sub] at hsB
    nlinarith
  have hmean : (x+y)/2 < Real.sin M := by
    nlinarith [mul_pos hsM (sub_pos.2 hc)]
  have hmono := Real.strictMonoOn_arcsin
    (show (x+y)/2 ∈ Icc (-1 : ℝ) 1 by constructor <;> linarith)
    (Real.sin_mem_Icc M) hmean
  rw [Real.arcsin_sin (by linarith [Real.pi_pos]) hM1] at hmono
  dsimp [M,A,B] at hmono
  linarith

def capLength (r x : ℝ) : ℝ := 2*Real.arccos (x/r)
def threeTruncatedLength (r x v : ℝ) : ℝ :=
  Real.pi/2 - Real.arcsin (x/r) + Real.arcsin (v/r)

def rectangleLength (r a b : ℝ) : ℝ :=
  min (Real.arccos ((a-1/2)/r)) (Real.arcsin ((b+1/2)/r)) -
    max (-(Real.arccos ((a-1/2)/r))) (Real.arcsin ((b-1/2)/r))

/-- A convenient n=3 bound: no differentiation is needed for an exterior square. -/
lemma three_truncated_strict {x v : ℝ}
    (hx : 0 ≤ x) (hx1 : x ≤ 3/16) (hv : 3/16 + (16/13)*x < v) :
    2*Real.pi/3 < threeTruncatedLength r3 x v := by
  let t := Real.arcsin (x/r3)
  have hux : 0 ≤ x/r3 := by positivity
  have hux1 : x/r3 ≤ 1/2 := by dsimp [r3]; linarith
  have ht0 : 0 ≤ t := Real.arcsin_nonneg.2 hux
  have ht1 : t ≤ Real.pi/6 := by
    have hh := Real.arcsin_le_arcsin hux1
    simpa [t, arcsin_half] using hh
  have hsin : Real.sin t = x/r3 := Real.sin_arcsin (by linarith) (by linarith)
  have hstep : Real.sin (Real.pi/6+t) < v/r3 := by
    rw [Real.sin_add, Real.sin_pi_div_six]
    have h₁ := mul_nonneg hux (sub_nonneg.2 (Real.cos_le_one (Real.pi/6)))
    have h₂ := Real.cos_le_one t
    rw [hsin]
    dsimp [r3] at *
    nlinarith
  have ha := (Real.lt_arcsin_iff_sin_lt'
    (show Real.pi/6+t ∈ Ico (-(Real.pi/2)) (Real.pi/2) by
      constructor <;> linarith [Real.pi_pos])).2 hstep
  dsimp [threeTruncatedLength, t] at *
  linarith

lemma three_cap_strict {x : ℝ} (hx : x < 3/16) :
    2*Real.pi/3 < capLength r3 x := by
  by_cases hxneg : x/r3 ≤ -1
  · rw [capLength, Real.arccos_of_le_neg_one hxneg]
    linarith [Real.pi_pos]
  · have hhalf : x/r3 < 1/2 := by dsimp [r3]; linarith
    have hh := Real.strictAntiOn_arccos
      (show x/r3 ∈ Icc (-1 : ℝ) 1 by constructor <;> linarith)
      (show (1/2 : ℝ) ∈ Icc (-1 : ℝ) 1 by norm_num) hhalf
    rw [arccos_half] at hh
    dsimp [capLength]
    linarith

lemma three_exterior_scalar {a b : ℝ} (ha : 1/2 ≤ a) (hb : 0 ≤ b)
    (h : P3Strict a b) :
    2*Real.pi/3 < min (capLength r3 (a-1/2))
      (threeTruncatedLength r3 (a-1/2) (1/2-b)) := by
  have hx0 : 0 ≤ a-1/2 := by linarith
  have hx1 : a-1/2 < 3/16 := by linarith [h.2.2.1]
  have hv : 3/16+(16/13)*(a-1/2) < 1/2-b := by linarith [h.1]
  exact lt_min (three_cap_strict hx1) (three_truncated_strict hx0 hx1.le hv)

/-- Rational part of the containing-square deficit estimate. -/
lemma three_deficit_margin {p q δ : ℝ}
    (hsum : 39/232 ≤ p+q)
    (hδ : δ ≤ Real.pi/6 - (p+q)/r3) : δ < 1/12 := by
  have hpi := Real.pi_lt_d4
  -- The repository already uses this explicit rational bound on π.
  dsimp [r3] at hδ
  linarith

/-- The cap geometry forces both residual squares into these elementary bounds. -/
lemma three_near_cap_coordinates {x a b : ℝ}
    (hx : 11/64 < x) (ha : a = x+1/2) (hb : 0 ≤ b) (hp : P3 a b) :
    1/2 ≤ a ∧ a ≤ 11/16 ∧ |b| < 1/16 := by
  have hA := hp.coord_le (by linarith) hb
  rw [abs_of_nonneg hb]
  exact ⟨by linarith, hA.1, by linarith [hp.2.2.1]⟩

/-- A concrete point lies inside BOTH squares in the terminal n=3 cap case.
This replaces another invocation of separating-axis enumeration. -/
lemma near_caps_point
    {a₁ a₂ b₁ b₂ C S : ℝ}
    (ha₁ : 1/2 ≤ a₁) (ha₁' : a₁ ≤ 11/16)
    (ha₂ : 1/2 ≤ a₂) (ha₂' : a₂ ≤ 11/16)
    (hb₁ : |b₁| < 1/16) (hb₂ : |b₂| < 1/16)
    (hC : 1/2 ≤ C) (hC' : C < 3/5) (hS : 4/5 < S)
    (hunit : C^2+S^2=1) :
    |1/5-a₁| < 1/2 ∧ |2/5-b₁| < 1/2 ∧
    |-C/5+2*S/5-a₂| < 1/2 ∧ |-S/5-2*C/5-b₂| < 1/2 := by
  have hS' : S < 7/8 := by nlinarith
  rcases abs_lt.mp hb₁ with ⟨hb₁l,hb₁u⟩
  rcases abs_lt.mp hb₂ with ⟨hb₂l,hb₂u⟩
  refine ⟨abs_lt.mpr ⟨by linarith, by linarith⟩,
    abs_lt.mpr ⟨by linarith, by linarith⟩,
    abs_lt.mpr ⟨by linarith, by linarith⟩,
    abs_lt.mpr ⟨by linarith, by linarith⟩⟩

/-- The radical margins used at the five-square dodecagon corner. -/
lemma five_radical_margins :
    (67/30 : ℝ) < Real.sqrt 5 ∧ Real.sqrt 5 < 56/25 ∧
    (151/70 : ℝ) < Real.sqrt 5 ∧ (15/7 : ℝ) < Real.sqrt 5 := by
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)
  have hp := Real.sqrt_nonneg 5
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor <;> nlinarith

lemma five_corner_rational_checks :
    (7/10 : ℝ) - (19/50)^4 < (33/40)^2 ∧
    (37/50 : ℝ)^2 < 7/10-(23/60)^2 ∧
    (10/7 : ℝ) * ((23/60)*(33/40)-(19/50)^2*(37/50)) = 104697/350000 ∧
    (104697/350000 : ℝ) < 3/10 ∧
    (3/10 : ℝ) < (Real.sqrt 5-1)/4 := by
  have hs := five_radical_margins.1
  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num, ?_⟩
  linarith

/-- The inscribed-disk cap for the containing square in the n=5 proof. -/
lemma five_extension_radical_margin :
    (19 : ℝ) < Real.sqrt 35 * (1+Real.sqrt 5) := by
  have h5 := Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)
  have h35 := Real.sq_sqrt (show (0 : ℝ) ≤ 35 by norm_num)
  have hp5 := Real.sqrt_nonneg 5
  have hp35 := Real.sqrt_nonneg 35
  have hlow := five_radical_margins.2.2.1
  have hid : (Real.sqrt 35*(1+Real.sqrt 5))^2 = 210+70*Real.sqrt 5 := by
    rw [mul_pow, h35]
    nlinarith [h5]
  have hn : 0 ≤ Real.sqrt 35*(1+Real.sqrt 5) := by positivity
  nlinarith

end ThreeUnitSquaresInCircle.Unified
