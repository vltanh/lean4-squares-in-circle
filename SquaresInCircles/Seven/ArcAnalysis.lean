import SquaresInCircles.Seven.Support
import SquaresInCircles.Seven.TaylorBounds
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv

/-!
# Estimates for the marker arc

Monotonicity from derivatives, arcsine bounds, and the envelope that bounds the
near-edge angle of the marker arc: it is concave, by one polynomial with
positive coefficients in a Bernstein basis, and its maximum is explicit.
-/
noncomputable section
open Set
namespace SquaresInCircles.Seven

lemma monoOn_of_hasDeriv_nonneg {l u : ℝ} {f d : ℝ → ℝ}
    (hc : ContinuousOn f (Icc l u))
    (hd : ∀ x ∈ Ioo l u, HasDerivAt f (d x) x)
    (hs : ∀ x ∈ Ioo l u, 0 ≤ d x) : MonotoneOn f (Icc l u) := by
  apply monotoneOn_of_deriv_nonneg (convex_Icc l u) hc
  · intro x hx
    have hx' : x ∈ Ioo l u := by simpa only [interior_Icc] using hx
    exact (hd x hx').differentiableAt.differentiableWithinAt
  · intro x hx
    have hx' : x ∈ Ioo l u := by simpa only [interior_Icc] using hx
    rw [(hd x hx').deriv]
    exact hs x hx'

lemma antiOn_of_hasDeriv_nonpos {l u : ℝ} {f d : ℝ → ℝ}
    (hc : ContinuousOn f (Icc l u))
    (hd : ∀ x ∈ Ioo l u, HasDerivAt f (d x) x)
    (hs : ∀ x ∈ Ioo l u, d x ≤ 0) : AntitoneOn f (Icc l u) := by
  apply antitoneOn_of_deriv_nonpos (convex_Icc l u) hc
  · intro x hx
    have hx' : x ∈ Ioo l u := by simpa only [interior_Icc] using hx
    exact (hd x hx').differentiableAt.differentiableWithinAt
  · intro x hx
    have hx' : x ∈ Ioo l u := by simpa only [interior_Icc] using hx
    rw [(hd x hx').deriv]
    exact hs x hx'

lemma asin_half : Real.arcsin (1/2 : ℝ) = Real.pi/6 := by
  have h := Real.arcsin_sin (x := Real.pi/6)
    (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])
  simpa only [Real.sin_pi_div_six] using h

lemma asin_upper_remainder {y : ℝ} (hy : -1/2 ≤ y ∧ y ≤ 11/40) :
    Real.arcsin y ≤ y+1331/256000 := by
  by_cases h : 0 ≤ y
  · have hb := arcsin_le_cubic h (by linarith [hy.2])
    have hc : y^3 ≤ (11/40 : ℝ)^3 := pow_le_pow_left₀ h hy.2 3
    nlinarith
  · have hb := arcsin_le_self_of_nonpos (by linarith [hy.1]) (by linarith)
    linarith

lemma weighted_center_bound {a u p r : ℝ} (h : Admissible a u) :
    p*(a+1/2)+r*(u+1/2) ≤ radius*Real.sqrt (p^2+r^2) := by
  have hlow := dot_lower_candidate (p := -p) (r := -r) h.2.2.2
  simpa only [neg_sq] using (show p*(a+1/2)+r*(u+1/2) ≤
      radius*Real.sqrt ((-p)^2+(-r)^2) by linarith)

/-- The positive numerator of the curvature of the vertical-endpoint envelope. -/
def arcCurvaturePolynomial (x : ℝ) : ℝ :=
  676*(1-x^2)^3-9*x^2*(9-8*x-4*x^2)^3

private def arcPowerCoefficients : Fin 9 → ℝ :=
  ![692224,5537792,14435008,16639232,10490656,
    6552896,3921235,805934,55780]

lemma arcCurvaturePolynomial_pos {x : ℝ} (hx : 0 ≤ x ∧ x ≤ 3/4) :
    0 < arcCurvaturePolynomial x := by
  let z := 4*x/3
  have hz : 0 ≤ z ∧ z ≤ 1 := by dsimp [z]; constructor <;> linarith [hx.1,hx.2]
  let term : Fin 9 → ℝ := fun i =>
    arcPowerCoefficients i*z^i.val*(1-z)^(8-i.val)
  have hc (i : Fin 9) : 0 < arcPowerCoefficients i := by
    fin_cases i <;> norm_num [arcPowerCoefficients]
  have ht (i : Fin 9) : 0 ≤ term i := by
    have hc' := (hc i).le
    have h0 := hz.1
    have h1 : 0 ≤ 1-z := sub_nonneg.mpr hz.2
    dsimp [term]
    positivity
  have hsum : 0 < ∑ i, term i := by
    by_cases he : z = 1
    · have hlast : 0 < term 8 := by norm_num [term,he,arcPowerCoefficients]
      exact hlast.trans_le (Finset.single_le_sum (fun i _ => ht i) (Finset.mem_univ _))
    · have h1 : 0 < 1-z := by
        by_contra hn
        exact he (le_antisymm hz.2 (by linarith))
      have hfirst : 0 < term 0 := by
        norm_num [term,arcPowerCoefficients]
        positivity
      exact hfirst.trans_le (Finset.single_le_sum (fun i _ => ht i) (Finset.mem_univ _))
  have hid : 1024*arcCurvaturePolynomial x = ∑ i, term i := by
    simp [term,arcPowerCoefficients,Fin.sum_univ_succ,z,arcCurvaturePolynomial]
    ring
  linarith

/-- Upper envelope for side label plus arcsine of the near vertical edge. -/
def arcEnvelope (x : ℝ) : ℝ :=
  Real.pi/6+1/24+(1/3)*Real.sqrt (targetSq-(x+1)^2)+Real.arcsin x-3*x/4

def arcEnvelopeDeriv (x : ℝ) : ℝ :=
  1/Real.sqrt (1-x^2)-3/4-(x+1)/(3*Real.sqrt (targetSq-(x+1)^2))

def arcEnvelopeSecond (x : ℝ) : ℝ :=
  x/(Real.sqrt (1-x^2))^3-targetSq/(3*(Real.sqrt (targetSq-(x+1)^2))^3)

lemma arc_radicands {x : ℝ} (hx : 0 ≤ x ∧ x ≤ 3/4) :
    0 < 1-x^2 ∧ 0 < targetSq-(x+1)^2 := by
  dsimp [targetSq]
  constructor <;> nlinarith [hx.1,hx.2]

lemma arcEnvelope_hasDeriv {x : ℝ} (hx : 0 ≤ x ∧ x ≤ 3/4) :
    HasDerivAt arcEnvelope (arcEnvelopeDeriv x) x := by
  have hp := arc_radicands hx
  have hB : Real.sqrt (targetSq-(x+1)^2) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.mpr hp.2)
  have hd : HasDerivAt (fun y : ℝ => targetSq-(y+1)^2) (-(2*(x+1))) x := by
    simpa using (((hasDerivAt_id x).add_const 1).pow 2).const_sub targetSq
  have hs := (hd.sqrt (ne_of_gt hp.2)).const_mul (1/3 : ℝ)
  have ha := Real.hasDerivAt_arcsin (x := x) (by linarith [hx.1]) (by linarith [hx.2])
  have h := ((hs.const_add (Real.pi/6+1/24)).add ha).sub
    ((hasDerivAt_id x).const_mul (3/4 : ℝ))
  convert h using 1
  · ext y; dsimp [arcEnvelope]; ring
  · dsimp [arcEnvelopeDeriv]
    field_simp
    ring

lemma arcEnvelopeDeriv_hasDeriv {x : ℝ} (hx : 0 ≤ x ∧ x ≤ 3/4) :
    HasDerivAt arcEnvelopeDeriv (arcEnvelopeSecond x) x := by
  have hp := arc_radicands hx
  set A := Real.sqrt (1-x^2) with hAdef
  set B := Real.sqrt (targetSq-(x+1)^2) with hBdef
  have hA : 0 < A := Real.sqrt_pos.mpr hp.1
  have hB : 0 < B := Real.sqrt_pos.mpr hp.2
  have hB2 : B^2=targetSq-(x+1)^2 := Real.sq_sqrt hp.2.le
  have dA : HasDerivAt (fun y : ℝ => Real.sqrt (1-y^2)) (-x/A) x := by
    have h1 : HasDerivAt (fun y : ℝ => 1-y^2) (-(2*x)) x := by
      simpa using (hasDerivAt_pow 2 x).const_sub 1
    have h := h1.sqrt (ne_of_gt hp.1)
    rw [← hAdef] at h
    refine h.congr_deriv ?_
    field_simp
  have dB : HasDerivAt (fun y : ℝ => Real.sqrt (targetSq-(y+1)^2)) (-(x+1)/B) x := by
    have h1 : HasDerivAt (fun y : ℝ => targetSq-(y+1)^2) (-(2*(x+1))) x := by
      simpa using (((hasDerivAt_id x).add_const 1).pow 2).const_sub targetSq
    have h := h1.sqrt (ne_of_gt hp.2)
    rw [← hBdef] at h
    refine h.congr_deriv ?_
    field_simp
  have hi : HasDerivAt (fun y : ℝ => 1/Real.sqrt (1-y^2)) (x/A^3) x := by
    have h := (hasDerivAt_const x (1 : ℝ)).div dA (ne_of_gt hA)
    rw [← hAdef] at h
    refine h.congr_deriv ?_
    field_simp
    ring
  have hj : HasDerivAt (fun y : ℝ => (y+1)/(3*Real.sqrt (targetSq-(y+1)^2)))
      (targetSq/(3*B^3)) x := by
    have h := ((hasDerivAt_id x).add_const 1).div (dB.const_mul 3)
      (by positivity : 3*B ≠ 0)
    rw [← hBdef] at h
    refine h.congr_deriv ?_
    simp only [id]
    field_simp
    linarith
  exact (hi.sub_const (3/4 : ℝ)).sub hj

lemma arcEnvelopeSecond_neg {x : ℝ} (hx : 0 ≤ x ∧ x ≤ 3/4) :
    arcEnvelopeSecond x < 0 := by
  have hp := arc_radicands hx
  let A := Real.sqrt (1-x^2)
  let B := Real.sqrt (targetSq-(x+1)^2)
  have hA : 0 < A := Real.sqrt_pos.mpr hp.1
  have hB : 0 < B := Real.sqrt_pos.mpr hp.2
  have hA2 : A^2=1-x^2 := Real.sq_sqrt hp.1.le
  have hB2 : B^2=targetSq-(x+1)^2 := Real.sq_sqrt hp.2.le
  have hpoly := arcCurvaturePolynomial_pos hx
  have hid :
      64*((targetSq*A^3)^2-(3*x*B^3)^2)=arcCurvaturePolynomial x := by
    calc
      _ = 64*(targetSq^2*(A^2)^3-9*x^2*(B^2)^3) := by ring
      _ = _ := by rw [hA2,hB2]; dsimp [arcCurvaturePolynomial,targetSq]; ring
  have hleft : 0 ≤ 3*x*B^3 := by
    have hx0 := hx.1
    positivity
  have hright : 0 < targetSq*A^3 := by dsimp [targetSq]; positivity
  have hlt : 3*x*B^3 < targetSq*A^3 := by nlinarith
  have hrepr : arcEnvelopeSecond x =
      (3*x*B^3-targetSq*A^3)/(3*A^3*B^3) := by
    change x/A^3-targetSq/(3*B^3) = _
    field_simp [ne_of_gt hA,ne_of_gt hB]
  rw [hrepr]
  exact div_neg_of_neg_of_pos (by linarith) (by positivity)

lemma arcEnvelopeDeriv_antitone : AntitoneOn arcEnvelopeDeriv (Icc (0 : ℝ) (3/4)) := by
  apply antiOn_of_hasDeriv_nonpos
  · intro x hx
    exact (arcEnvelopeDeriv_hasDeriv hx).continuousAt.continuousWithinAt
  · intro x hx
    exact arcEnvelopeDeriv_hasDeriv ⟨hx.1.le,hx.2.le⟩
  · intro x hx
    exact (arcEnvelopeSecond_neg ⟨hx.1.le,hx.2.le⟩).le

lemma arcEnvelopeDeriv_quarter_neg : arcEnvelopeDeriv (1/4) < 0 := by
  let A := Real.sqrt (15/16 : ℝ)
  let B := Real.sqrt (27/16 : ℝ)
  have hA : 0 < A := Real.sqrt_pos.mpr (by norm_num)
  have hB : 0 < B := Real.sqrt_pos.mpr (by norm_num)
  have ha2 : A^2=15/16 := Real.sq_sqrt (by norm_num)
  have hb2 : B^2=27/16 := Real.sq_sqrt (by norm_num)
  have hAa : 20/21 < A := by nlinarith
  have hBb : B < 25/18 := by nlinarith
  have ha : 1/A < 21/20 := (div_lt_iff₀ hA).mpr (by nlinarith)
  have hb : (3/10 : ℝ) < (5/4)/(3*B) :=
    (lt_div_iff₀ (by positivity)).mpr (by nlinarith)
  have he : arcEnvelopeDeriv (1/4) = 1/A-3/4-(5/4)/(3*B) := by
    norm_num [arcEnvelopeDeriv,targetSq,A,B]
  rw [he]
  linarith

lemma arcEnvelope_antitone_right : AntitoneOn arcEnvelope (Icc (1/4 : ℝ) (3/4)) := by
  apply antiOn_of_hasDeriv_nonpos
  · intro x hx
    exact (arcEnvelope_hasDeriv ⟨by linarith [hx.1],hx.2⟩).continuousAt.continuousWithinAt
  · intro x hx
    exact arcEnvelope_hasDeriv ⟨by linarith [hx.1],hx.2.le⟩
  · intro x hx
    have h := arcEnvelopeDeriv_antitone
      (show (1/4 : ℝ) ∈ Icc (0 : ℝ) (3/4) by norm_num)
      (show x ∈ Icc (0 : ℝ) (3/4) by constructor <;> linarith [hx.1,hx.2]) hx.1.le
    exact h.trans arcEnvelopeDeriv_quarter_neg.le

lemma arcEnvelope_bound_small {x : ℝ} (hx : 0 ≤ x ∧ x ≤ 1/4) :
    arcEnvelope x ≤ Real.pi/6+(Real.sqrt 87061-86)/384 := by
  have ha := arcsin_le_cubic hx.1 (by linarith [hx.2])
  have hm := mul_nonneg hx.1 (show 0 ≤ 1/16-x^2 by nlinarith [hx.2])
  have hasin : Real.arcsin x ≤ (65/64)*x := by nlinarith
  let B := Real.sqrt (targetSq-(x+1)^2)
  have hp := (arc_radicands ⟨hx.1,by linarith [hx.2]⟩).2
  have hB : 0 ≤ B := Real.sqrt_nonneg _
  have hB2 : B^2=targetSq-(x+1)^2 := Real.sq_sqrt hp.le
  let r := Real.sqrt (87061 : ℝ)
  have hr : 0 ≤ r := Real.sqrt_nonneg _
  have hr2 : r^2=87061 := Real.sq_sqrt (by norm_num)
  have hid : ((17/64)*(x+1)+(1/3)*B)^2+
      ((1/3)*(x+1)-(17/64)*B)^2 =
      ((17/64 : ℝ)^2+(1/3)^2)*((x+1)^2+B^2) := by ring
  have hcs : (17/64)*(x+1)+(1/3)*B ≤ r/384 := by
    have he : (x+1)^2+B^2=13/4 := by dsimp [targetSq] at hB2; linarith
    rw [he] at hid
    have hsq := sq_nonneg ((1/3)*(x+1)-(17/64)*B)
    nlinarith
  dsimp [arcEnvelope]
  change Real.pi/6+1/24+(1/3)*B+Real.arcsin x-3*x/4 ≤ _
  dsimp [r] at hcs
  linarith

lemma arcEnvelope_bound {x : ℝ} (hx : 0 ≤ x ∧ x ≤ 3/4) :
    arcEnvelope x ≤ Real.pi/6+(Real.sqrt 87061-86)/384 := by
  by_cases h : x ≤ 1/4
  · exact arcEnvelope_bound_small ⟨hx.1,h⟩
  · exact (arcEnvelope_antitone_right
      (show (1/4 : ℝ) ∈ Icc (1/4 : ℝ) (3/4) by norm_num)
      ⟨(le_of_not_ge h),hx.2⟩ (le_of_not_ge h)).trans
      (arcEnvelope_bound_small (by norm_num))

end SquaresInCircles.Seven
