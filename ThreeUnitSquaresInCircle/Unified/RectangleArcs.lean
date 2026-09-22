import ThreeUnitSquaresInCircle.Unified.ElementaryTrig

/-! The occupied arc of a canonical exterior square.  All planar membership
claims are for the open square, so disjointness is literal, not almost everywhere. -/
noncomputable section
open Set
namespace ThreeUnitSquaresInCircle.Unified

lemma near_corner_angle {u v : ℝ} (hu : u ∈ Ico (0:ℝ) 1)
    (hv : v ∈ Icc (-1:ℝ) 1) (hcorner : u^2+v^2 < 1) :
    -Real.arccos u < Real.arcsin v := by
  have huA : Real.arcsin u < Real.pi/2 := by
    apply (Real.arcsin_lt_iff_lt_sin
      (show u ∈ Icc (-1:ℝ) 1 by exact ⟨by linarith [hu.1],hu.2.le⟩)
      (show Real.pi/2 ∈ Icc (-(Real.pi/2)) (Real.pi/2) by constructor <;> linarith [Real.pi_pos])).mpr
    simpa using hu.2
  have hu0 : 0 ≤ Real.arcsin u := Real.arcsin_nonneg.mpr hu.1
  by_cases hv0 : 0 ≤ v
  · have hh := Real.arcsin_nonneg.mpr hv0
    dsimp [Real.arccos]
    linarith
  · have hcos0 : 0 ≤ Real.cos (Real.arcsin u) := Real.cos_nonneg_of_mem_Icc
      ⟨by linarith [Real.pi_pos],huA.le⟩
    have hunit := Real.sin_sq_add_cos_sq (Real.arcsin u)
    rw [Real.sin_arcsin (by linarith [hu.1]) hu.2.le] at hunit
    have hvc : -v < Real.cos (Real.arcsin u) := by nlinarith
    have ha := (Real.arcsin_lt_iff_lt_sin
      (show -v ∈ Icc (-1:ℝ) 1 by constructor <;> linarith [hv.1,hv.2])
      (show Real.pi/2-Real.arcsin u ∈ Icc (-(Real.pi/2)) (Real.pi/2) by
        constructor <;> linarith [Real.pi_pos])).mpr
      (by simpa only [Real.sin_pi_div_two_sub] using hvc)
    rw [Real.arcsin_neg] at ha
    dsimp [Real.arccos]
    linarith

def rectangleLo (b r : ℝ) : ℝ := Real.arcsin ((b-1/2)/r)
def rectangleHi (a b r : ℝ) : ℝ :=
  min (Real.arccos ((a-1/2)/r)) (Real.arcsin ((b+1/2)/r))

lemma rectangle_interval_mem {a b r t : ℝ} (hr : 0 < r) (hfar : r < a+1/2)
    (hx : (a-1/2)/r ∈ Ico (0:ℝ) 1)
    (hy : (b-1/2)/r ∈ Icc (-1:ℝ) 1)
    (hcorner : ((a-1/2)/r)^2+((b-1/2)/r)^2 < 1)
    (ht : t ∈ Ioo (rectangleLo b r) (rectangleHi a b r)) :
    |r*Real.cos t-a| < 1/2 ∧ |r*Real.sin t-b| < 1/2 := by
  let A := Real.arccos ((a-1/2)/r)
  have hnear := near_corner_angle hx hy hcorner
  have hta : t < A := (lt_min_iff.mp ht.2).1
  have htb : t < Real.arcsin ((b+1/2)/r) := (lt_min_iff.mp ht.2).2
  have htl : -A < t := lt_trans hnear ht.1
  have hA0 : 0 ≤ A := Real.arccos_nonneg _
  have hA1 : A ≤ Real.pi/2 := by
    have hh := Real.arcsin_nonneg.mpr hx.1
    dsimp [A,Real.arccos]
    linarith
  have htdom : t ∈ Ioo (-(Real.pi/2)) (Real.pi/2) :=
    ⟨by linarith,by linarith⟩
  have htc : (a-1/2)/r < Real.cos t := by
    have hh := Real.cos_lt_cos_of_nonneg_of_le_pi (abs_nonneg t)
      (show A ≤ Real.pi by linarith [Real.pi_pos])
      (abs_lt.mpr ⟨htl,hta⟩)
    rw [Real.cos_arccos (by linarith [hx.1]) hx.2.le] at hh
    simpa only [Real.cos_abs] using hh
  have hts0 : (b-1/2)/r < Real.sin t :=
    (Real.arcsin_lt_iff_lt_sin' ⟨htdom.1,htdom.2.le⟩).mp ht.1
  have hts1 : Real.sin t < (b+1/2)/r :=
    (Real.lt_arcsin_iff_sin_lt' ⟨htdom.1.le,htdom.2⟩).mp htb
  have hxc := (div_lt_iff₀ hr).mp htc
  have hyc0 := (div_lt_iff₀ hr).mp hts0
  have hyc1 := (lt_div_iff₀ hr).mp hts1
  have hxr := mul_le_mul_of_nonneg_left (Real.cos_le_one t) hr.le
  exact ⟨abs_lt.mpr ⟨by nlinarith,by nlinarith⟩,
    abs_lt.mpr ⟨by nlinarith,by nlinarith⟩⟩

lemma rectangle_length_le_two_pi (a b r : ℝ) :
    rectangleHi a b r-rectangleLo b r ≤ 2*Real.pi := by
  have hu := Real.arccos_le_pi ((a-1/2)/r)
  have hl := Real.neg_pi_div_two_le_arcsin ((b-1/2)/r)
  have hh := min_le_left (Real.arccos ((a-1/2)/r)) (Real.arcsin ((b+1/2)/r))
  dsimp [rectangleHi,rectangleLo]
  linarith [Real.pi_pos]

lemma exterior_arc_from_length {S : UnitSquare} {o : Point} (C : SquareChart S o)
    {r L : ℝ} (hr : 0 < r) (hfar : r < C.a+1/2)
    (hx : (C.a-1/2)/r ∈ Ico (0:ℝ) 1)
    (hy : (C.b-1/2)/r ∈ Icc (-1:ℝ) 1)
    (hcorner : ((C.a-1/2)/r)^2+((C.b-1/2)/r)^2 < 1)
    (hL : 0 < L) (hlen : L < rectangleHi C.a C.b r-rectangleLo C.b r) :
    ∃ A : OpenArc o r {p | openSquare S p}, L/2 < A.halfWidth := by
  obtain ⟨A,hA⟩ := C.arc r (rectangleLo C.b r) (rectangleHi C.a C.b r)
    (by linarith) (rectangle_length_le_two_pi _ _ _)
    (fun t ht => rectangle_interval_mem hr hfar hx hy hcorner ht)
  exact ⟨A,by rw [hA]; linarith⟩

end ThreeUnitSquaresInCircle.Unified
