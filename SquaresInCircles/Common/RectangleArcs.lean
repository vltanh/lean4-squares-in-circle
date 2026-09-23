import SquaresInCircles.Common.Charts

/-! Occupied arcs of an exterior square, from its sorted chart coordinates
`b ≤ a` with `1/2 ≤ a`: the cap cut off by the near edge and clipped by the
side edge, and the rectangle interval that also meets the far side. All planar
membership claims are for the open square, so disjointness is literal, not
almost everywhere. -/
noncomputable section
open Set
namespace SquaresInCircles

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

lemma cap_length_identity (A V : ℝ) : A-max (-A) (-V)=min (2*A) (A+V) := by
  by_cases h : A ≤ V
  · rw [max_eq_left (by linarith),min_eq_left (by linarith)]
    ring
  · rw [max_eq_right (by linarith),min_eq_right (by linarith)]
    ring

/-- The occupied interval of an exterior square: between the near edge,
`±A` with `A = arccos ((a-1/2)/r)`, and the side edges `arcsin ((b∓1/2)/r)`. -/
lemma cap_mem {a b r t : ℝ} (hr : 0 < r) (hfar : r < a+1/2)
    (hx : (a-1/2)/r ∈ Icc (0:ℝ) 1)
    (ht : t ∈ Ioo (max (-Real.arccos ((a-1/2)/r)) (Real.arcsin ((b-1/2)/r)))
      (min (Real.arccos ((a-1/2)/r)) (Real.arcsin ((b+1/2)/r)))) :
    |r*Real.cos t-a| < 1/2 ∧ |r*Real.sin t-b| < 1/2 := by
  have hta := (lt_min_iff.mp ht.2).1
  have htl := (max_lt_iff.mp ht.1).1
  have hA := Real.arccos_le_pi_div_two.mpr hx.1
  have htdom : t ∈ Ioo (-(Real.pi/2)) (Real.pi/2) := ⟨by linarith,by linarith⟩
  have htc : (a-1/2)/r < Real.cos t := by
    have hh := Real.cos_lt_cos_of_nonneg_of_le_pi (abs_nonneg t)
      (show Real.arccos ((a-1/2)/r) ≤ Real.pi by linarith [Real.pi_pos])
      (abs_lt.mpr ⟨htl,hta⟩)
    rwa [Real.cos_arccos (by linarith [hx.1]) hx.2,Real.cos_abs] at hh
  have hts0 : (b-1/2)/r < Real.sin t :=
    (Real.arcsin_lt_iff_lt_sin' ⟨htdom.1,htdom.2.le⟩).mp (max_lt_iff.mp ht.1).2
  have hts1 : Real.sin t < (b+1/2)/r :=
    (Real.lt_arcsin_iff_sin_lt' ⟨htdom.1.le,htdom.2⟩).mp (lt_min_iff.mp ht.2).2
  have hxc := (div_lt_iff₀ hr).mp htc
  have hyc0 := (div_lt_iff₀ hr).mp hts0
  have hyc1 := (lt_div_iff₀ hr).mp hts1
  have hxr := mul_le_mul_of_nonneg_left (Real.cos_le_one t) hr.le
  exact ⟨abs_lt.mpr ⟨by linarith,by linarith⟩,abs_lt.mpr ⟨by linarith,by linarith⟩⟩

/-- On a circle of radius at most `1/2` the far side is out of reach, and the
occupied interval is the cap `(max (-A) (-V), A)` with `V = arcsin ((1/2-b)/r)`. -/
lemma cap_mem_near {a b r t : ℝ} (hr : 0 < r) (hr2 : r ≤ 1/2)
    (ha : 1/2 ≤ a) (ha1 : a-1/2 ≤ r) (hb : 0 ≤ b)
    (ht : t ∈ Ioo (max (-Real.arccos ((a-1/2)/r)) (-Real.arcsin ((1/2-b)/r)))
      (Real.arccos ((a-1/2)/r))) :
    |r*Real.cos t-a| < 1/2 ∧ |r*Real.sin t-b| < 1/2 := by
  have hx : (a-1/2)/r ∈ Icc (0:ℝ) 1 :=
    ⟨div_nonneg (by linarith) hr.le,(div_le_one hr).mpr ha1⟩
  have htop : Real.arcsin ((b+1/2)/r)=Real.pi/2 :=
    Real.arcsin_of_one_le ((le_div_iff₀ hr).mpr (by linarith))
  refine cap_mem hr (by linarith) hx ?_
  rwa [htop,min_eq_left (Real.arccos_le_pi_div_two.mpr hx.1),
    show (b-1/2)/r=-((1/2-b)/r) by ring,Real.arcsin_neg]

/-- The cap as an occupied arc: its length is `min (2A) (A+V)`, and a full cap,
`A ≤ V`, is centred on the square's radial phase. -/
lemma SquareChart.cap_arc {S : UnitSquare} {o : Point} (C : SquareChart S o) {r : ℝ}
    (hr : 0 < r) (hr2 : r ≤ 1/2) (ha : 1/2 ≤ C.a) (ha1 : C.a-1/2 < r) (hb : C.b ≤ 1/2) :
    ∃ A : OpenArc o r {p | openSquare S p},
      2*A.halfWidth=min (2*Real.arccos ((C.a-1/2)/r))
        (Real.arccos ((C.a-1/2)/r)+Real.arcsin ((1/2-C.b)/r)) ∧
      (Real.arccos ((C.a-1/2)/r) ≤ Real.arcsin ((1/2-C.b)/r) → A.center=C.phase) := by
  have hA := Real.arccos_le_pi_div_two.mpr (div_nonneg (by linarith : 0 ≤ C.a-1/2) hr.le)
  have hA0 := Real.arccos_pos.mpr ((div_lt_one hr).mpr ha1)
  have hV0 := Real.arcsin_nonneg.mpr (div_nonneg (by linarith : 0 ≤ 1/2-C.b) hr.le)
  obtain ⟨A,hA',hc⟩ := C.arc r _ _ (by rw [max_lt_iff]; constructor <;> linarith)
    (by have h := le_max_left (-Real.arccos ((C.a-1/2)/r)) (-Real.arcsin ((1/2-C.b)/r))
        linarith [Real.pi_pos])
    (fun t ht => cap_mem_near hr hr2 ha ha1.le C.nonneg.2 ht)
  refine ⟨A,by rw [hA',← cap_length_identity]; ring,fun hfull => ?_⟩
  rw [hc,max_eq_left (by linarith)]
  simp [chartAngle]

def rectangleLo (b r : ℝ) : ℝ := Real.arcsin ((b-1/2)/r)
def rectangleHi (a b r : ℝ) : ℝ :=
  min (Real.arccos ((a-1/2)/r)) (Real.arcsin ((b+1/2)/r))

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
  obtain ⟨A,hA,-⟩ := C.arc r (rectangleLo C.b r) (rectangleHi C.a C.b r)
    (by linarith) (rectangle_length_le_two_pi _ _ _)
    (fun t ht => cap_mem hr hfar ⟨hx.1,hx.2.le⟩
      (by rwa [max_eq_right (near_corner_angle hx hy hcorner).le]))
  exact ⟨A,by rw [hA]; linarith⟩

end SquaresInCircles
