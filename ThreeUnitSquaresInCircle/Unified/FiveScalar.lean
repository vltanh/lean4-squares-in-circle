import ThreeUnitSquaresInCircle.Unified.RectangleArcs

/-! Scalar estimates for the dodecagon.  The auxiliary radius `5/6` is rational.
This replaces the earlier calculus maximization by a cubic arcsine bound. -/
noncomputable section
open Set
namespace ThreeUnitSquaresInCircle.Unified

def auxFive : ℝ := 5/6

lemma sqrt_five_lt_2237 : Real.sqrt 5 < (2237:ℝ)/1000 := by
  have hh := Real.sq_sqrt (show (0:ℝ) ≤ 5 by norm_num)
  have hp := Real.sqrt_nonneg 5
  nlinarith

lemma five_arcsin_sum {x y : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1/2)
    (hy0 : -1/2 ≤ y) (hy1 : y ≤ 1/2)
    (hsum : x+y ≤ 237/1000) (hside : 3*x+y ≤ 1) :
    Real.arcsin (x/auxFive)+Real.arcsin (y/auxFive) < Real.pi/10 := by
  have ex : x/auxFive = 6/5*x := by rw [auxFive]; ring
  have ey : y/auxFive = 6/5*y := by rw [auxFive]; ring
  rw [ex,ey]
  have hFx := arcsin_le_cubic (x := 6/5*x) (by positivity) (by linarith)
  have hrat : Real.arcsin (6/5*x)+Real.arcsin (6/5*y) < 313/1000 := by
    by_cases hy : 0 ≤ y
    · have hFy := arcsin_le_cubic (x := 6/5*y) (by positivity) (by linarith)
      have hcross := mul_nonneg (mul_nonneg hx0 hy) (add_nonneg hx0 hy)
      have hcubes : x^3+y^3 ≤ (x+y)^3 := by nlinarith
      have hsumcube : (x+y)^3 ≤ (237/1000:ℝ)^3 := by gcongr
      nlinarith
    · have hFy := arcsin_le_self_of_nonpos (x := 6/5*y) (by linarith) (by linarith)
      by_cases hxq : x ≤ 23/60
      · have hc : x^3 ≤ (23/60:ℝ)^3 := by gcongr
        nlinarith
      · have hq : 23/60 ≤ x := (lt_of_not_ge hxq).le
        have hxsq : x^2+x*(23/60)+(23/60:ℝ)^2 ≤ 3/4 := by nlinarith
        have hprod := mul_nonneg (sub_nonneg.mpr hq) (sub_nonneg.mpr hxsq)
        have hc : x^3 ≤ (23/60:ℝ)^3+(3/4)*(x-23/60) := by nlinarith
        nlinarith
  have hp : (313:ℝ)/1000 < Real.pi/10 := by linarith [Real.pi_gt_d2]
  exact hrat.trans hp

lemma five_rectangle_length {a b : ℝ} (ha : 1/2 ≤ a) (hb : 0 ≤ b)
    (hsort : b ≤ a) (h : P5 a b) :
    2*Real.pi/5 < rectangleHi a b auxFive-rectangleLo b auxFive := by
  have ha1 : a ≤ 1 := by linarith [h.1.1]
  have hb1 : b ≤ 1 := by linarith
  have hs : (a-1/2)+(b-1/2) ≤ 237/1000 := by
    linarith [h.2,sqrt_five_lt_2237]
  have hf := five_arcsin_sum (x := a-1/2) (y := b-1/2)
    (by linarith) (by linarith) (by linarith) (by linarith)
    hs (by linarith [h.1.1])
  have hfirst : 2*Real.pi/5 <
      Real.arccos ((a-1/2)/auxFive)-Real.arcsin ((b-1/2)/auxFive) := by
    dsimp [Real.arccos]
    linarith
  have hsecond : 2*Real.pi/5 <
      Real.arcsin ((b+1/2)/auxFive)-Real.arcsin ((b-1/2)/auxFive) := by
    by_cases htop : auxFive ≤ b+1/2
    · have hc : Real.arcsin ((b+1/2)/auxFive)=Real.pi/2 :=
        Real.arcsin_of_one_le ((le_div_iff₀ (by norm_num [auxFive])).mpr (by linarith))
      rw [hc]
      have hx := Real.arcsin_nonneg.mpr
        (show 0 ≤ (a-1/2)/auxFive by dsimp [auxFive]; linarith)
      dsimp [Real.arccos] at hfirst
      linarith
    · have hbhalf : b < 1/2 := by dsimp [auxFive] at htop; linarith
      have htop' : b+1/2 < 5/6 := by dsimp [auxFive] at htop; linarith
      have hu : (b+1/2)/auxFive ∈ Icc (0:ℝ) 1 := by
        rw [show (b+1/2)/auxFive = 6/5*(b+1/2) by rw [auxFive]; ring]
        constructor <;> linarith
      have hv : (1/2-b)/auxFive ∈ Icc (0:ℝ) 1 := by
        dsimp [auxFive]; constructor <;> linarith
      have hh := arcsin_sum_gt_of_sin_lt hu hv
        (show Real.pi/5 ∈ Icc (0:ℝ) (Real.pi/2) by constructor <;> linarith [Real.pi_pos])
        (by norm_num [auxFive]; nlinarith [sin_pi_fifth_lt_three_fifths])
      have he : (b-1/2)/auxFive = -((1/2-b)/auxFive) := by ring
      rw [he,Real.arcsin_neg]
      linarith
  dsimp [rectangleHi,rectangleLo]
  have hh : 2*Real.pi/5+Real.arcsin ((b-1/2)/auxFive) <
      min (Real.arccos ((a-1/2)/auxFive)) (Real.arcsin ((b+1/2)/auxFive)) :=
    lt_min (by linarith) (by linarith)
  linarith

/-- Exterior dodecagon square: an actual occupied open arc longer than 72 degrees. -/
theorem five_exterior_arc (S : UnitSquare) (o : Point)
    (h : P5 (alpha S o) (beta S o)) (hout : ¬ openSquare S o) :
    ∃ A : OpenArc o auxFive {p | openSquare S p}, Real.pi/5 < A.halfWidth := by
  obtain ⟨C,hsort⟩ := sorted_square_chart S o
  have hC : P5 C.a C.b := by
    rcases C.coordinates with ⟨ha,hb⟩ | ⟨ha,hb⟩
    · simpa only [ha,hb] using h
    · simpa only [ha,hb] using p5_swap h
  have ha := C.exterior hsort hout
  have hb := C.nonneg.2
  have ha1 : C.a ≤ 1 := by linarith [hC.1.1]
  have hb1 : C.b ≤ 1 := by linarith
  have hx : (C.a-1/2)/auxFive ∈ Ico (0:ℝ) 1 := by
    dsimp [auxFive]; constructor <;> linarith
  have hy : (C.b-1/2)/auxFive ∈ Icc (-1:ℝ) 1 := by
    dsimp [auxFive]; constructor <;> linarith
  have hcorner : ((C.a-1/2)/auxFive)^2+((C.b-1/2)/auxFive)^2 < 1 := by
    have hx2 : (C.a-1/2)^2 ≤ 1/4 := by nlinarith
    have hy2 : (C.b-1/2)^2 ≤ 1/4 := by nlinarith
    norm_num [auxFive,div_eq_mul_inv]
    nlinarith
  obtain ⟨A,hA⟩ := exterior_arc_from_length C (by norm_num [auxFive])
    (by dsimp [auxFive]; linarith) hx hy hcorner
    (show 0 < 2*Real.pi/5 by positivity) (five_rectangle_length ha hb hsort hC)
  exact ⟨A,by linarith⟩

end ThreeUnitSquaresInCircle.Unified
