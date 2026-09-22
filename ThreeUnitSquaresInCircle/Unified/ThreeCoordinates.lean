import ThreeUnitSquaresInCircle.Unified.ThreeExterior
import ThreeUnitSquaresInCircle.Unified.ArcMetric

/-!
# Cartesian access to the square charts

The final overlap witness must concern actual square interiors. The lemmas
here recover Cartesian membership from the existing all-radius chart identity.
-/
noncomputable section
open Set
namespace ThreeUnitSquaresInCircle.Unified

/-- A point with coordinates `(x,y)` in the positively oriented frame at `phase`. -/
def pointInDirection (o : Point) (phase : Direction) (x y : ℝ) : Point :=
  (o.1+phase.cos*x-phase.sin*y, o.2+phase.sin*x+phase.cos*y)

lemma pointInDirection_polar (o : Point) (phase : Direction) (r t : ℝ) :
    pointInDirection o phase (r*Real.cos t) (r*Real.sin t) =
      circlePoint o r (phase+(t:Direction)) := by
  apply Prod.ext <;>
    simp only [pointInDirection,circlePoint,Real.Angle.cos_add,Real.Angle.sin_add,
      Real.Angle.cos_coe,Real.Angle.sin_coe] <;> ring

lemma pointInDirection_norm (o : Point) (phase : Direction) (x y : ℝ) :
    normSq (sub (pointInDirection o phase x y) o)=x^2+y^2 := by
  calc
    _ = (phase.cos^2+phase.sin^2)*(x^2+y^2) := by
      dsimp [normSq,sub,pointInDirection]; ring
    _ = _ := by rw [Real.Angle.cos_sq_add_sin_sq]; ring

lemma plane_polar (x y : ℝ) :
    ∃ r t : ℝ, r*Real.cos t=x ∧ r*Real.sin t=y := by
  by_cases hz : x=0 ∧ y=0
  · exact ⟨0,0,by simp [hz.1],by simp [hz.2]⟩
  let r := Real.sqrt (x^2+y^2)
  have hr : 0 < r := Real.sqrt_pos.mpr (by
    by_contra hn
    have hx : x=0 := by nlinarith [sq_nonneg x,sq_nonneg y]
    have hy : y=0 := by nlinarith [sq_nonneg x,sq_nonneg y]
    exact hz ⟨hx,hy⟩)
  have hr2 : r^2=x^2+y^2 := Real.sq_sqrt (by positivity)
  let F : UnitSquare :=
    { center := (0,0)
      cosine := x/r
      sine := y/r
      unit := by
        rw [div_pow,div_pow,← add_div,← hr2]
        exact div_self (ne_of_gt (sq_pos_of_pos hr)) }
  obtain ⟨t,htc,hts⟩ := frame_angle F
  refine ⟨r,t,?_,?_⟩
  · rw [htc]
    dsimp [F]
    field_simp [ne_of_gt hr]
  · rw [hts]
    dsimp [F]
    field_simp [ne_of_gt hr]

/-- Reversal of a chart changes only the sign of its transverse center coordinate. -/
def SquareChart.signedB {S : UnitSquare} {o : Point} (C : SquareChart S o) : ℝ :=
  if C.reversed then -C.b else C.b

lemma SquareChart.abs_signedB {S : UnitSquare} {o : Point} (C : SquareChart S o) :
    |C.signedB|=C.b := by
  unfold SquareChart.signedB
  split_ifs <;> simp only [abs_neg,abs_of_nonneg C.nonneg.2]

lemma SquareChart.cartesian {S : UnitSquare} {o : Point} (C : SquareChart S o)
    (x y : ℝ) :
    openSquare S (pointInDirection o C.phase x y) ↔
      |x-C.a| < 1/2 ∧ |y-C.signedB| < 1/2 := by
  obtain ⟨r,t,hx,hy⟩ := plane_polar x y
  rw [← hx,← hy,pointInDirection_polar]
  cases hrev : C.reversed
  · have h := C.membership r t
    simpa only [chartAngle,hrev,Bool.false_eq_true,ite_false,SquareChart.signedB] using h
  · have h := C.membership r (-t)
    have habs : |-(r*Real.sin t)-C.b|=|r*Real.sin t+C.b| := by
      rw [show -(r*Real.sin t)-C.b=-(r*Real.sin t+C.b) by ring,abs_neg]
    simpa only [chartAngle,hrev,ite_true,neg_neg,Real.cos_neg,Real.sin_neg,
      mul_neg,SquareChart.signedB,sub_neg_eq_add,habs] using h

lemma pointInDirection_transition (o : Point) (φ ψ : Direction) (x y : ℝ) :
    pointInDirection o φ x y = pointInDirection o ψ
      ((ψ-φ).cos*x+(ψ-φ).sin*y)
      (-(ψ-φ).sin*x+(ψ-φ).cos*y) := by
  have hu := Real.Angle.cos_sq_add_sin_sq ψ
  apply Prod.ext
  · calc
      _ = o.1+(ψ.cos^2+ψ.sin^2)*(φ.cos*x-φ.sin*y) := by
        dsimp [pointInDirection]
        rw [hu]
        ring
      _ = _ := by
        simp only [pointInDirection,sub_eq_add_neg,Real.Angle.cos_add,Real.Angle.sin_add,
          Real.Angle.cos_neg,Real.Angle.sin_neg]
        ring
  · calc
      _ = o.2+(ψ.cos^2+ψ.sin^2)*(φ.sin*x+φ.cos*y) := by
        dsimp [pointInDirection]
        rw [hu]
        ring
      _ = _ := by
        simp only [pointInDirection,sub_eq_add_neg,Real.Angle.cos_add,Real.Angle.sin_add,
          Real.Angle.cos_neg,Real.Angle.sin_neg]
        ring

/-- The disk given by the nearer side of a containing square is really inside it. -/
lemma inscribed_disk_mem (S : UnitSquare) (o : Point) {a p : ℝ}
    (hp : 0 < p) (hpa : a+p=1/2)
    (hx : alpha S o ≤ a) (hy : beta S o ≤ a) {z : Point}
    (hz : normSq (sub z o) < p^2) : openSquare S z := by
  have hu := frame_norm S (sub z o)
  have hX : |frameX S (sub z o)| < p := by
    apply abs_lt.mpr
    constructor <;> nlinarith [sq_nonneg (frameY S (sub z o))]
  have hY : |frameY S (sub z o)| < p := by
    apply abs_lt.mpr
    constructor <;> nlinarith [sq_nonneg (frameX S (sub z o))]
  have heX : localX S z=frameX S (sub z o)+localX S o := by
    dsimp [localX,frameX,sub]; ring
  have heY : localY S z=frameY S (sub z o)+localY S o := by
    dsimp [localY,frameY,sub]; ring
  refine ⟨?_,?_⟩
  · rw [heX]
    have hb := abs_add (frameX S (sub z o)) (localX S o)
    change |localX S o| ≤ a at hx
    linarith
  · rw [heY]
    have hb := abs_add (frameY S (sub z o)) (localY S o)
    change |localY S o| ≤ a at hy
    linarith

/-- Build an occupied symmetric cap with its midpoint direction retained. -/
def symmetricChartArc {S : UnitSquare} {o : Point} (C : SquareChart S o)
    (r A : ℝ) (hA : 0 < A) (hApi : A ≤ Real.pi)
    (hm : ∀ t ∈ Ioo (-A) A,
      |r*Real.cos t-C.a| < 1/2 ∧ |r*Real.sin t-C.b| < 1/2) :
    OpenArc o r {z | openSquare S z} where
  center := C.phase
  halfWidth := A
  positive := hA
  atMostPi := hApi
  inside := by
    intro θ hθ
    let t := (θ-C.phase).toReal
    have ht : |t| < A := by simpa only [direction_dist] using hθ
    have he : θ=C.phase+(t:Direction) := direction_offset _ _
    cases hr : C.reversed
    · have h := (C.membership r t).mpr (hm t (abs_lt.mp ht))
      simpa only [chartAngle,hr,Bool.false_eq_true,ite_false,he] using h
    · have h := (C.membership r (-t)).mpr (hm (-t)
        ⟨by linarith [(abs_lt.mp ht).2],by linarith [(abs_lt.mp ht).1]⟩)
      simpa only [chartAngle,hr,ite_true,neg_neg,he] using h

lemma near_axis_angles {φ ψ : Direction}
    (hlo : 2*Real.pi/3 ≤ dist φ ψ)
    (hhi : dist φ ψ < 2*Real.pi/3+1/12) :
    -(3/5:ℝ) < (ψ-φ).cos ∧ (ψ-φ).cos ≤ -1/2 ∧
      4/5 < |(ψ-φ).sin| ∧ |(ψ-φ).sin| < 7/8 := by
  let γ := |(ψ-φ).toReal|
  have hγ : γ=dist φ ψ := by rw [dist_comm,direction_dist]
  have hγpi : γ ≤ Real.pi := (ψ-φ).abs_toReal_le_pi
  have hcγ : Real.cos γ=(ψ-φ).cos := by
    have h := congrArg Real.Angle.cos (Real.Angle.coe_toReal (ψ-φ))
    simpa only [γ,Real.cos_abs,Real.Angle.cos_coe] using h
  have hcbase : Real.cos (2*Real.pi/3)=-(1/2:ℝ) := by
    rw [show 2*Real.pi/3=2*(Real.pi/3) by ring,Real.cos_two_mul,
      Real.cos_pi_div_three]
    norm_num
  have hcle : Real.cos γ ≤ -1/2 := by
    rcases eq_or_lt_of_le (hlo.trans_eq hγ.symm) with he | he
    · rw [← he,hcbase]
    · have hh := Real.cos_lt_cos_of_nonneg_of_le_pi
        (show 0 ≤ 2*Real.pi/3 by positivity) hγpi he
      rw [hcbase] at hh
      exact hh.le
  let ε := γ-2*Real.pi/3
  have hε0 : 0 ≤ ε := by dsimp [ε]; linarith
  have hε1 : ε < 1/12 := by dsimp [ε]; linarith
  have hεpi : ε ≤ Real.pi := by dsimp [ε]; linarith [Real.pi_pos]
  have hsε0 := Real.sin_nonneg_of_nonneg_of_le_pi hε0 hεpi
  have hsε1 := Real.sin_le hε0
  have hprod := mul_nonneg hsε0 (sub_nonneg.mpr (Real.sin_le_one (2*Real.pi/3)))
  have hid : Real.cos γ =
      -(1/2)*Real.cos ε-Real.sin (2*Real.pi/3)*Real.sin ε := by
    rw [show γ=2*Real.pi/3+ε by dsimp [ε]; ring,Real.cos_add,hcbase]
  have hclo : -(3/5:ℝ) < Real.cos γ := by
    nlinarith [Real.cos_le_one ε]
  rw [hcγ] at hcle hclo
  have hu := Real.Angle.cos_sq_add_sin_sq (ψ-φ)
  have hsabs := abs_nonneg (ψ-φ).sin
  have hssq : |(ψ-φ).sin|^2=(ψ-φ).sin^2 := sq_abs _
  have hcSqUp : (ψ-φ).cos^2 < (3/5:ℝ)^2 := by
    have h := mul_pos (show 0 < (ψ-φ).cos+3/5 by linarith)
      (show 0 < 3/5-(ψ-φ).cos by linarith)
    nlinarith
  have hcSqLo : (1/2:ℝ)^2 ≤ (ψ-φ).cos^2 := by
    have h := mul_nonneg (show 0 ≤ -(ψ-φ).cos-1/2 by linarith)
      (show 0 ≤ -(ψ-φ).cos+1/2 by linarith)
    nlinarith
  refine ⟨hclo,hcle,?_,?_⟩
  · by_contra hn
    have h := mul_nonneg (show 0 ≤ 4/5-|(ψ-φ).sin| by linarith)
      (show 0 ≤ 4/5+|(ψ-φ).sin| by positivity)
    nlinarith
  · by_contra hn
    have h := mul_nonneg (show 0 ≤ |(ψ-φ).sin|-7/8 by linarith)
      (show 0 ≤ |(ψ-φ).sin|+7/8 by positivity)
    nlinarith

/-- An explicit intersection point, not another separating-axis assumption. -/
lemma near_axis_square_overlap {S T : UnitSquare} {o : Point}
    (C : SquareChart S o) (D : SquareChart T o)
    (ha : 1/2 ≤ C.a ∧ C.a ≤ 11/16) (hb : C.b < 1/16)
    (ha' : 1/2 ≤ D.a ∧ D.a ≤ 11/16) (hb' : D.b < 1/16)
    (hlo : 2*Real.pi/3 ≤ dist C.phase D.phase)
    (hhi : dist C.phase D.phase < 2*Real.pi/3+1/12) :
    ∃ z, openSquare S z ∧ openSquare T z := by
  obtain ⟨hc0,hc1,hs0,hs1⟩ := near_axis_angles hlo hhi
  have hbabs : |C.signedB| < 1/16 := by rw [C.abs_signedB]; exact hb
  have hbabs' : |D.signedB| < 1/16 := by rw [D.abs_signedB]; exact hb'
  rcases abs_lt.mp hbabs with ⟨hb0,hb1⟩
  rcases abs_lt.mp hbabs' with ⟨hb0',hb1'⟩
  by_cases hs : 0 ≤ (D.phase-C.phase).sin
  · rw [abs_of_nonneg hs] at hs0 hs1
    refine ⟨pointInDirection o C.phase (1/5) (2/5),?_,?_⟩
    · apply (C.cartesian _ _).mpr
      constructor <;> apply abs_lt.mpr <;> constructor <;> linarith [ha.1,ha.2]
    · rw [pointInDirection_transition o C.phase D.phase]
      apply (D.cartesian _ _).mpr
      constructor <;> apply abs_lt.mpr <;> constructor <;> linarith [ha'.1,ha'.2]
  · rw [abs_of_neg (lt_of_not_ge hs)] at hs0 hs1
    refine ⟨pointInDirection o C.phase (1/5) (-(2/5)),?_,?_⟩
    · apply (C.cartesian _ _).mpr
      constructor <;> apply abs_lt.mpr <;> constructor <;> linarith [ha.1,ha.2]
    · rw [pointInDirection_transition o C.phase D.phase]
      apply (D.cartesian _ _).mpr
      constructor <;> apply abs_lt.mpr <;> constructor <;> linarith [ha'.1,ha'.2]

end ThreeUnitSquaresInCircle.Unified
