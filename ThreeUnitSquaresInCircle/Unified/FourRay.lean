import ThreeUnitSquaresInCircle.Unified.FourScalar

/-! An origin-containing square swept along its center ray contains a
quarter-circle on every auxiliary circle with `0 < r < 1/sqrt(2)`.
The proof below uses strict half-planes and constructs the ray parameter. -/
noncomputable section
open Set
namespace ThreeUnitSquaresInCircle.Unified

lemma ray_parameter {a b X Y : ℝ} (ha : 0 < a) (hb : 0 ≤ b)
    (hX : a-1/2 < X) (hY : b-1/2 < Y)
    (hstrip : |b*X-a*Y| < (a+b)/2) :
    ∃ m : ℝ, 0 ≤ m ∧ |X-(1+m)*a| < 1/2 ∧ |Y-(1+m)*b| < 1/2 := by
  rcases eq_or_lt_of_le hb with hzero | hbpos
  · subst b
    have hYs : |Y| < 1/2 := by
      rw [zero_mul,zero_sub,abs_neg,abs_mul,abs_of_pos ha] at hstrip
      nlinarith
    by_cases hx : X ≤ a
    · exact ⟨0,le_rfl,abs_lt.mpr ⟨by nlinarith,by nlinarith⟩,by simpa using hYs⟩
    · refine ⟨X/a-1,?_,?_,by simpa using hYs⟩
      · have hh := (lt_div_iff₀ ha).mpr (show 1*a < X by linarith)
        linarith
      · have he : X-(1+(X/a-1))*a=0 := by field_simp; ring
        rw [he]; norm_num
  · rcases abs_lt.mp hstrip with ⟨hs0,hs1⟩
    let L := max 1 (max ((X-1/2)/a) ((Y-1/2)/b))
    let U := min ((X+1/2)/a) ((Y+1/2)/b)
    have h1X : 1 < (X+1/2)/a := (lt_div_iff₀ ha).mpr (by linarith)
    have h1Y : 1 < (Y+1/2)/b := (lt_div_iff₀ hbpos).mpr (by linarith)
    have hXX : (X-1/2)/a < (X+1/2)/a := (div_lt_div_iff_of_pos_right ha).mpr (by linarith)
    have hYY : (Y-1/2)/b < (Y+1/2)/b := (div_lt_div_iff_of_pos_right hbpos).mpr (by linarith)
    have hXY : (X-1/2)/a < (Y+1/2)/b :=
      (div_lt_div_iff₀ ha hbpos).mpr (by nlinarith)
    have hYX : (Y-1/2)/b < (X+1/2)/a :=
      (div_lt_div_iff₀ hbpos ha).mpr (by nlinarith)
    have hLU : L < U := by
      dsimp [L,U]
      exact max_lt (lt_min h1X h1Y) (max_lt (lt_min hXX hXY) (lt_min hYX hYY))
    obtain ⟨z,hzL,hzU⟩ := exists_between hLU
    have hz1 : 1 < z := (le_max_left _ _).trans_lt hzL
    have hzX : (X-1/2)/a < z := (le_trans (le_max_left _ _) (le_max_right _ _)).trans_lt hzL
    have hzY : (Y-1/2)/b < z := (le_trans (le_max_right _ _) (le_max_right _ _)).trans_lt hzL
    have hzX' : z < (X+1/2)/a := lt_of_lt_of_le hzU (min_le_left _ _)
    have hzY' : z < (Y+1/2)/b := lt_of_lt_of_le hzU (min_le_right _ _)
    have hx0 := (div_lt_iff₀ ha).mp hzX
    have hy0 := (div_lt_iff₀ hbpos).mp hzY
    have hx1 := (lt_div_iff₀ ha).mp hzX'
    have hy1 := (lt_div_iff₀ hbpos).mp hzY'
    exact ⟨z-1,by linarith,abs_lt.mpr ⟨by nlinarith,by nlinarith⟩,
      abs_lt.mpr ⟨by nlinarith,by nlinarith⟩⟩

lemma first_octant_direction {a b : ℝ} (ha : 0 < a) (hb : 0 ≤ b) (hba : b ≤ a) :
    ∃ l δ : ℝ, 0 < l ∧ a ≤ l ∧ l ≤ a+b ∧
      0 ≤ δ ∧ δ ≤ Real.pi/4 ∧ l*Real.cos δ=a ∧ l*Real.sin δ=b := by
  let l := Real.sqrt (a^2+b^2)
  have hl : 0 < l := Real.sqrt_pos.mpr (by nlinarith [sq_nonneg b])
  have hl2 : l^2=a^2+b^2 := Real.sq_sqrt (by positivity)
  have hal : a ≤ l := by nlinarith [sq_nonneg b]
  have hlab : l ≤ a+b := by nlinarith [mul_nonneg ha.le hb]
  let δ := Real.arccos (a/l)
  have ha0 : 0 < a/l := div_pos ha hl
  have ha1 : a/l ≤ 1 := (div_le_one hl).mpr hal
  have hc : Real.cos δ=a/l := Real.cos_arccos (by linarith) ha1
  have hδ0 : 0 ≤ δ := Real.arccos_nonneg _
  have hδ1 : δ < Real.pi/2 := by
    have hh := Real.arcsin_pos.mpr ha0
    dsimp [δ,Real.arccos]; linarith
  have hsin0 : 0 ≤ Real.sin δ := Real.sin_nonneg_of_nonneg_of_le_pi hδ0 (by linarith [Real.pi_pos])
  have hcos : l*Real.cos δ=a := by rw [hc]; field_simp
  have hu := congrArg (fun x : ℝ => l^2*x) (Real.sin_sq_add_cos_sq δ)
  have hc2 := congrArg (fun x : ℝ => x^2) hcos
  have hsin : l*Real.sin δ=b := by
    have hnn := mul_nonneg hl.le hsin0
    nlinarith
  have hδ4 : δ ≤ Real.pi/4 := by
    by_contra hn
    have hlt := Real.strictMonoOn_sin
      (show Real.pi/2-δ ∈ Icc (-(Real.pi/2)) (Real.pi/2) by constructor <;> linarith [Real.pi_pos])
      (show δ ∈ Icc (-(Real.pi/2)) (Real.pi/2) by constructor <;> linarith [Real.pi_pos])
      (show Real.pi/2-δ < δ by linarith)
    rw [Real.sin_pi_div_two_sub] at hlt
    have hh := mul_lt_mul_of_pos_left hlt hl
    rw [hcos,hsin] at hh
    linarith
  exact ⟨l,δ,hl,hal,hlab,hδ0,hδ4,hcos,hsin⟩

lemma canonical_quarter_ray {a b r : ℝ} (ha : 0 < a) (hb : 0 ≤ b)
    (hba : b ≤ a) (ha1 : a < 1/2) (hr : 0 < r) (hr1 : r < halfDiagonal) :
    ∃ δ : ℝ, ∀ t ∈ Ioo (δ-Real.pi/4) (δ+Real.pi/4),
      ∃ m : ℝ, 0 ≤ m ∧ |r*Real.cos t-(1+m)*a| < 1/2 ∧
        |r*Real.sin t-(1+m)*b| < 1/2 := by
  obtain ⟨l,δ,hl,hal,hlab,hδ0,hδ1,hcos,hsin⟩ := first_octant_direction ha hb hba
  have hd := halfDiagonal_pos
  have hrd : r*halfDiagonal < 1/2 := by
    have hh := mul_lt_mul_of_pos_right hr1 hd
    nlinarith [halfDiagonal_sq]
  refine ⟨δ,?_⟩
  intro t ht
  have htDom : t ∈ Ioo (-(Real.pi/2)) (Real.pi/2) := by
    constructor <;> linarith [ht.1,ht.2,Real.pi_pos]
  have hX : a-1/2 < r*Real.cos t := by
    have hc := Real.cos_pos_of_mem_Ioo htDom
    have hh := mul_pos hr hc
    linarith
  have hmin := Real.strictMonoOn_sin
    (show δ-Real.pi/4 ∈ Icc (-(Real.pi/2)) (Real.pi/2) by constructor <;> linarith [Real.pi_pos])
    ⟨htDom.1.le,htDom.2.le⟩ ht.1
  have hid : l*Real.sin (δ-Real.pi/4)=(b-a)*halfDiagonal := by
    rw [Real.sin_sub,Real.cos_pi_div_four,Real.sin_pi_div_four]
    dsimp [halfDiagonal]
    calc
      _ = (l*Real.sin δ-l*Real.cos δ)*(Real.sqrt 2/2) := by ring
      _ = _ := by rw [hsin,hcos]
  have hY : b-1/2 < r*Real.sin t := by
    -- Multiply in two stages, retaining positive factors explicitly.
    have hmin' := mul_lt_mul_of_pos_left hmin hl
    rw [hid] at hmin'
    have hmin'' := mul_lt_mul_of_pos_left hmin' hr
    have h₁ := mul_nonneg (show 0 ≤ 1/2-r*halfDiagonal by linarith) (sub_nonneg.mpr hba)
    have h₂ := mul_nonneg (sub_nonneg.mpr hal) (show 0 ≤ 1/2-b by linarith)
    have h₃ := mul_nonneg hb (show 0 ≤ 1/2-a by linarith)
    by_contra hn
    have h₄ := mul_nonneg hl.le (sub_nonneg.mpr (le_of_not_gt hn))
    nlinarith
  have hs0 := Real.strictMonoOn_sin
    (show -(Real.pi/4) ∈ Icc (-(Real.pi/2)) (Real.pi/2) by constructor <;> linarith [Real.pi_pos])
    (show t-δ ∈ Icc (-(Real.pi/2)) (Real.pi/2) by constructor <;> linarith [ht.1,ht.2,Real.pi_pos])
    (show -(Real.pi/4) < t-δ by linarith [ht.1])
  have hs1 := Real.strictMonoOn_sin
    (show t-δ ∈ Icc (-(Real.pi/2)) (Real.pi/2) by constructor <;> linarith [ht.1,ht.2,Real.pi_pos])
    (show Real.pi/4 ∈ Icc (-(Real.pi/2)) (Real.pi/2) by constructor <;> linarith [Real.pi_pos])
    (show t-δ < Real.pi/4 by linarith [ht.2])
  rw [Real.sin_neg,Real.sin_pi_div_four] at hs0
  rw [Real.sin_pi_div_four] at hs1
  have habs : |Real.sin (t-δ)| < halfDiagonal := abs_lt.mpr ⟨hs0,hs1⟩
  have he : b*(r*Real.cos t)-a*(r*Real.sin t) = -r*l*Real.sin (t-δ) := by
    rw [← hcos,← hsin,Real.sin_sub]
    ring
  have hstrip : |b*(r*Real.cos t)-a*(r*Real.sin t)| < (a+b)/2 := by
    rw [he,abs_mul,abs_mul,abs_neg,abs_of_pos hr,abs_of_pos hl]
    have h₁ := mul_lt_mul_of_pos_left habs (mul_pos hr hl)
    have h₂ := mul_lt_mul_of_pos_right hrd hl
    nlinarith
  exact ray_parameter ha hb hX hY hstrip

/-- A quarter-circle is available from the containing square's radial sweep. -/
theorem four_containing_arc {S : UnitSquare} {o : Point} (C : SquareChart S o)
    {r : ℝ} (hsort : C.b ≤ C.a) (ho : openSquare S o)
    (hpos : 0 < C.a+C.b) (hr : 0 < r) (hr1 : r < halfDiagonal) :
    ∃ A : OpenArc o r (openRay S o), A.halfWidth=Real.pi/4 := by
  have hinside := C.origin.mp ho
  have ha : 0 < C.a := by linarith [C.nonneg.2]
  obtain ⟨δ,hδ⟩ := canonical_quarter_ray ha C.nonneg.2 hsort hinside.1 hr hr1
  obtain ⟨A,hA⟩ := arcFromChartInterval o r (openRay S o) C.phase C.reversed
    (δ-Real.pi/4) (δ+Real.pi/4)
    (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])
    (fun t ht => C.ray_mem (hδ t ht))
  exact ⟨A,by rw [hA]; ring⟩

end ThreeUnitSquaresInCircle.Unified
