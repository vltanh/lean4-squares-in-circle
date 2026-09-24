import SquaresInCircles.Seven.ArcAnalysis

/-!
# The marker arc

For an admissible state, the closed square holds the arc of the unit circle of
half-width `801/1600` about its label: each of the four edge lines stays out
of the way, the far one trivially.
-/
noncomputable section
open Set
namespace SquaresInCircles.Seven

lemma axial_minus_asin_lower {u : ℝ} (hu : 0 ≤ u ∧ u ≤ 31/40) :
    Real.pi/6 ≤ axial u-Real.arcsin (u-1/2) := by
  let f : ℝ → ℝ := fun y => 5*(y+1/2)/4-Real.arcsin y
  have hmono : MonotoneOn f (Icc (-1/2 : ℝ) (1/2)) := by
    apply monoOn_of_hasDeriv_nonneg (d := fun y => 5/4-1/Real.sqrt (1-y^2))
    · fun_prop
    · intro y hy
      have ha := Real.hasDerivAt_arcsin (x := y) (by linarith [hy.1]) (by linarith [hy.2])
      have h := (((hasDerivAt_id y).add_const (1/2 : ℝ)).const_mul (5/4 : ℝ)).sub ha
      convert h using 1
      · funext z
        simp only [f,Pi.sub_apply,id]
        ring
      · ring
    · intro y hy
      have hp : 0 < 1-y^2 := by nlinarith [hy.1,hy.2]
      have hr : 0 < Real.sqrt (1-y^2) := Real.sqrt_pos.mpr hp
      have hs := Real.sq_sqrt hp.le
      have hlo : 4/5 ≤ Real.sqrt (1-y^2) := by nlinarith [hy.1,hy.2]
      have hi : 1/Real.sqrt (1-y^2) ≤ 5/4 :=
        (div_le_iff₀ hr).mpr (by nlinarith)
      linarith
  have hm := hmono
    (show (-1/2 : ℝ) ∈ Icc (-1/2 : ℝ) (1/2) by norm_num)
    (show u-1/2 ∈ Icc (-1/2 : ℝ) (1/2) by constructor <;> linarith [hu.1,hu.2])
    (by linarith [hu.1])
  have hneg : Real.arcsin (-1/2 : ℝ) = -(Real.pi/6) := by
    rw [neg_div,Real.arcsin_neg,asin_half]
  simp only [f,hneg] at hm
  dsimp [axial]
  linarith

lemma marker_lower_endpoint {a u : ℝ} (h : Admissible a u) :
    Real.arcsin (u-1/2)+801/1600 < label a u := by
  have hy : -1/2 ≤ u-1/2 ∧ u-1/2 ≤ 11/40 := by
    constructor <;> linarith [h.1,h.u_lt]
  have hasin := asin_upper_remainder hy
  have hp := Real.pi_gt_d2
  have hA := axial_minus_asin_lower ⟨h.1,h.u_lt.le⟩
  have hcs : (3/4)*(a+1/2)+(2/3)*(u+1/2) < 2171/1200 := by
    have hid : ((3/4)*(a+1/2)+(2/3)*(u+1/2))^2+
        ((2/3)*(a+1/2)-(3/4)*(u+1/2))^2 = (145/144)*phi a u := by
      dsimp [phi]; ring
    have hh := h.2.2.2
    dsimp [targetSq] at hh
    have hs := sq_nonneg ((2/3)*(a+1/2)-(3/4)*(u+1/2))
    nlinarith
  have hT : Real.arcsin (u-1/2)+801/1600 < side a u := by
    dsimp [side]
    linarith
  have hcap : Real.arcsin (u-1/2)+801/1600 < Real.pi/4 := by
    linarith [h.u_lt]
  unfold label
  exact lt_min (lt_min (by linarith) hT) hcap

lemma marker_vertical_endpoint {a u : ℝ} (h : Admissible a u) :
    label a u+801/1600 < Real.arccos (a-1/2) := by
  let x := a-1/2
  have hx : 0 ≤ x ∧ x ≤ 3/4 := by
    dsimp [x]; constructor <;> linarith [h.2.2.1,h.a_lt_five_fourths]
  have hp := (arc_radicands hx).2
  have hs := Real.sq_sqrt hp.le
  have hu : u+1/2 ≤ Real.sqrt (targetSq-(x+1)^2) := by
    have hh := h.2.2.2
    have hn := Real.sqrt_nonneg (targetSq-(x+1)^2)
    dsimp [phi,x] at hh hs hn ⊢
    nlinarith [h.1]
  have henv : side a u+Real.arcsin x ≤ arcEnvelope x := by
    dsimp [side,arcEnvelope,x] at *
    linarith
  have hb := arcEnvelope_bound hx
  have hl := h.label_le_side
  have hsqrt : Real.sqrt (87061 : ℝ) < 2951/10 := by
    have hh := Real.sq_sqrt (show (0 : ℝ) ≤ 87061 by norm_num)
    nlinarith [Real.sqrt_nonneg (87061 : ℝ)]
  have hpi := Real.pi_gt_d2
  change label a u+801/1600 < Real.arccos x
  rw [Real.arccos_eq_pi_div_two_sub_arcsin]
  linarith

/-- The tangent to arcsine at 3/5, including the nondifferentiable endpoint 1. -/
lemma asin_tangent_three_fifths {x : ℝ} (hx : 1/2 ≤ x ∧ x ≤ 1) :
    Real.arcsin (3/5 : ℝ)+(5/4)*(x-3/5) ≤ Real.arcsin x := by
  let f : ℝ → ℝ := fun y => Real.arcsin y-(5/4)*y
  have hd (y : ℝ) (hy : 1/2 < y ∧ y < 1) :
      HasDerivAt f (1/Real.sqrt (1-y^2)-5/4) y := by
    have h := (Real.hasDerivAt_arcsin (x := y)
      (by linarith [hy.1]) (by linarith [hy.2])).sub
      ((hasDerivAt_id y).const_mul (5/4 : ℝ))
    exact h.congr_deriv (by ring)
  by_cases hxc : x ≤ 3/5
  · have hm : AntitoneOn f (Icc (1/2 : ℝ) (3/5)) := by
      apply antiOn_of_hasDeriv_nonpos
      · dsimp [f]; fun_prop
      · intro y hy; exact hd y ⟨hy.1,by linarith [hy.2]⟩
      · intro y hy
        have hr : 0 < Real.sqrt (1-y^2) := Real.sqrt_pos.mpr (by nlinarith [hy.1,hy.2])
        have hs := Real.sq_sqrt (show 0 ≤ 1-y^2 by nlinarith [hy.1,hy.2])
        have hlo : 4/5 ≤ Real.sqrt (1-y^2) := by nlinarith [hy.1,hy.2]
        have hi : 1/Real.sqrt (1-y^2) ≤ 5/4 :=
          (div_le_iff₀ hr).mpr (by nlinarith)
        linarith
    have hh := hm ⟨hx.1,hxc⟩ (show (3/5 : ℝ) ∈ Icc (1/2 : ℝ) (3/5) by norm_num) hxc
    dsimp [f] at hh
    linarith
  · have hm : MonotoneOn f (Icc (3/5 : ℝ) 1) := by
      apply monoOn_of_hasDeriv_nonneg
      · dsimp [f]; fun_prop
      · intro y hy; exact hd y ⟨by linarith [hy.1],hy.2⟩
      · intro y hy
        have hr : 0 < Real.sqrt (1-y^2) := Real.sqrt_pos.mpr (by nlinarith [hy.1,hy.2])
        have hs := Real.sq_sqrt (show 0 ≤ 1-y^2 by nlinarith [hy.1,hy.2])
        have hup : Real.sqrt (1-y^2) ≤ 4/5 := by nlinarith [hy.1,hy.2]
        have hi : (5/4 : ℝ) ≤ 1/Real.sqrt (1-y^2) :=
          (le_div_iff₀ hr).mpr (by nlinarith)
        linarith
    have hh := hm (show (3/5 : ℝ) ∈ Icc (3/5 : ℝ) 1 by norm_num)
      ⟨le_of_not_ge hxc,hx.2⟩ (le_of_not_ge hxc)
    dsimp [f] at hh
    linarith

lemma marker_horizontal_endpoint {a u : ℝ} (h : Admissible a u) (hu : u ≤ 1/2) :
    label a u+801/1600 < Real.arcsin (u+1/2) := by
  have hs : Real.sin (63/100 : ℝ) < 3/5 := by
    have hb := sin_upper_five (x := 63/100) (by norm_num)
    norm_num at hb ⊢
    linarith
  have ha : (63/100 : ℝ) < Real.arcsin (3/5 : ℝ) :=
    (Real.lt_arcsin_iff_sin_lt'
      (show (63/100 : ℝ) ∈ Ico (-(Real.pi/2)) (Real.pi/2) by
        constructor <;> linarith [Real.two_le_pi])).mpr hs
  have ht := asin_tangent_three_fifths
    (x := u+1/2) (by constructor <;> linarith [h.1])
  have hl := h.label_le_axial
  dsimp [axial] at hl
  linarith

/-- The marker arc: chart angles within `801/1600` of the label stay in the
closed square. -/
theorem marker_arc {a u t : ℝ} (h : Admissible a u)
    (ht : |t-label a u| ≤ 801/1600) :
    |Real.cos t-a| ≤ 1/2 ∧ |Real.sin t-u| ≤ 1/2 := by
  have hl := marker_lower_endpoint h
  have hv := marker_vertical_endpoint h
  have hP := h.label_nonneg
  rcases abs_le.mp ht with ⟨ht0,ht1⟩
  have hcos0 : -Real.arccos (a-1/2) < t := by linarith
  have hcos1 : t < Real.arccos (a-1/2) := by linarith
  have ha0 : 0 ≤ a-1/2 := by linarith [h.2.2.1]
  have ha1 : a-1/2 ≤ 1 := by linarith [h.a_lt_five_fourths]
  have hcos : a-1/2 < Real.cos t := by
    have hh := Real.cos_lt_cos_of_nonneg_of_le_pi (abs_nonneg t)
      (Real.arccos_le_pi (a-1/2)) (abs_lt.mpr ⟨hcos0,hcos1⟩)
    rw [Real.cos_arccos (by linarith) ha1,Real.cos_abs] at hh
    exact hh
  have htdom : t ∈ Ioo (-(Real.pi/2)) (Real.pi/2) := by
    have hA : Real.arccos (a-1/2) ≤ Real.pi/2 := Real.arccos_le_pi_div_two.mpr ha0
    constructor <;> linarith
  have hsin0 : u-1/2 < Real.sin t :=
    (Real.arcsin_lt_iff_lt_sin' ⟨htdom.1,htdom.2.le⟩).mp (by linarith)
  have hsin1 : Real.sin t ≤ u+1/2 := by
    by_cases hu : u ≤ 1/2
    · have hh := marker_horizontal_endpoint h hu
      have hs : Real.sin t < u+1/2 :=
        (Real.lt_arcsin_iff_sin_lt' ⟨htdom.1.le,htdom.2⟩).mp (by linarith)
      exact hs.le
    · linarith [Real.sin_le_one t]
  exact ⟨abs_le.mpr ⟨by linarith,by linarith [Real.cos_le_one t,h.2.2.1]⟩,
    abs_le.mpr ⟨by linarith,by linarith⟩⟩

end SquaresInCircles.Seven
