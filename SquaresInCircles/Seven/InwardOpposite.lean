import SquaresInCircles.Seven.InwardBoundaryMinima
import SquaresInCircles.Seven.InwardAxialAxial
import SquaresInCircles.Seven.CapReduction

/-!
# The inward axis with opposite signs

Axial sources move monotonically to the axial/side transition, and a side
target moves along its label segment to the axial tie. A nonpositive turn keeps
the remainder of the side source, so the only zero is a side source with an
axial target.
-/
noncomputable section
namespace SquaresInCircles.Seven
open Boundary

lemma inward_opposite_side_positive_turn {a u A v : ℝ}
    (h : Admissible a u) (h' : Admissible A v)
    (hT : label a u=side a u) (hA : label A v=axial v)
    (hz : 0<label a u+label A v-Real.pi/6) :
    0<pairSupport a u A v .positive .negative 2 gap := by
  let z := label a u+label A v-Real.pi/6
  have hzu : z≤Real.pi/3 := by dsimp [z]; linarith [h.label_le_quarter,h'.label_le_quarter]
  have ht : s0≤label a u ∧ label a u≤Real.pi/4 :=
    ⟨(side_state_transition_bounds h hT).2.2,h.label_le_quarter⟩
  have hsEq : otherLabel z (label a u)=label A v := by dsimp [otherLabel,z]; ring
  have hvEq : otherV z (label a u)=v := by
    rw [otherV,hsEq,hA]
    dsimp [axial]; ring
  have hp := opposite_upper_pos ⟨hz,hzu⟩ ht
    ⟨by rw [hsEq]; exact h'.label_nonneg,by rw [hsEq]; exact h'.label_le_quarter⟩
  have ha := side_radial_upper h hT
  have hb := axial_upper h' hA
  have hs0 := Real.sin_nonneg_of_nonneg_of_le_pi (x := z) hz.le (by linarith [hzu,Real.pi_pos])
  have hm := mul_nonneg (sub_nonneg.mpr hb) hs0
  rw [inward_opposite_formula h h']
  change 0 < inwardOpposite a A v z
  dsimp [oppositeUpper] at hp
  rw [hvEq] at hp
  dsimp [inwardOpposite] at *
  linarith

/-- The inward axis with opposite signs, side source and axial target. A
nonpositive turn keeps the remainder of the side source, so zero support
forces the side state and `v = 0`. -/
theorem inward_opposite_side_axial_property {a u A v : ℝ}
    (h : Admissible a u) (h' : Admissible A v)
    (hT : label a u=side a u) (hA : label A v=axial v) :
    PairProperty a u A v .positive .negative 2 := by
  by_cases hz : 0<label a u+label A v-Real.pi/6
  · exact .of_pos (inward_opposite_side_positive_turn h h' hT hA hz)
  have hl := inward_opposite_negative_turn h h' hT hA (le_of_not_gt hz)
  have hW := h.remainder_nonneg
  have he := abs_nonneg (label a u+label A v-Real.pi/6)
  refine ⟨by linarith,fun hzero => ?_⟩
  have hc := Equality.remainder_zero h (by linarith)
  have he0 : label a u+label A v-Real.pi/6=0 := abs_eq_zero.mp (by linarith)
  rw [hc.1,hc.2,Equality.side_label,hA] at he0
  dsimp [axial] at he0
  exact Or.inr (Or.inl ⟨rfl,hc,Equality.axial_of_transverse_zero h' (by linarith)⟩)

lemma inward_opposite_axial_positive_turn {a u A v : ℝ}
    (h : Admissible a u) (h' : Admissible A v)
    (hA : label a u=axial u) (hB : label A v=axial v)
    (hz : 0<label a u+label A v-Real.pi/6) :
    0<pairSupport a u A v .positive .negative 2 gap := by
  let z := label a u+label A v-Real.pi/6
  let t := label a u
  have ht : 0≤t ∧ t≤Real.pi/4 := ⟨h.label_nonneg,h.label_le_quarter⟩
  have hu : u=(4/5)*t := by dsimp [t]; rw [hA]; dsimp [axial]; ring
  have huDom : 0≤u ∧ u≤Real.pi/5 := by rw [hu]; constructor <;> linarith [ht.1,ht.2]
  have hvDom : 0≤v ∧ v≤Real.pi/5 := by
    have hh := h'.label_le_quarter
    rw [hB] at hh
    dsimp [axial] at hh
    exact ⟨h'.1,by linarith⟩
  have hzu : z≤Real.pi/3 := by dsimp [z]; linarith [h.label_le_quarter,h'.label_le_quarter]
  have hs0 := Real.sin_nonneg_of_nonneg_of_le_pi (x := z) hz.le (by linarith [hzu,Real.pi_pos])
  rw [inward_opposite_formula h h']
  change 0 < inwardOpposite a A v z
  by_cases ht0 : s0≤t
  · have hu0 : u0≤u := by rw [hu]; dsimp [s0] at ht0; linarith
    have hur : u≤rd := by linarith [huDom.2,pi_lt_22_over_7,rd_bounds.1]
    have haup := axial_upper h hA
    rw [axialTop_right ⟨hu0,hur⟩] at haup
    have he : axialLine u=tieA t := by rw [hu]; dsimp [axialLine,tieA]; ring
    rw [he] at haup
    obtain ⟨ha,hat,haT⟩ := tie_state ⟨ht0,ht.2⟩
    have hside : label (tieA t) ((4/5)*t)=side (tieA t) ((4/5)*t) := hat.trans haT.symm
    have hp := inward_opposite_side_positive_turn ha h' hside hB
      (by rw [hat]; exact hz)
    rw [inward_opposite_formula ha h',hat] at hp
    change 0 < inwardOpposite (tieA t) A v z at hp
    dsimp [inwardOpposite] at *
    linarith
  · have htu : t ≤ s0 := (lt_of_not_ge ht0).le
    have huu : u≤u0 := by rw [hu]; dsimp [s0] at htu; linarith
    let vp := (4/5)*z+2*Real.pi/15-u0
    have hvEq : v=(4/5)*z+2*Real.pi/15-u := by
      dsimp [z]
      rw [hA,hB]
      dsimp [axial]; ring
    have hvp : 0≤vp ∧ vp≤v := by
      dsimp [vp]
      constructor
      · linarith [show 0<z from hz,transition_coarse.2.2.2.1,pi_lower_157]
      · rw [hvEq]; linarith
    have hvpDom : 0≤vp ∧ vp≤Real.pi/5 := ⟨hvp.1,hvp.2.trans hvDom.2⟩
    obtain ⟨hb,hbA⟩ := axialTop_state hvpDom
    have haT : label a0 u0=side a0 u0 := transition_labels.2
    have hzero : label a0 u0=s0 := by rw [transition_labels.1]; dsimp [s0,axial]; ring
    have he : label a0 u0+label (axialTop vp) vp-Real.pi/6=z := by
      rw [hzero,hbA]
      dsimp [axial,vp,s0]; ring
    have hp := inward_opposite_side_positive_turn transition_admissible hb haT hbA
      (by rw [he]; exact hz)
    rw [inward_opposite_formula transition_admissible hb,he] at hp
    have haup := a_le_circle h
    have hdisp := circle_displacement_half h.1 huu le_rfl
    rw [circle_u0] at hdisp
    have hbup := axial_upper h' hB
    have hmon := axialTop_antitone hvp.1 hvp.2 hvDom.2
    have htarget : A≤axialTop vp := hbup.trans hmon
    have htargetMul := mul_nonneg (sub_nonneg.mpr htarget) hs0
    have hmul := mul_nonneg (sub_nonneg.mpr huu)
      (sub_nonneg.mpr (cos_ge_half ⟨hz.le,hzu⟩))
    rw [show v=vp+(u0-u) by rw [hvEq]; dsimp [vp]; ring]
    dsimp [inwardOpposite] at hp ⊢
    linarith

lemma inward_opposite_axial_axial_pos {a u A v : ℝ}
    (h : Admissible a u) (h' : Admissible A v)
    (hA : label a u=axial u) (hB : label A v=axial v) :
    0<pairSupport a u A v .positive .negative 2 gap := by
  by_cases he : label a u+label A v-Real.pi/6≤0
  · exact inward_axial_nonpositive_turn .negative h h' hA hB
      (by simp only [TransverseSign.coe]; linarith)
  · exact inward_opposite_axial_positive_turn h h' hA hB (lt_of_not_ge he)

lemma inward_opposite_side_target_reduction {a u A v : ℝ}
    (h : Admissible a u) (h' : Admissible A v)
    (hT : label A v=side A v) :
    pairSupport a u (tieA (label A v)) ((4/5)*label A v)
      .positive .negative 2 gap ≤
      pairSupport a u A v .positive .negative 2 gap := by
  let s := label A v
  let z := label a u+s-Real.pi/6
  have hs : s0 ≤ s ∧ s≤Real.pi/4 :=
    ⟨(side_state_transition_bounds h' hT).2.2,h'.label_le_quarter⟩
  obtain ⟨hb,hlabel,hside⟩ := tie_state hs
  have hz : -1/6<z ∧ z≤Real.pi/3 := by
    have ht0 := h.label_nonneg
    have ht1 := h.label_le_quarter
    have hs0 := side_selected_label_gt h' hT
    dsimp [z,s]
    constructor <;> linarith [h'.label_le_quarter,pi_lt_22_over_7]
  have hcoef : 0<Real.cos z-(4/9)*Real.sin z := by
    by_cases hz0 : 0≤z
    · linarith [cos_ge_half ⟨hz0,hz.2⟩,Real.sin_le_one z]
    · have hS : Real.sin z≤0 := by
        have hh := Real.sin_nonneg_of_nonneg_of_le_pi
          (show 0≤-z by linarith) (by linarith [hz.1,pi_lower_157])
        rw [Real.sin_neg] at hh
        linarith
      have hC : 0<Real.cos z := Real.cos_pos_of_mem_Ioo
        ⟨by linarith [hz.1,pi_lower_157],by linarith [hz0,Real.pi_pos]⟩
      linarith
  have hseg := side_segment h' hT
  have he : A=tieA s+(4/9)*(v-(4/5)*s) := hseg.2.2
  have hmul := mul_nonneg (show 0≤v-(4/5)*s by linarith [hseg.1]) hcoef.le
  rw [inward_opposite_formula h hb,inward_opposite_formula h h',hlabel]
  change inwardOpposite a (tieA s) ((4/5)*s) z ≤ inwardOpposite a A v z
  rw [he]
  dsimp [inwardOpposite]
  linarith

/-- The inward axis with signs `(+,-)`, all active labels. A side target
reduces to the axial tie of its label, which is no contact. -/
theorem fixed_gap_inward_opposite_active {a u A v : ℝ}
    (h : Admissible a u) (h' : Admissible A v)
    (ha : ActiveLabel a u) (hb : ActiveLabel A v) :
    PairProperty a u A v .positive .negative 2 := by
  have axialTarget (B w : ℝ) (hB : Admissible B w)
      (hBA : label B w=axial w) : PairProperty a u B w .positive .negative 2 := by
    rcases ha with hA | hT
    · exact .of_pos (inward_opposite_axial_axial_pos h hB hA hBA)
    · exact inward_opposite_side_axial_property h hB hT hBA
  rcases hb with hA | hT
  · exact axialTarget A v h' hA
  have hs : s0 ≤ label A v ∧ label A v≤Real.pi/4 :=
    ⟨(side_state_transition_bounds h' hT).2.2,h'.label_le_quarter⟩
  obtain ⟨hB,hlabel,-⟩ := tie_state hs
  have hBA : label (tieA (label A v)) ((4/5)*label A v)=axial ((4/5)*label A v) := by
    rw [hlabel]; dsimp [axial]; ring
  have hp := axialTarget _ _ hB hBA
  have hcomp := inward_opposite_side_target_reduction h h' hT
  refine ⟨hp.1.trans hcomp,fun hz => ?_⟩
  rcases hp.2 (le_antisymm (hcomp.trans hz.le) hp.1) with ⟨hsign,-⟩ | ⟨-,-,hv,-⟩ | ⟨-,-,hc⟩
  · cases hsign
  · linarith [side_selected_label_gt h' hT]
  · rw [hc.1,hc.2,Equality.side_label] at hBA
    dsimp [axial] at hBA
    linarith [pi_lt_22_over_7]

end SquaresInCircles.Seven
