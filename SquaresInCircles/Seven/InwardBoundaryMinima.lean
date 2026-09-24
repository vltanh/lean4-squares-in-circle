import SquaresInCircles.Seven.InwardCircularCertificate
import SquaresInCircles.Seven.TargetBoundaryMonotonicity
import SquaresInCircles.Seven.CapReduction

/-!
# Finite boundary reduction of the positive inward-opposite turn

A diagonal source is moved to its junction or a capped axial endpoint.
A circular source with a straight axial target is moved to one of its two
junctions. The two circular pieces use the quadratic certificate, and the
remaining diagonal junction uses one fixed positive value plus monotonicity.
-/
noncomputable section
open Set
namespace SquaresInCircles.Seven
namespace Boundary

def otherLabel (z t : ℝ) : ℝ := z+Real.pi/6-t
def otherV (z t : ℝ) : ℝ := (4/5)*otherLabel z t
def oppositeUpper (z t : ℝ) : ℝ :=
  inwardOpposite (sideTopA t) (axialTop (otherV z t)) (otherV z t) z

def diagonalJunction (z : ℝ) : ℝ :=
  inwardOpposite rd (tieA (otherLabel z td)) (otherV z td) z

lemma sideTopA_diagonal {t : ℝ} (ht : td ≤ t) : sideTopA t=diagonal t := by
  by_cases he : t=td
  · subst t
    simp only [sideTopA,ite_eq_left le_rfl]
    rw [side_at_diagonal.1]
    dsimp [diagonal,td]
    ring
  · simp only [sideTopA,ite_eq_right (show ¬t≤td from fun h => he (le_antisymm h ht))]

lemma sideTopA_td : sideTopA td=rd := by
  simp only [sideTopA,ite_eq_left le_rfl]
  exact side_at_diagonal.1

lemma opposite_upper_circular {z t : ℝ}
    (hz : 0 < z) (ht : s0 ≤ t ∧ t ≤ td)
    (hs : 0 ≤ otherLabel z t ∧ otherLabel z t ≤ s0) :
    0 < oppositeUpper z t := by
  have htt : s0 ≤ t ∧ t ≤ Real.pi/4 := ⟨ht.1,ht.2.trans td_bounds.2.le⟩
  have hs' : 0 ≤ otherV z t ∧ otherV z t ≤ Real.pi/5 := by
    dsimp [otherV]
    constructor <;> linarith [hs.1,hs.2,transition_coarse.2.2.2.2.2,pi_lower_157]
  obtain ⟨ha,halabel⟩ := sideTop_state htt
  have hT := target_at_upper_side t htt
  obtain ⟨hb,hB⟩ := axialTop_state hs'
  have hv : otherV z t ≤ 3/10 := by
    dsimp [otherV]
    have hu := transition_coarse.2.2.2.1
    dsimp [s0] at hs
    linarith
  have hzz : z ≤ diagonalAngle := by
    dsimp [otherLabel] at hs
    dsimp [diagonalAngle]
    linarith [ht.2]
  have hz' : z ≤ 5/8 := hzz.trans diagonal_angle_bounds.2.1.le
  apply inward_circular_pos ha hb hT hB
    (show z=label (sideTopA t) (sideTopU t)+label (axialTop (otherV z t)) (otherV z t)-Real.pi/6 by
      rw [halabel,hB]
      dsimp [axial,otherV,otherLabel]
      ring) ⟨hz,hz'⟩ hv

lemma opposite_upper_cap {z t : ℝ}
    (hz : 0 < z ∧ z ≤ Real.pi/3) (ht : td ≤ t ∧ t ≤ Real.pi/4)
    (hs : otherLabel z t=Real.pi/4) : 0 < oppositeUpper z t := by
  have hv : otherV z t=Real.pi/5 := by rw [otherV,hs]; ring
  have hu0 : u0 ≤ Real.pi/5 := by linarith [transition_coarse.2.2.2.1,pi_lower_157]
  have hur : Real.pi/5 ≤ rd := by linarith [rd_bounds.1,pi_upper_22]
  have hA : axialTop (Real.pi/5) < 3/4 := by
    rw [axialTop_right ⟨hu0,hur⟩]
    dsimp [axialLine]
    linarith [pi_lower_157]
  have ha : sideTopA t < 31/40 := by
    rw [sideTopA_diagonal ht.1]
    have hd : diagonal td=rd := by dsimp [diagonal,td]; ring
    have hh : diagonal t≤diagonal td := by dsimp [diagonal]; linarith [ht.1]
    rw [hd] at hh
    linarith [rd_bounds.2]
  have hC : 1/2 ≤ Real.cos z := by
    have hh := Real.strictAntiOn_cos.antitoneOn
      (show z∈Icc 0 Real.pi by constructor <;> linarith [hz.1,hz.2,Real.pi_pos])
      (show Real.pi/3∈Icc 0 Real.pi by constructor <;> linarith [Real.pi_pos]) hz.2
    simpa only [Real.cos_pi_div_three] using hh
  have hS0 := Real.sin_nonneg_of_nonneg_of_le_pi hz.1.le (by linarith [hz.2,Real.pi_pos])
  have hb := (axialTop_state ⟨by positivity,le_rfl⟩).1
  have hm := mul_nonneg (show 0≤3/4-axialTop (Real.pi/5) by linarith) hS0
  have hc := mul_le_mul_of_nonneg_left hC (show 0≤Real.pi/5+1/2 by positivity)
  dsimp [oppositeUpper,inwardOpposite]
  rw [hv,abs_of_nonneg hS0]
  nlinarith [Real.sin_le_one z,pi_lower_157]

lemma diagonal_junction_pos {z : ℝ}
    (hz : 0 < z ∧ z ≤ Real.pi/3)
    (hs : s0 ≤ otherLabel z td ∧ otherLabel z td ≤ Real.pi/4) :
    0 < diagonalJunction z := by
  have hstart : diagonalAngle ≤ z := by
    dsimp [otherLabel] at hs
    dsimp [diagonalAngle]
    linarith [hs.1]
  have hmono : MonotoneOn diagonalJunction (Icc diagonalAngle z) := by
    apply monoOn_of_hasDeriv_nonneg (d := fun x => (43/90-(4/5)*otherLabel x td)*Real.sin x+
      (13/10-tieA (otherLabel x td))*Real.cos x)
    · unfold diagonalJunction inwardOpposite tieA otherV otherLabel; fun_prop
    · intro x hx
      have hx0 : 0 < x := lt_of_lt_of_le diagonal_angle_bounds.1 hx.1.le
      have hxpi : x < Real.pi := by linarith [hx.2,hz.2,Real.pi_pos]
      have hsin : 0 < Real.sin x := Real.sin_pos_of_pos_of_lt_pi hx0 hxpi
      have hloc : inwardOpposite rd (tieA (otherLabel x td)) (otherV x td) x =
          1/2-rd-(tieA (otherLabel x td)-1/2)*Real.sin x+
          (otherV x td+1/2)*Real.cos x := by
        dsimp [inwardOpposite]
        rw [abs_of_nonneg hsin.le]
        ring
      have hevent : (fun y => diagonalJunction y) =ᶠ[nhds x]
          (fun y => 1/2-rd-(tieA (otherLabel y td)-1/2)*Real.sin y+
          (otherV y td+1/2)*Real.cos y) := by
        filter_upwards [((Real.continuous_sin.tendsto x).eventually (lt_mem_nhds hsin))] with y hy
        dsimp [diagonalJunction,inwardOpposite]
        rw [abs_of_pos hy]
        ring
      have ha : HasDerivAt (fun y => tieA (otherLabel y td)) (-(44/45)) x := by
        exact ((hasDerivAt_const x ((2*Real.pi+7)/9)).fun_sub
          ((((hasDerivAt_id' x).add_const (Real.pi/6)).sub_const td).const_mul (44/45))).congr_deriv
          (by ring)
      have hv : HasDerivAt (fun y => otherV y td) (4/5) x := by
        exact ((((hasDerivAt_id' x).add_const (Real.pi/6)).sub_const td).const_mul (4/5)).congr_deriv
          (by ring)
      have hd := (((hasDerivAt_const x (1/2-rd)).fun_sub
        ((ha.sub_const (1/2)).fun_mul (Real.hasDerivAt_sin x))).fun_add
        ((hv.add_const (1/2)).fun_mul (Real.hasDerivAt_cos x)))
      have hd' : HasDerivAt
          (fun y => 1/2-rd-(tieA (otherLabel y td)-1/2)*Real.sin y+
          (otherV y td+1/2)*Real.cos y)
          ((43/90-(4/5)*otherLabel x td)*Real.sin x+
          (13/10-tieA (otherLabel x td))*Real.cos x) x := by
        exact hd.congr_deriv (by dsimp [otherV]; ring)
      exact hd'.congr_of_eventuallyEq hevent
    · intro x hx
      let s := otherLabel x td
      have hsx : s0 ≤ s ∧ s ≤ Real.pi/4 := by
        dsimp [s,otherLabel,diagonalAngle] at *
        constructor <;> linarith [hs.1,hs.2,hx.1,hx.2]
      have ht := transition_coarse
      have hC : 1/2 ≤ Real.cos x := by
        have hh := Real.strictAntiOn_cos.antitoneOn
          (show x∈Icc 0 Real.pi by constructor <;> linarith [hx.1,diagonal_angle_bounds.1,hx.2,hz.2,Real.pi_pos])
          (show Real.pi/3∈Icc 0 Real.pi by constructor <;> linarith [Real.pi_pos]) (by linarith [hx.2,hz.2])
        simpa only [Real.cos_pi_div_three] using hh
      have hS0 := Real.sin_nonneg_of_nonneg_of_le_pi (x := x)
        (by linarith [hx.1,diagonal_angle_bounds.1]) (by linarith [hx.2,hz.2,Real.pi_pos])
      have hSC : Real.sin x≤(9/4)*Real.cos x := by linarith [Real.sin_le_one x]
      have ha : tieA s<9/8 := by
        have hbase : tieA s0=a0 := by dsimp [tieA,s0]; linarith [transition_line]
        have hm : tieA s≤tieA s0 := by dsimp [tieA]; linarith [hsx.1]
        rw [hbase] at hm
        linarith
      by_cases hc : 0≤43/90-(4/5)*s
      · have hp := mul_nonneg hc hS0
        have hp' := mul_nonneg (show 0≤13/10-tieA s by linarith) (by linarith : 0≤Real.cos x)
        linarith
      · have hp := mul_nonneg (show 0≤-(43/90-(4/5)*s) by linarith) (sub_nonneg.mpr hSC)
        have hm : 0<(13/10-tieA s)+(9/4)*(43/90-(4/5)*s) := by
          dsimp [tieA]
          linarith [hsx.2,pi_upper_22]
        have hm' := mul_nonneg hm.le (show 0≤Real.cos x by linarith)
        nlinarith
  have he : diagonalJunction diagonalAngle=diagonalValue := by
    have hs' : otherLabel diagonalAngle td=s0 := by dsimp [otherLabel,diagonalAngle]; ring
    have ha : tieA s0=a0 := by dsimp [tieA,s0]; linarith [transition_line]
    have hv : otherV diagonalAngle td=u0 := by rw [otherV,hs']; dsimp [s0]; ring
    have hsin := Real.sin_nonneg_of_nonneg_of_le_pi diagonal_angle_bounds.1.le
      (by linarith [diagonal_angle_bounds.2.1,pi_lower_157])
    dsimp [diagonalJunction,inwardOpposite]
    rw [hs',ha,hv,abs_of_nonneg hsin]
    dsimp [diagonalValue,u0]
    ring
  have hbase : 0<diagonalJunction diagonalAngle := by rw [he]; linarith [diagonal_value_lower]
  exact hbase.trans_le (hmono ⟨le_rfl,hstart⟩ ⟨hstart,le_rfl⟩ hstart)

lemma opposite_upper_junction {z : ℝ}
    (hz : 0<z ∧ z≤Real.pi/3)
    (hs : 0≤otherLabel z td ∧ otherLabel z td≤Real.pi/4) :
    0<oppositeUpper z td := by
  by_cases hc : otherLabel z td ≤ s0
  · exact opposite_upper_circular hz.1
      ⟨by linarith [transition_coarse.2.2.2.2.2,td_bounds.1],le_rfl⟩ ⟨hs.1,hc⟩
  · have hs' : s0≤otherLabel z td := (lt_of_not_ge hc).le
    have hv : u0≤otherV z td ∧ otherV z td≤rd := by
      dsimp [otherV]
      constructor
      · dsimp [s0] at hs'; linarith
      · linarith [hs.2,pi_upper_22,rd_bounds.1]
    have htop : axialTop (otherV z td)=tieA (otherLabel z td) := by
      rw [axialTop_right hv]
      dsimp [otherV,axialLine,tieA]
      ring
    dsimp [oppositeUpper]
    rw [sideTopA_td,htop]
    exact diagonal_junction_pos hz ⟨hs',hs.2⟩

lemma diagonal_source_reduction {z t l : ℝ}
    (hz : 0≤z ∧ z≤Real.pi/3)
    (ht : td≤l ∧ l≤t)
    (hs : 0≤otherLabel z t ∧ otherLabel z l≤Real.pi/4) :
    oppositeUpper z l≤oppositeUpper z t := by
  have hvl : 0≤otherV z t ∧ otherV z t≤otherV z l ∧ otherV z l≤Real.pi/5 := by
    dsimp [otherV,otherLabel] at *
    exact ⟨by linarith,by linarith,by linarith⟩
  have hA := axialTop_displacement hvl.1 hvl.2.1 hvl.2.2
  have hS := Real.sin_nonneg_of_nonneg_of_le_pi hz.1 (by linarith [hz.2,Real.pi_pos])
  have hC := cos_nonneg_quarter (x := z) ⟨by linarith [hz.1,Real.pi_pos],by linarith [hz.2,Real.pi_pos]⟩
  have hp := mul_le_mul_of_nonneg_right hA hS
  have hd : 0≤t-l := sub_nonneg.mpr ht.2
  have hvd : otherV z l-otherV z t=(4/5)*(t-l) := by dsimp [otherV,otherLabel]; ring
  have hS1 := mul_nonneg hd (show 0≤1-Real.sin z from sub_nonneg.mpr (Real.sin_le_one z))
  have hC1 := mul_nonneg hd (show 0≤1-Real.cos z from sub_nonneg.mpr (Real.cos_le_one z))
  dsimp [oppositeUpper,inwardOpposite]
  rw [sideTopA_diagonal ht.1,sideTopA_diagonal (ht.1.trans ht.2)]
  dsimp [diagonal]
  rw [hvd] at hp
  nlinarith

lemma circular_source_line_reduction {z t r : ℝ}
    (hz : 19/100≤z ∧ z≤Real.pi/3)
    (ht : s0≤t ∧ t≤r) (hr : r≤td)
    (hs : s0≤otherLabel z r ∧ otherLabel z t≤Real.pi/4) :
    oppositeUpper z r≤oppositeUpper z t := by
  have hsdom (x : ℝ) (hx : t≤x ∧ x≤r) :
      u0≤otherV z x ∧ otherV z x≤rd := by
    dsimp [otherV,otherLabel] at *
    constructor
    · dsimp [s0] at hs; linarith
    · linarith [pi_upper_22,rd_bounds.1]
  have htline : axialTop (otherV z t)=tieA (otherLabel z t) := by
    rw [axialTop_right (hsdom t ⟨le_rfl,ht.2⟩)]
    dsimp [axialLine,otherV,tieA]; ring
  have hrline : axialTop (otherV z r)=tieA (otherLabel z r) := by
    rw [axialTop_right (hsdom r ⟨ht.2,le_rfl⟩)]
    dsimp [axialLine,otherV,tieA]; ring
  have ha := sideA_displacement ht.1 ht.2 hr
  have hm := line_to_circle_turn_margin hz
  have hp := mul_nonneg (sub_nonneg.mpr ht.2) (sub_nonneg.mpr hm.le)
  dsimp [oppositeUpper,inwardOpposite]
  rw [htline,hrline]
  simp only [sideTopA,ite_eq_left (ht.2.trans hr),ite_eq_left hr]
  dsimp [tieA,otherV,otherLabel]
  nlinarith

/-- Every positive-turn pair of upper endpoints is excluded. The proof is a
finite analytic case split, not a sampled parameter-space cover. -/
theorem opposite_upper_pos {z t : ℝ}
    (hz : 0<z ∧ z≤Real.pi/3)
    (ht : s0≤t ∧ t≤Real.pi/4)
    (hs : 0≤otherLabel z t ∧ otherLabel z t≤Real.pi/4) :
    0<oppositeUpper z t := by
  by_cases hdiag : td≤t
  · let l := max td (z-Real.pi/12)
    have hlt : l≤t := max_le hdiag (by dsimp [otherLabel] at hs; linarith [hs.2])
    have hld : td≤l := le_max_left _ _
    have hsl : otherLabel z l≤Real.pi/4 := by
      have hh : z-Real.pi/12≤l := le_max_right _ _
      dsimp [otherLabel]
      linarith
    have hsl0 : 0≤otherLabel z l := by dsimp [otherLabel] at *; linarith [hs.1]
    have hcomp := diagonal_source_reduction ⟨hz.1.le,hz.2⟩ ⟨hld,hlt⟩ ⟨hs.1,hsl⟩
    have hbase : 0<oppositeUpper z l := by
      by_cases hc : z-Real.pi/12≤td
      · have he : l=td := max_eq_left hc
        rw [he]
        exact opposite_upper_junction hz ⟨by simpa only [he] using hsl0,by simpa only [he] using hsl⟩
      · have he : l=z-Real.pi/12 := max_eq_right (le_of_not_ge hc)
        exact opposite_upper_cap hz ⟨hld,hlt.trans ht.2⟩
          (by rw [he]; dsimp [otherLabel]; ring)
    exact hbase.trans_le hcomp
  · have htc : t≤td := (lt_of_not_ge hdiag).le
    by_cases hcircle : otherLabel z t ≤ s0
    · exact opposite_upper_circular hz.1 ⟨ht.1,htc⟩ ⟨hs.1,hcircle⟩
    · let r := min td (z+Real.pi/6-s0)
      have htr : t≤r := le_min htc (by dsimp [otherLabel] at hcircle; linarith)
      have hrd : r≤td := min_le_left _ _
      have hsr : s0≤otherLabel z r := by
        have hh : r≤z+Real.pi/6-s0 := min_le_right _ _
        dsimp [otherLabel]
        linarith
      have hzlow : 19/100≤z := by
        have hsc := transition_bounds
        have hh : s0<otherLabel z t := lt_of_not_ge hcircle
        dsimp [otherLabel,s0] at hh ht
        linarith [pi_upper_22]
      have hcomp := circular_source_line_reduction ⟨hzlow,hz.2⟩ ⟨ht.1,htr⟩ hrd ⟨hsr,hs.2⟩
      have hbase : 0<oppositeUpper z r := by
        by_cases hc : td≤z+Real.pi/6-s0
        · have he : r=td := min_eq_left hc
          rw [he]
          exact opposite_upper_junction hz ⟨by rw [he] at hsr; linarith [transition_coarse.2.2.2.2.1],
            by dsimp [otherLabel] at hs ⊢; linarith [hs.2,htc]⟩
        · have he : r=z+Real.pi/6-s0 := min_eq_right (le_of_not_ge hc)
          have hsEq : otherLabel z r=s0 := by rw [he]; dsimp [otherLabel]; ring
          exact opposite_upper_circular hz.1 ⟨ht.1.trans htr,hrd⟩
            ⟨by rw [hsEq]; linarith [transition_coarse.2.2.2.2.1],by rw [hsEq]⟩
      exact hbase.trans_le hcomp

end Boundary

/-- Complete side/axial inward-opposite sector. Strictness is retained for
negative and zero turns through the original source remainder. -/
theorem inward_opposite_side_axial_property {a u A v : ℝ}
    (h : Admissible a u) (h' : Admissible A v)
    (hT : label a u=side a u) (hA : label A v=axial v) :
    PairProperty a u A v .positive .negative 2 := by
  let z := label a u+label A v-Real.pi/6
  by_cases hz0 : z≤0
  · have hl := inward_opposite_negative_turn h h' hT hA hz0
    refine ⟨by linarith [h.remainder_nonneg,abs_nonneg z],?_⟩
    intro ha hb
    linarith [ha.remainder_pos,abs_nonneg z]
  · have hz : 0<z ∧ z≤Real.pi/3 := by
      constructor
      · exact lt_of_not_ge hz0
      · dsimp [z]; linarith [h.label_le_quarter,h'.label_le_quarter]
    have ht : Boundary.s0≤label a u ∧ label a u≤Real.pi/4 :=
      ⟨(Boundary.side_state_transition_bounds h hT).2.2,h.label_le_quarter⟩
    have hsEq : Boundary.otherLabel z (label a u)=label A v := by dsimp [Boundary.otherLabel,z]; ring
    have hvEq : Boundary.otherV z (label a u)=v := by
      rw [Boundary.otherV,hsEq,hA]
      dsimp [axial]; ring
    have hp := Boundary.opposite_upper_pos hz ht
      ⟨by rw [hsEq]; exact h'.label_nonneg,by rw [hsEq]; exact h'.label_le_quarter⟩
    have ha := Boundary.side_radial_upper h hT
    have hb := Boundary.axial_upper h' hA
    have hs0 := Real.sin_nonneg_of_nonneg_of_le_pi hz.1.le (by linarith [hz.2,Real.pi_pos])
    have hm := mul_nonneg (sub_nonneg.mpr hb) hs0
    have hcompare : Boundary.oppositeUpper z (label a u) ≤ inwardOpposite a A v z := by
      dsimp [Boundary.oppositeUpper]
      rw [hvEq]
      dsimp [inwardOpposite]
      nlinarith
    have hpos : 0<pairSupport a u A v .positive .negative 2 gap := by
      rw [inward_opposite_formula h h']
      exact hp.trans_le hcompare
    exact ⟨hpos.le,fun _ _ => hpos⟩

end SquaresInCircles.Seven
