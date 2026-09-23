import SquaresInCircles.Common.AngularBudget

/-!
# Metric facts for occupied arc witnesses

An open arc here is an actual region-membership certificate, not an angular
shadow. These lemmas do not assume that it is the whole circle intersection.
No packing theorem is used.
-/
noncomputable section
open Set
namespace SquaresInCircles

lemma direction_coe_norm_le (t : ℝ) : ‖(t : Direction)‖ ≤ |t| := by
  have h := QuotientAddGroup.norm_mk_le_norm
    (S := AddSubgroup.zmultiples (2 * Real.pi)) (m := t)
  rw [Real.norm_eq_abs] at h
  exact h

lemma direction_dist_coe_le (a b : ℝ) :
    dist (a : Direction) (b : Direction) ≤ |a-b| := by
  rw [dist_eq_norm, ← Real.Angle.coe_sub]
  exact direction_coe_norm_le _

lemma direction_diameter (a b : Direction) : dist a b ≤ Real.pi := by
  rw [direction_dist]
  exact (a-b).abs_toReal_le_pi

/-- Two disjoint positive-radius occupied arcs have separated midpoint directions. -/
lemma OpenArc.centers_separated {o : Point} {r : ℝ} {U V : Set Point}
    (A : OpenArc o r U) (B : OpenArc o r V) (hUV : Disjoint U V) :
    A.halfWidth + B.halfWidth ≤ dist A.center B.center := by
  by_contra hn
  have hd : dist A.center B.center < A.halfWidth+B.halfWidth := lt_of_not_ge hn
  let H := A.halfWidth+B.halfWidth
  have hH : 0 < H := add_pos A.positive B.positive
  let s := A.halfWidth/H
  let t := B.halfWidth/H
  have hs : 0 < s := div_pos A.positive hH
  have ht : 0 < t := div_pos B.positive hH
  have hst : s+t=1 := by
    dsimp only [s,t]
    rw [← add_div]
    exact div_self (ne_of_gt hH)
  have hsH : s*H=A.halfWidth := div_mul_cancel₀ _ (ne_of_gt hH)
  have htH : t*H=B.halfWidth := div_mul_cancel₀ _ (ne_of_gt hH)
  let d := (B.center-A.center).toReal
  have hdabs : |d|=dist A.center B.center := by
    rw [dist_comm, direction_dist]
  have hrep : B.center=A.center+(d:Direction) := direction_offset _ _
  let z := A.center+((s*d:ℝ):Direction)
  have hza : z-A.center=((s*d:ℝ):Direction) := by dsimp [z]; abel
  have hzb : z-B.center=((-t*d:ℝ):Direction) := by
    rw [hrep]
    have he : s*d-d = -t*d := by rw [show s = 1-t by linarith]; ring
    dsimp [z]
    rw [← he,Real.Angle.coe_sub]
    abel
  have hzA : dist z A.center < A.halfWidth := by
    rw [dist_eq_norm,hza]
    have hb := direction_coe_norm_le (s*d)
    rw [abs_mul,abs_of_pos hs,hdabs] at hb
    have hm := mul_lt_mul_of_pos_left hd hs
    change s*dist A.center B.center < s*H at hm
    rw [hsH] at hm
    exact hb.trans_lt hm
  have hzB : dist z B.center < B.halfWidth := by
    rw [dist_eq_norm,hzb]
    have hb := direction_coe_norm_le (-t*d)
    rw [abs_mul,abs_neg,abs_of_pos ht,hdabs] at hb
    have hm := mul_lt_mul_of_pos_left hd ht
    change t*dist A.center B.center < t*H at hm
    rw [htH] at hm
    exact hb.trans_lt hm
  exact Set.disjoint_left.mp hUV (A.inside z hzA) (B.inside z hzB)

lemma direction_norm_wrapped {t : ℝ} (ht : |t| ≤ 2*Real.pi) :
    ‖(t:Direction)‖ ≤ 2*Real.pi-|t| := by
  rcases le_total 0 t with hs | hs
  · have he : ((t-2*Real.pi:ℝ):Direction)=(t:Direction) := by simp
    have hh := direction_coe_norm_le (t-2*Real.pi)
    rw [he,abs_of_nonpos (by rw [abs_of_nonneg hs] at ht; linarith)] at hh
    rw [abs_of_nonneg hs]
    linarith
  · have he : ((t+2*Real.pi:ℝ):Direction)=(t:Direction) := by simp
    have hh := direction_coe_norm_le (t+2*Real.pi)
    rw [he,abs_of_nonneg (by rw [abs_of_nonpos hs] at ht; linarith)] at hh
    rw [abs_of_nonpos hs]
    linarith

/-- Three geodesic distances on a circle of circumference `2*pi` sum to at most `2*pi`. -/
lemma direction_triangle_perimeter (x y z : Direction) :
    dist x y + dist y z + dist z x ≤ 2*Real.pi := by
  let a := (x-z).toReal
  let b := (y-z).toReal
  have ha : |a| ≤ Real.pi := (x-z).abs_toReal_le_pi
  have hb : |b| ≤ Real.pi := (y-z).abs_toReal_le_pi
  have hx : x=z+(a:Direction) := direction_offset _ _
  have hy : y=z+(b:Direction) := direction_offset _ _
  have he : x-y=((a-b:ℝ):Direction) := by
    rw [hx,hy,Real.Angle.coe_sub]; abel
  have hd : dist x y ≤ |a-b| := by
    rw [dist_eq_norm,he]; exact direction_coe_norm_le _
  have hd' : dist x y ≤ 2*Real.pi-|a-b| := by
    rw [dist_eq_norm,he]
    apply direction_norm_wrapped
    exact (abs_sub a b).trans (by linarith)
  have hxz : dist z x=|a| := by rw [dist_comm,direction_dist]
  have hyz : dist y z=|b| := by rw [direction_dist]
  rw [hxz,hyz]
  rcases le_total a 0 with ha0 | ha0 <;>
    rcases le_total b 0 with hb0 | hb0 <;>
    rcases le_total (a-b) 0 with hab | hab <;>
    simp_all only [abs_of_nonneg,abs_of_nonpos] <;> linarith

lemma triple_arc_budget {o : Point} {r : ℝ} {U V W : Set Point}
    (A : OpenArc o r U) (B : OpenArc o r V) (C : OpenArc o r W)
    (hUV : Disjoint U V) (hUW : Disjoint U W) (hVW : Disjoint V W) :
    A.halfWidth+B.halfWidth+C.halfWidth ≤ Real.pi := by
  let regions : Fin 3 → Set Point := ![U,V,W]
  let arcs : (i : Fin 3) → OpenArc o r (regions i) := fun i =>
    match i with
    | 0 => A
    | 1 => B
    | 2 => C
  have hdisj : Pairwise (fun i j => Disjoint (regions i) (regions j)) := by
    intro i j hij
    fin_cases i <;> fin_cases j
    · exact False.elim (hij rfl)
    · exact hUV
    · exact hUW
    · exact hUV.symm
    · exact False.elim (hij rfl)
    · exact hVW
    · exact hUW.symm
    · exact hVW.symm
    · exact False.elim (hij rfl)
  have h := open_arc_budget arcs hdisj
  rw [Fin.sum_univ_three] at h
  exact h

/-- Bounds for the third separation supplied by three disjoint arc witnesses. -/
lemma OpenArc.third_distance_bounds {o : Point} {r : ℝ} {U V W : Set Point}
    (A : OpenArc o r U) (B : OpenArc o r V) (C : OpenArc o r W)
    (hUV : Disjoint U V) (hUW : Disjoint U W) (hVW : Disjoint V W) :
    B.halfWidth+C.halfWidth ≤ dist B.center C.center ∧
      dist B.center C.center ≤
        2*Real.pi-2*A.halfWidth-B.halfWidth-C.halfWidth := by
  refine ⟨B.centers_separated C hVW,?_⟩
  have hab := A.centers_separated B hUV
  have hac := A.centers_separated C hUW
  have hp := direction_triangle_perimeter B.center C.center A.center
  rw [dist_comm C.center A.center] at hp
  linarith

end SquaresInCircles
