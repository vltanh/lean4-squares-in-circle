import SquaresInCircles.Seven.Uniqueness.PairGeometry
import SquaresInCircles.Common.ArcMetric
import Mathlib.Data.Fin.Tuple.Sort

/-!
# Angular rigidity at the critical budget

Sort six real lifts. Five consecutive gaps and the wraparound gap are at
least pi/3; their six nonnegative slacks sum to zero. This proves the regular
hexagon rather than assuming an equality tiling.
-/
noncomputable section
open Set
namespace SquaresInCircles.Seven
namespace Equality

lemma coe_angle_distance_le {x y : ℝ} (hxy : x ≤ y) :
    dist (x : Direction) (y : Direction) ≤ y-x := by
  rw [dist_comm,dist_eq_norm,←Real.Angle.coe_sub]
  exact (direction_coe_norm_le (y-x)).trans_eq (abs_of_nonneg (sub_nonneg.mpr hxy))

private def steps (r : Fin 6 → ℝ) : Fin 6 → ℝ :=
  ![r 1-r 0,r 2-r 1,r 3-r 2,r 4-r 3,r 5-r 4,r 0+2*Real.pi-r 5]

/-- Six separated marker directions are precisely one regular hexagon. -/
theorem six_directions_hexagon (c : Fin 6 → Direction)
    (hsep : ∀ i j, i ≠ j → gap ≤ dist (c i) (c j)) :
    ∃ (φ : Direction) (σ : Equiv.Perm (Fin 6)),
      ∀ i, c (σ i) = φ+(((i.val : ℝ)*gap : ℝ) : Direction) := by
  classical
  let r : Fin 6 → ℝ := fun i => (c i).toReal
  let σ := Tuple.sort r
  let p : Fin 6 → ℝ := fun i => r (σ i)
  have hmono : Monotone p := Tuple.monotone_sort r
  have hrepr (i : Fin 6) : (p i : Direction) = c (σ i) := Real.Angle.coe_toReal _
  have hlinear (i j : Fin 6) (hij : i < j) : gap ≤ p j-p i := by
    have hd := coe_angle_distance_le (hmono hij.le)
    rw [hrepr,hrepr] at hd
    exact (hsep (σ i) (σ j) (fun he => (ne_of_lt hij) (σ.injective he))).trans hd
  have hwrap : gap ≤ p 0+2*Real.pi-p 5 := by
    have h0 : -Real.pi < p 0 := Real.Angle.neg_pi_lt_toReal _
    have h5 : p 5 ≤ Real.pi := Real.Angle.toReal_le_pi _
    have hd := coe_angle_distance_le (show p 5 ≤ p 0+2*Real.pi by linarith)
    have he : ((p 0+2*Real.pi : ℝ) : Direction) = (p 0 : Direction) := by
      rw [Real.Angle.coe_add]
      simp
    rw [he,hrepr,hrepr] at hd
    exact (hsep (σ 5) (σ 0) (fun he => by have := σ.injective he; norm_num at this)).trans hd
  have hstep (i : Fin 6) : gap ≤ steps p i := by
    fin_cases i
    · exact hlinear 0 1 (by decide)
    · exact hlinear 1 2 (by decide)
    · exact hlinear 2 3 (by decide)
    · exact hlinear 3 4 (by decide)
    · exact hlinear 4 5 (by decide)
    · exact hwrap
  have hsum : ∑ i, (steps p i-gap) = 0 := by
    simp [steps,Fin.sum_univ_succ,gap]
    ring
  have htight (i : Fin 6) : steps p i = gap := by
    have hn (j : Fin 6) : 0 ≤ steps p j-gap := sub_nonneg.mpr (hstep j)
    have hu := Finset.single_le_sum (fun j _ => hn j) (Finset.mem_univ i)
    rw [hsum] at hu
    linarith [hstep i]
  have hp (i : Fin 6) : p i = p 0+(i.val : ℝ)*gap := by
    have h0 := htight 0
    have h1 := htight 1
    have h2 := htight 2
    have h3 := htight 3
    have h4 := htight 4
    fin_cases i <;> norm_num [steps] at * <;> linarith
  refine ⟨c (σ 0),σ,?_⟩
  intro i
  rw [←hrepr i,hp,Real.Angle.coe_add,hrepr]

def next (i : Fin 6) : Fin 6 := i+1

lemma next_ne (i : Fin 6) : next i ≠ i := by fin_cases i <;> decide

lemma hexagon_successor {c : Fin 6 → Direction} {φ : Direction}
    (h : ∀ i, c i = φ+(((i.val : ℝ)*gap : ℝ) : Direction)) (i : Fin 6) :
    (gap : Direction) = c (next i)-c i := by
  have hperiod : ((6*gap : ℝ) : Direction) = 0 := by
    rw [show (6 : ℝ)*gap = 2*Real.pi by dsimp [gap]; ring]
    simp
  have hwrap : (((-5 : ℝ)*gap : ℝ) : Direction) = (gap : Direction) := by
    rw [show (-5 : ℝ)*gap = gap-6*gap by ring,Real.Angle.coe_sub,hperiod,sub_zero]
  have hd : c (next i)-c i =
      ((((next i).val : ℝ)*gap-(i.val : ℝ)*gap : ℝ) : Direction) := by
    rw [h,h,Real.Angle.coe_sub]
    abel
  have hr : ((next i).val : ℝ)*gap-(i.val : ℝ)*gap =
      if i = 5 then -5*gap else gap := by
    fin_cases i <;> norm_num [next] <;> ring
  rw [hd,hr]
  split_ifs
  · exact hwrap.symm
  · rfl

/-- Seven directions with separation at least pi/3 cannot occur. -/
lemma seven_directions_impossible (c : Fin 7 → Direction)
    (hsep : ∀ i j, i ≠ j → gap ≤ dist (c i) (c j)) : False := by
  have hballs : Pairwise (fun i j =>
      Disjoint (Metric.closedBall (c i) (1/2)) (Metric.closedBall (c j) (1/2))) := by
    intro i j hij
    rw [Set.disjoint_left]
    intro z hi hj
    have htri := dist_triangle (c i) z (c j)
    have hi' : dist (c i) z ≤ 1/2 := by simpa [dist_comm] using hi
    have hj' : dist z (c j) ≤ 1/2 := hj
    have hg := hsep i j hij
    dsimp [gap] at hg
    linarith [pi_lower_157]
  have hb := closed_arc_budget c (fun _ => (1/2 : ℝ))
    (fun _ => ⟨by norm_num,by linarith [Real.pi_pos,pi_lower_157]⟩) hballs
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at hb
  norm_num at hb
  linarith [pi_lt_22_over_7]

/-- Exactly one square contains the tested point at the optimum. The center
of that square is not assumed to equal the tested point. -/
theorem exists_containing (S : Fin 7 → UnitSquare) (o : Point)
    (hp : Packing S o radius) : ∃ i, openSquare (S i) o := by
  classical
  by_contra hn
  have hext : ∀ i, ¬ openSquare (S i) o := by simpa only [not_exists] using hn
  choose C hsort using (fun i => sorted_square_chart (S i) o)
  have hadm (i : Fin 7) : Admissible (C i).a (C i).b := by
    apply chart_admissible (C i) (hsort i) (hext i)
    have hh := hp.phi_le i
    simpa only [radius_sq,targetSq] using hh
  apply seven_directions_impossible (fun i => chartMarker (C i))
  intro i j hij
  exact marker_separation_closed (C i) (C j) (hadm i) (hadm j) (hp.disjoint i j hij)

end Equality
end SquaresInCircles.Seven
