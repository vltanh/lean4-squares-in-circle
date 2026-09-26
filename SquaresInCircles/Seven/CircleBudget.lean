import SquaresInCircles.Seven.Labels
import SquaresInCircles.Common.ArcMetric
import Mathlib.Data.Fin.Tuple.Sort

/-!
# Six markers

Six directions pairwise at least `π/3` apart form a regular hexagon: sorted,
their six gaps, including the one that wraps round, are at least `π/3` and add
up to `2π`. So neighbours are exactly `π/3` apart, and six directions cannot be
pairwise more than `π/3` apart.
-/
noncomputable section
namespace SquaresInCircles.Seven
namespace Equality

lemma coe_angle_distance_le {x y : ℝ} (hxy : x ≤ y) :
    dist (x : Direction) (y : Direction) ≤ y-x := by
  rw [dist_comm,dist_eq_norm,←Real.Angle.coe_sub]
  exact (direction_coe_norm_le (y-x)).trans_eq (abs_of_nonneg (sub_nonneg.mpr hxy))

private def steps (r : Fin 6 → ℝ) : Fin 6 → ℝ :=
  ![r 1-r 0,r 2-r 1,r 3-r 2,r 4-r 3,r 5-r 4,r 0+2*Real.pi-r 5]

/-- Six directions pairwise at least `π/3` apart form a regular hexagon. -/
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

end Equality

/-- Six points cannot all have pairwise circular distances strictly above pi/3. -/
theorem six_markers_impossible (c : Fin 6 → Direction)
    (hsep : Pairwise (fun i j => Real.pi/3 < dist (c i) (c j))) : False := by
  obtain ⟨φ,σ,hc⟩ := Equality.six_directions_hexagon c (fun i j hij => (hsep hij).le)
  have hd : Real.pi/3 < dist (c (σ (Equality.next 0))) (c (σ 0)) :=
    hsep (σ.injective.ne (Equality.next_ne 0))
  have he : (gap : Direction) = c (σ (Equality.next 0))-c (σ 0) :=
    Equality.hexagon_successor (c := fun i => c (σ i)) hc 0
  rw [dist_eq_norm,← he] at hd
  have hle := direction_coe_norm_le gap
  rw [abs_of_pos (show 0 < gap by unfold gap; positivity)] at hle
  exact lt_irrefl gap (hd.trans_le hle)

end SquaresInCircles.Seven
