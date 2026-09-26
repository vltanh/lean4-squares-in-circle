import SquaresInCircles.Seven.Labels
import SquaresInCircles.Common.Angles

/-!
# Six markers

Six directions pairwise at least `π/3` apart form a regular hexagon, by
`regular_polygon`. So neighbours are exactly `π/3` apart, and six directions
cannot be pairwise more than `π/3` apart.
-/
noncomputable section
namespace SquaresInCircles.Seven
namespace Equality

/-- Six directions pairwise at least `π/3` apart form a regular hexagon. -/
theorem six_directions_hexagon (c : Fin 6 → Direction)
    (hsep : ∀ i j, i ≠ j → gap ≤ dist (c i) (c j)) :
    ∃ (φ : Direction) (σ : Equiv.Perm (Fin 6)),
      ∀ i, c (σ i) = φ+(((i.val : ℝ)*gap : ℝ) : Direction) :=
  regular_polygon c (by unfold gap; push_cast; ring) hsep

def next (i : Fin 6) : Fin 6 := i+1

lemma next_ne (i : Fin 6) : next i ≠ i := by fin_cases i <;> decide

lemma hexagon_successor {c : Fin 6 → Direction} {φ : Direction}
    (h : ∀ i, c i = φ+(((i.val : ℝ)*gap : ℝ) : Direction)) (i : Fin 6) :
    (gap : Direction) = c (next i)-c i := by
  rw [h,h,add_sub_add_left_eq_sub,←Real.Angle.coe_sub,Real.Angle.angle_eq_iff_two_pi_dvd_sub]
  exact ⟨if i = 5 then 1 else 0,by fin_cases i <;> norm_num [next,gap] <;> ring⟩

end Equality

/-- Six points cannot all have pairwise circular distances strictly above pi/3. -/
theorem six_markers_impossible (c : Fin 6 → Direction)
    (hsep : Pairwise (fun i j => Real.pi/3 < dist (c i) (c j))) : False := by
  obtain ⟨φ,σ,hc⟩ := Equality.six_directions_hexagon c (fun i j hij => (hsep hij).le)
  have hd : Real.pi/3 < dist (c (σ (Equality.next 0))) (c (σ 0)) :=
    hsep (σ.injective.ne (Equality.next_ne 0))
  rw [dist_eq_norm,← Equality.hexagon_successor hc 0] at hd
  exact hd.not_ge ((direction_coe_norm_le gap).trans_eq (abs_of_pos (by unfold gap; positivity)))

end SquaresInCircles.Seven
