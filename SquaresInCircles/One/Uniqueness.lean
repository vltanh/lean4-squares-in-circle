import SquaresInCircles.One.Optimality
import SquaresInCircles.Common.Contacts

/-! At the optimal radius the square is centred at the disk centre. -/
noncomputable section
namespace SquaresInCircles

/-- At the optimal radius the square is centred at the disk centre. -/
theorem One.uniqueness (S : Fin 1 → UnitSquare) (o : Point)
    (hp : Packing S o One.radius) : HasNormalForm S o One.centers := by
  have h := hp.phi_le 0
  rw [One.radius_sq] at h
  have ha := alpha_nonneg (S 0) o
  have hb := beta_nonneg (S 0) o
  unfold phi at h
  have ha0 : alpha (S 0) o=0 := by nlinarith
  have hb0 : beta (S 0) o=0 := by nlinarith
  have hc : (S 0).center=o := by
    have hn := local_center_norm (S 0) o
    rw [ha0,hb0] at hn
    simp only [normSq,sub] at hn
    apply Prod.ext <;> nlinarith [sq_nonneg ((S 0).center.1-o.1),
      sq_nonneg ((S 0).center.2-o.2)]
  obtain ⟨t,htc,hts⟩ := frame_angle (S 0)
  have hcos : (t:Direction).cos=(S 0).cosine := htc
  have hsin : (t:Direction).sin=(S 0).sine := hts
  apply normal_form_of_slots (φ := (t:Direction)) hp.disjoint
  intro i
  obtain rfl : i=0 := Subsingleton.elim i 0
  refine ⟨0,?_⟩
  rw [show One.centers 0=(0,0) from rfl]
  simpa only [hc,sub,sub_self,frameX,frameY,mul_zero,add_zero] using
    self_represents (S 0) o (t:Direction) hcos hsin

end SquaresInCircles
