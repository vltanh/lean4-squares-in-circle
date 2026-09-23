import SquaresInCircles.Two.Optimality
import SquaresInCircles.Common.Angles

/-! At the optimal radius the disk centre is the midpoint of the two centres,
and `unit_contact` makes the squares share a full edge: the rectangle. -/
noncomputable section
namespace SquaresInCircles

/-- At the optimal radius the two squares form the rectangle. -/
theorem Two.uniqueness (S : Fin 2 → UnitSquare) (o : Point)
    (hp : Packing S o Two.radius) : HasNormalForm S o Two.centers := by
  have hnear (i : Fin 2) : normSq (sub (S i).center o) ≤ 1/4 := by
    rw [local_center_norm]
    have h := hp.phi_le i
    rw [Two.radius_sq] at h
    exact center_near_of_phi_le (alpha_nonneg _ _) (beta_nonneg _ _) h
  have hd01 := hp.2.2 0 1 (by decide)
  have hfar := centers_distance_sq_ge_one (S 0) (S 1) hd01
  have hpar := normSq_parallelogram (S 1).center (S 0).center o
  have hnn := normSq_nonneg (sub (add (S 1).center (S 0).center) (scale 2 o))
  have hone : normSq (sub (S 1).center (S 0).center)=1 := by
    linarith [hnear 0,hnear 1]
  have hmid : normSq (sub (add (S 1).center (S 0).center) (scale 2 o))=0 := by
    linarith [hnear 0,hnear 1]
  simp only [normSq,sub,add,scale] at hmid
  have hmx : (S 0).center.1=2*o.1-(S 1).center.1 := by
    nlinarith [sq_nonneg ((S 1).center.1+(S 0).center.1-2*o.1),
      sq_nonneg ((S 1).center.2+(S 0).center.2-2*o.2)]
  have hmy : (S 0).center.2=2*o.2-(S 1).center.2 := by
    nlinarith [sq_nonneg ((S 1).center.1+(S 0).center.1-2*o.1),
      sq_nonneg ((S 1).center.2+(S 0).center.2-2*o.2)]
  obtain ⟨haxes,hslots⟩ := unit_contact (S 0) (S 1) hd01 hone
  obtain ⟨t,htc,hts⟩ := frame_angle (S 0)
  have hcos : (t:Direction).cos=(S 0).cosine := htc
  have hsin : (t:Direction).sin=(S 0).sine := hts
  have r0 := self_represents (S 0) o (t:Direction) hcos hsin
  have r1 := same_axes_represents (S 0) (S 1) o (t:Direction) hcos hsin haxes
  -- In the frame of `S 0`, the centres are `∓ d/2` for the unit offset `d`.
  have hx0 : frameX (S 0) (sub (S 0).center o)=
      -frameX (S 0) (sub (S 1).center (S 0).center)/2 := by
    simp only [frameX,sub,hmx,hmy]; ring
  have hy0 : frameY (S 0) (sub (S 0).center o)=
      -frameY (S 0) (sub (S 1).center (S 0).center)/2 := by
    simp only [frameY,sub,hmx,hmy]; ring
  have hx1 : frameX (S 0) (sub (S 1).center o)=
      frameX (S 0) (sub (S 1).center (S 0).center)/2 := by
    simp only [frameX,sub,hmx,hmy]; ring
  have hy1 : frameY (S 0) (sub (S 1).center o)=
      frameY (S 0) (sub (S 1).center (S 0).center)/2 := by
    simp only [frameY,sub,hmx,hmy]; ring
  rw [hx0,hy0] at r0
  rw [hx1,hy1] at r1
  -- A vertical offset is turned into a horizontal one by a quarter turn.
  have hq : (t:Direction)=((t:Direction)-quarterShift 3)+quarterShift 3 := by abel
  rcases hslots with ⟨hx,hy⟩ | ⟨hx,hy⟩ | ⟨hx,hy⟩ | ⟨hx,hy⟩ <;> rw [hx,hy] at r0 r1
  · apply normal_form_of_slots (φ := (t:Direction)) hp.disjoint
    intro i
    rcases (show i=0 ∨ i=1 by revert i; decide) with rfl | rfl
    · exact ⟨0,by convert r0 using 1; norm_num [Two.centers]⟩
    · exact ⟨1,by convert r1 using 1; norm_num [Two.centers]⟩
  · rw [hq] at r0 r1
    have q0 := represents_quarter 3 r0
    have q1 := represents_quarter 3 r1
    apply normal_form_of_slots (φ := (t:Direction)-quarterShift 3) hp.disjoint
    intro i
    rcases (show i=0 ∨ i=1 by revert i; decide) with rfl | rfl
    · exact ⟨0,by convert q0 using 1; norm_num [Two.centers,turnPoint]⟩
    · exact ⟨1,by convert q1 using 1; norm_num [Two.centers,turnPoint]⟩
  · apply normal_form_of_slots (φ := (t:Direction)) hp.disjoint
    intro i
    rcases (show i=0 ∨ i=1 by revert i; decide) with rfl | rfl
    · exact ⟨1,by convert r0 using 1; norm_num [Two.centers]⟩
    · exact ⟨0,by convert r1 using 1; norm_num [Two.centers]⟩
  · rw [hq] at r0 r1
    have q0 := represents_quarter 3 r0
    have q1 := represents_quarter 3 r1
    apply normal_form_of_slots (φ := (t:Direction)-quarterShift 3) hp.disjoint
    intro i
    rcases (show i=0 ∨ i=1 by revert i; decide) with rfl | rfl
    · exact ⟨1,by convert q0 using 1; norm_num [Two.centers,turnPoint]⟩
    · exact ⟨0,by convert q1 using 1; norm_num [Two.centers,turnPoint]⟩

end SquaresInCircles
