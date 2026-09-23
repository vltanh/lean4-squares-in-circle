import SquaresInCircles.Common.Contacts
import SquaresInCircles.Five.Optimality

/-! The closed dodecagon itself is rigid.  This is stronger than uniqueness
for the circular packing problem and permits equality in every input facet. -/
noncomputable section
open Set
namespace SquaresInCircles

lemma dodecagon_norm_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (h : P5 a b) :
    a^2+b^2 ≤ 1 := by
  by_cases hs : a+b ≤ 1
  · nlinarith [mul_nonneg ha hb]
  · have hroot : Real.sqrt 5 < 12/5 := by
      have hh := Real.sq_sqrt (show (0:ℝ) ≤ 5 by norm_num)
      nlinarith [Real.sqrt_nonneg 5]
    have htop : a+b < 7/5 := by linarith [h.2]
    have hd0 : -(3-2*(a+b)) ≤ a-b := by linarith [h.1.2]
    have hd1 : a-b ≤ 3-2*(a+b) := by linarith [h.1.1]
    have hsq := mul_nonneg (show 0 ≤ (3-2*(a+b))+(a-b) by linarith)
      (show 0 ≤ (3-2*(a+b))-(a-b) by linarith)
    have hp := mul_neg_of_pos_of_neg (show 0 < a+b-1 by linarith)
      (show 5*(a+b)-7 < 0 by linarith)
    linarith

/-- All five slots are forced by the centered square and unit-distance contacts. -/
theorem Five.polygon_uniqueness (S : Fin 5 → UnitSquare) (o : Point)
    (hd : InteriorDisjoint S) (hp : ∀ i, P5 (alpha (S i) o) (beta (S i) o)) :
    HasNormalForm S o Five.centers := by
  classical
  obtain ⟨k,hk⟩ := five_centered_square S o hd hp
  obtain ⟨t,htc,hts⟩ := frame_angle (S k)
  let φ : Direction := (t:Direction)
  have hc : φ.cos=(S k).cosine := htc
  have hs : φ.sin=(S k).sine := hts
  apply normal_form_of_slots (φ := φ) hd
  intro i
  by_cases hi : i=k
  · subst i
    refine ⟨0,?_⟩
    have hh := self_represents (S k) o φ hc hs
    rw [show Five.centers 0=(0,0) by simp [Five.centers]]
    simpa only [hk,sub,sub_self,frameX,frameY,mul_zero,add_zero] using hh
  · have hlow := centers_distance_sq_ge_one (S k) (S i) (hd k i (Ne.symm hi))
    have hupp : normSq (sub (S i).center o) ≤ 1 := by
      rw [local_center_norm]
      exact dodecagon_norm_le (alpha_nonneg _ _) (beta_nonneg _ _) (hp i)
    have hone : normSq (sub (S i).center (S k).center)=1 := by rw [hk] at *; linarith
    obtain ⟨haxes,hslots⟩ := unit_contact (S k) (S i) (hd k i (Ne.symm hi)) hone
    have hrep := same_axes_represents (S k) (S i) o φ hc hs haxes
    rw [hk] at hslots
    rcases hslots with ⟨hx,hy⟩ | ⟨hx,hy⟩ | ⟨hx,hy⟩ | ⟨hx,hy⟩ <;> rw [hx,hy] at hrep
    exacts [⟨1,hrep⟩,⟨2,hrep⟩,⟨3,hrep⟩,⟨4,hrep⟩]

/-- Geometric uniqueness of the radius-sqrt(5/2) disk packing. -/
theorem Five.uniqueness (S : Fin 5 → UnitSquare) (o : Point)
    (hp : Packing S o Five.radius) : HasNormalForm S o Five.centers := by
  apply Five.polygon_uniqueness S o hp.disjoint
  intro i
  apply p5_of_phi_le
  have h := hp.phi_le i
  rwa [Five.radius_sq] at h

end SquaresInCircles
