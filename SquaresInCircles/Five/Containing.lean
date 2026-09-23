import SquaresInCircles.Five.Exterior

/-! The five-square containing case: a safely swept square contains a disk,
which in turn contains a 72-degree arc. -/
noncomputable section
open Set
namespace SquaresInCircles

lemma containing_center_norm (S : UnitSquare) {o : Point} (ho : openSquare S o) :
    normSq (sub S.center o) < 1/2 := by
  have ha : alpha S o < 1/2 := ho.1
  have hb : beta S o < 1/2 := ho.2
  rw [local_center_norm]
  nlinarith [alpha_nonneg S o,beta_nonneg S o]

/-- Polar form of a nonzero vector, from the complex number `v.1 + i v.2`. -/
lemma vector_direction {v : Point} (hv : v ≠ (0,0)) :
    ∃ (θ : Direction) (l : ℝ), 0 < l ∧ l^2=normSq v ∧
      v=(l*θ.cos,l*θ.sin) := by
  let z : ℂ := ⟨v.1,v.2⟩
  have hz : z ≠ 0 := fun h => hv (Prod.ext (congrArg Complex.re h) (congrArg Complex.im h))
  refine ⟨(Complex.arg z:Direction),‖z‖,norm_pos_iff.mpr hz,?_,?_⟩
  · rw [Complex.sq_norm,Complex.normSq_apply]; simp only [normSq,z]; ring
  · simp only [Real.Angle.cos_coe,Real.Angle.sin_coe,Complex.norm_mul_cos_arg,
      Complex.norm_mul_sin_arg,z]

lemma circle_distance_formula (o : Point) (r s : ℝ) (θ : Direction) (t : ℝ) :
    normSq (sub (circlePoint o r (θ+(t:Direction))) (circlePoint o s θ)) =
      r^2+s^2-2*r*s*Real.cos t := by
  have hid : normSq (sub (circlePoint o r (θ+(t:Direction))) (circlePoint o s θ)) =
      r^2*(θ.cos^2+θ.sin^2)*(Real.cos t^2+Real.sin t^2) +
      s^2*(θ.cos^2+θ.sin^2)-2*r*s*Real.cos t*(θ.cos^2+θ.sin^2) := by
    dsimp [normSq,sub,circlePoint]
    simp only [Real.Angle.cos_add,Real.Angle.sin_add,Real.Angle.cos_coe,Real.Angle.sin_coe]
    ring
  rw [hid,Real.Angle.cos_sq_add_sin_sq]
  rw [Real.cos_sq_add_sin_sq]
  ring

/-- The ray sweep contains a radius-1/2 disk at distance `1/sqrt(2)` from `o`. -/
lemma containing_ray_disk (S : UnitSquare) (o : Point)
    (ho : openSquare S o) (hne : S.center ≠ o) :
    ∃ θ : Direction, ∀ p : Point,
      normSq (sub p (circlePoint o halfDiagonal θ)) < 1/4 → p ∈ openRay S o := by
  obtain ⟨θ,l,hl0,hl2,hvθ⟩ := vector_direction (sub_ne_origin hne)
  have hl : l < halfDiagonal := by
    nlinarith [containing_center_norm S ho,halfDiagonal_sq,halfDiagonal_pos]
  let t := halfDiagonal/l-1
  have ht : 0 ≤ t := by
    dsimp [t]
    have hh : 1 < halfDiagonal/l := (lt_div_iff₀ hl0).mpr (by linarith)
    linarith
  let w := scale t (sub S.center o)
  have hz : circlePoint o halfDiagonal θ=add S.center w := by
    have hc₁ := congrArg Prod.fst hvθ
    have hc₂ := congrArg Prod.snd hvθ
    apply Prod.ext <;> dsimp [circlePoint,add,w,scale,t,sub] at * <;>
      field_simp [ne_of_gt hl0] <;> nlinarith
  refine ⟨θ,?_⟩
  intro p hp
  let q := sub p w
  have he : sub q S.center=sub p (circlePoint o halfDiagonal θ) := by
    rw [hz]
    apply Prod.ext <;> dsimp [q,sub,add] <;> ring
  have hq : openSquare S q := small_disk_in_openSquare S (by simpa only [he] using hp)
  refine ⟨t,ht,q,hq,?_⟩
  apply Prod.ext <;> dsimp [q,w,sub,add] <;> ring

lemma five_arc_in_radial_disk (o : Point) (θ : Direction) {φ : Direction}
    (hφ : dist φ θ < Real.pi/5) :
    normSq (sub (circlePoint o auxFive φ) (circlePoint o halfDiagonal θ)) < 1/4 := by
  let t := (φ-θ).toReal
  have ht : |t| < Real.pi/5 := by simpa only [direction_dist] using hφ
  have hcos := cos_gt_401_500 ht.le
  have hprod := mul_lt_mul_of_pos_left hcos halfDiagonal_pos
  have he : φ=θ+(t:Direction) := direction_offset φ θ
  rw [he,circle_distance_formula]
  have ha := halfDiagonal_gt_707
  have ha2 := halfDiagonal_sq
  dsimp [auxFive]
  linarith

/-- A containing square with nonzero center supplies the missing 72-degree arc. -/
theorem five_containing_arc (S : UnitSquare) (o : Point)
    (ho : openSquare S o) (hne : S.center ≠ o) :
    ∃ A : OpenArc o auxFive (openRay S o), A.halfWidth=Real.pi/5 := by
  obtain ⟨θ,hθ⟩ := containing_ray_disk S o ho hne
  refine ⟨{ center := θ
            halfWidth := Real.pi/5
            positive := by positivity
            atMostPi := by linarith [Real.pi_pos]
            inside := fun φ hφ => hθ _ (five_arc_in_radial_disk o θ hφ) },rfl⟩

end SquaresInCircles
