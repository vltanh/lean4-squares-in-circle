import ThreeUnitSquaresInCircle.Unified.FiveScalar

/-! The five-square containing case: a safely swept square contains a disk,
which in turn contains a 72-degree arc. -/
noncomputable section
open Set
namespace ThreeUnitSquaresInCircle.Unified

lemma normSq_pos_of_ne {v : Point} (hv : v ≠ (0,0)) : 0 < normSq v := by
  have hn := normSq_nonneg v
  by_contra hh
  apply hv
  apply Prod.ext <;> dsimp [normSq] at * <;>
    nlinarith [sq_nonneg v.1,sq_nonneg v.2]

lemma small_disk_in_openSquare (S : UnitSquare) {p : Point}
    (hp : normSq (sub p S.center) < 1/4) : openSquare S p := by
  have hu := frame_norm S (sub p S.center)
  change (localX S p)^2+(localY S p)^2=normSq (sub p S.center) at hu
  exact ⟨abs_lt.mpr ⟨by nlinarith [sq_nonneg (localY S p)],
                         by nlinarith [sq_nonneg (localY S p)]⟩,
         abs_lt.mpr ⟨by nlinarith [sq_nonneg (localX S p)],
                         by nlinarith [sq_nonneg (localX S p)]⟩⟩

lemma containing_center_norm (S : UnitSquare) {o : Point} (ho : openSquare S o) :
    normSq (sub S.center o) < 1/2 := by
  have hu := frame_norm S (sub S.center o)
  rw [frame_centerX,frame_centerY] at hu
  rcases abs_lt.mp ho.1 with ⟨hx0,hx1⟩
  rcases abs_lt.mp ho.2 with ⟨hy0,hy1⟩
  have hx : (localX S o)^2 < 1/4 := by nlinarith
  have hy : (localY S o)^2 < 1/4 := by nlinarith
  nlinarith

lemma vector_direction {v : Point} (hv : v ≠ (0,0)) :
    ∃ (θ : Direction) (l : ℝ), 0 < l ∧ l^2=normSq v ∧
      v=(l*θ.cos,l*θ.sin) := by
  let l := Real.sqrt (normSq v)
  have hl0 : 0 < l := Real.sqrt_pos.mpr (normSq_pos_of_ne hv)
  have hl2 : l^2=normSq v := Real.sq_sqrt (normSq_nonneg v)
  let F : UnitSquare :=
    { center := (0,0)
      cosine := v.1/l
      sine := v.2/l
      unit := by
        field_simp [ne_of_gt hl0]
        simpa only [normSq] using hl2.symm }
  obtain ⟨t,htc,hts⟩ := frame_angle F
  refine ⟨(t:Direction),l,hl0,hl2,?_⟩
  apply Prod.ext
  · simp only [Real.Angle.cos_coe,htc,F]
    field_simp [ne_of_gt hl0]
  · simp only [Real.Angle.sin_coe,hts,F]
    field_simp [ne_of_gt hl0]

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
  have ht : Real.cos t^2+Real.sin t^2=1 := by nlinarith [Real.sin_sq_add_cos_sq t]
  rw [ht]
  ring

def halfDiagonal : ℝ := Real.sqrt 2/2

lemma halfDiagonal_pos : 0 < halfDiagonal := by unfold halfDiagonal; positivity
lemma halfDiagonal_sq : halfDiagonal^2=1/2 := by
  have hh := Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)
  dsimp [halfDiagonal]
  nlinarith
lemma halfDiagonal_gt_707 : (707:ℝ)/1000 < halfDiagonal := by
  nlinarith [halfDiagonal_sq,halfDiagonal_pos]

/-- The ray sweep contains a radius-1/2 disk at distance `1/sqrt(2)` from `o`. -/
lemma containing_ray_disk (S : UnitSquare) (o : Point)
    (ho : openSquare S o) (hne : S.center ≠ o) :
    ∃ θ : Direction, ∀ p : Point,
      normSq (sub p (circlePoint o halfDiagonal θ)) < 1/4 → p ∈ openRay S o := by
  have hv : sub S.center o ≠ (0,0) := by
    intro hh
    apply hne
    have h₁ := congrArg Prod.fst hh
    have h₂ := congrArg Prod.snd hh
    apply Prod.ext <;> dsimp [sub] at * <;> linarith
  obtain ⟨θ,l,hl0,hl2,hvθ⟩ := vector_direction hv
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
  nlinarith

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

end ThreeUnitSquaresInCircle.Unified
