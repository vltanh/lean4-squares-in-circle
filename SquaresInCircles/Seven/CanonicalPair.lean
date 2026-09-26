import SquaresInCircles.Seven.Contacts
import SquaresInCircles.Seven.SeparatingAxes

/-!
# The canonical pair

Two squares in the frame of the first one, the second turned by the relative
phase. If their open squares are disjoint, the separating-axis theorem gives a
nonpositive support sum on one of the four axes, of the pair or of the pair
seen from the second square.
-/
noncomputable section
namespace SquaresInCircles.Seven

def relativePhase (a u A v g : ℝ) (s t : TransverseSign) : ℝ :=
  g+s.coe*label a u-t.coe*label A v

def centerDX (a u A v g : ℝ) (s t : TransverseSign) : ℝ :=
  A*Real.cos (relativePhase a u A v g s t)-t.coe*v*Real.sin (relativePhase a u A v g s t)-a

def centerDY (a u A v g : ℝ) (s t : TransverseSign) : ℝ :=
  A*Real.sin (relativePhase a u A v g s t)+t.coe*v*Real.cos (relativePhase a u A v g s t)-s.coe*u

def pairWidth (d : ℝ) : ℝ := (1+|Real.cos d|+|Real.sin d|)/2

lemma pair_support_axis_values (a u A v g : ℝ) (s t : TransverseSign) :
    pairSupport a u A v s t 0 g=pairWidth (relativePhase a u A v g s t)-centerDX a u A v g s t ∧
    pairSupport a u A v s t 1 g=pairWidth (relativePhase a u A v g s t)-centerDY a u A v g s t ∧
    pairSupport a u A v s t 2 g=pairWidth (relativePhase a u A v g s t)+centerDX a u A v g s t ∧
    pairSupport a u A v s t 3 g=pairWidth (relativePhase a u A v g s t)+centerDY a u A v g s t := by
  let d := relativePhase a u A v g s t
  have he (c : ℝ) : c-g-s.coe*label a u+t.coe*label A v=c-d := by
    dsimp [d,relativePhase]
    ring
  rw [pairSupport_zero,pairSupport_one,pairSupport_two,pairSupport_three,he,he,he,he,
    support_three_half_sub,support_two_pi_sub,
    show 5*Real.pi/2-d=(Real.pi/2-d)+2*Real.pi by ring]
  simp only [support,Real.cos_pi_sub,Real.sin_pi_sub,Real.cos_add_two_pi,Real.sin_add_two_pi,
    Real.cos_pi_div_two_sub,Real.sin_pi_div_two_sub,abs_neg,pairWidth,centerDX,centerDY,d]
  refine ⟨?_,?_,?_,?_⟩ <;> ring

lemma reverse_reflected_phase (a u A v g : ℝ) (s t : TransverseSign) :
    relativePhase A v a u g t.flip s.flip=relativePhase a u A v g s t := by
  dsimp [relativePhase]
  rw [TransverseSign.coe_flip,TransverseSign.coe_flip]
  ring

def rotatedState (a b d : ℝ) : UnitSquare where
  center := (a*Real.cos d-b*Real.sin d,a*Real.sin d+b*Real.cos d)
  cosine := Real.cos d
  sine := Real.sin d
  unit := Real.cos_sq_add_sin_sq d

lemma rotatedState_local (a b d : ℝ) (p : Point) :
    localX (rotatedState a b d) p=Real.cos d*p.1+Real.sin d*p.2-a ∧
    localY (rotatedState a b d) p= -Real.sin d*p.1+Real.cos d*p.2-b := by
  have hu := Real.sin_sq_add_cos_sq d
  constructor
  · dsimp [localX,rotatedState]
    linear_combination -a*hu
  · dsimp [localY,rotatedState]
    linear_combination -b*hu

namespace Equality

def CanonicalDisjoint (a u A v g : ℝ) (s t : TransverseSign) : Prop :=
  ∀ x y : ℝ, ¬ ((|x-a| < 1/2 ∧ |y-s.coe*u| < 1/2) ∧
    (|Real.cos (relativePhase a u A v g s t)*x+
       Real.sin (relativePhase a u A v g s t)*y-A| < 1/2 ∧
     |-Real.sin (relativePhase a u A v g s t)*x+
       Real.cos (relativePhase a u A v g s t)*y-t.coe*v| < 1/2))

private lemma first_axes_of_support {a u A v g : ℝ} (s t : TransverseSign)
    (h : ∀ k, 0 < pairSupport a u A v s t k g) :
    |centerDX a u A v g s t| < pairWidth (relativePhase a u A v g s t) ∧
    |centerDY a u A v g s t| < pairWidth (relativePhase a u A v g s t) := by
  have he := pair_support_axis_values a u A v g s t
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  have h3 := h 3
  rw [he.1] at h0
  rw [he.2.1] at h1
  rw [he.2.2.1] at h2
  rw [he.2.2.2] at h3
  exact ⟨abs_lt.mpr ⟨by linarith,by linarith⟩,
    abs_lt.mpr ⟨by linarith,by linarith⟩⟩

lemma reverse_center_coordinates (a u A v g : ℝ) (s t : TransverseSign) :
    Real.cos (relativePhase a u A v g s t)*centerDX a u A v g s t+
      Real.sin (relativePhase a u A v g s t)*centerDY a u A v g s t =
        -centerDX A v a u g t.flip s.flip ∧
    -Real.sin (relativePhase a u A v g s t)*centerDX a u A v g s t+
      Real.cos (relativePhase a u A v g s t)*centerDY a u A v g s t =
        centerDY A v a u g t.flip s.flip := by
  let d := relativePhase a u A v g s t
  have hu := Real.sin_sq_add_cos_sq d
  constructor <;> dsimp [centerDX,centerDY] <;>
    rw [reverse_reflected_phase] <;> simp only [TransverseSign.coe_flip]
  · change Real.cos d*(A*Real.cos d-t.coe*v*Real.sin d-a)+
      Real.sin d*(A*Real.sin d+t.coe*v*Real.cos d-s.coe*u) = _
    linear_combination A*hu
  · change -Real.sin d*(A*Real.cos d-t.coe*v*Real.sin d-a)+
      Real.cos d*(A*Real.sin d+t.coe*v*Real.cos d-s.coe*u) = _
    linear_combination t.coe*v*hu

/-- A disjoint canonical pair has a nonpositive support in one of its frames. -/
lemma canonical_has_separator {a u A v g : ℝ} (s t : TransverseSign)
    (hd : CanonicalDisjoint a u A v g s t) :
    (∃ k, pairSupport a u A v s t k g ≤ 0) ∨
    (∃ k, pairSupport A v a u t.flip s.flip k g ≤ 0) := by
  by_contra hn
  have hf : ∀ k, 0 < pairSupport a u A v s t k g := by
    intro k
    by_contra hk
    exact hn (Or.inl ⟨k,le_of_not_gt hk⟩)
  have hr : ∀ k, 0 < pairSupport A v a u t.flip s.flip k g := by
    intro k
    by_contra hk
    exact hn (Or.inr ⟨k,le_of_not_gt hk⟩)
  have hfirst := first_axes_of_support s t hf
  have hsecond := first_axes_of_support t.flip s.flip hr
  rw [reverse_reflected_phase] at hsecond
  let d := relativePhase a u A v g s t
  let S := rotatedState a (s.coe*u) 0
  let T := rotatedState A (t.coe*v) d
  have hdisj : ∀ p, ¬ (openSquare S p ∧ openSquare T p) := by
    intro p hp
    have hS := rotatedState_local a (s.coe*u) 0 p
    have hT := rotatedState_local A (t.coe*v) d p
    apply hd p.1 p.2
    constructor
    · have hh := hp.1
      change |localX S p| < 1/2 ∧ |localY S p| < 1/2 at hh
      dsimp [S] at hh
      rw [hS.1,hS.2] at hh
      simpa using hh
    · have hh := hp.2
      change |localX T p| < 1/2 ∧ |localY T p| < 1/2 at hh
      dsimp [T] at hh
      rw [hT.1,hT.2] at hh
      exact hh
  have hc : relativeC S T = Real.cos d := by
    norm_num [S,T,rotatedState,relativeC]
  have hs : relativeS S T = Real.sin d := by
    norm_num [S,T,rotatedState,relativeS]
  have hw : SAT.threshold S T = pairWidth d := by rw [SAT.threshold,hc,hs]; rfl
  have hx : frameX S (sub T.center S.center) = centerDX a u A v g s t := by
    norm_num [S,T,rotatedState,frameX,sub,centerDX,d]
  have hy : frameY S (sub T.center S.center) = centerDY a u A v g s t := by
    norm_num [S,T,rotatedState,frameY,sub,centerDY,d]
  have hT := relative_normal S T (sub T.center S.center)
  rw [hc,hs,hx,hy] at hT
  have he := reverse_center_coordinates a u A v g s t
  have hsep := SAT.separating_axes S T hdisj
  rw [hw,hx,hy,hT.1,hT.2,he.1,he.2,abs_neg] at hsep
  rcases hsep with hsep | hsep | hsep | hsep
  · exact (not_le_of_gt hfirst.1) hsep
  · exact (not_le_of_gt hfirst.2) hsep
  · exact (not_le_of_gt hsecond.1) hsep
  · exact (not_le_of_gt hsecond.2) hsep

end Equality
end SquaresInCircles.Seven
