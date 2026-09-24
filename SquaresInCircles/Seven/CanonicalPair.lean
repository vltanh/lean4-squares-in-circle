import SquaresInCircles.Seven.AllGaps
import SquaresInCircles.Seven.SeparatingAxes
import SquaresInCircles.Common.Constructions

/-!
# The canonical pair

Positive support sums on the two axes of the first square, and, for the pair
seen from the second square, on its two axes, give a point in both open
squares by the separating-axis theorem.
-/
noncomputable section
open Set
namespace SquaresInCircles.Seven

namespace TransverseSign

def flip : TransverseSign → TransverseSign
  | .positive => .negative
  | .negative => .positive

lemma coe_flip (s : TransverseSign) : s.flip.coe= -s.coe := by cases s <;> norm_num [flip,coe]
end TransverseSign

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
  have he (k : Fin 4) : cardinalAngle k+Real.pi-g-s.coe*label a u+t.coe*label A v=
      cardinalAngle k+Real.pi-d := by dsimp [d,relativePhase]; ring
  have h0 : support A (t.coe*v) (Real.pi-d)=
      -A*Real.cos d+t.coe*v*Real.sin d+(|Real.cos d|+|Real.sin d|)/2 := by
    simp only [support,Real.cos_pi_sub,Real.sin_pi_sub,abs_neg]
    ring
  have h1 : support A (t.coe*v) (3*Real.pi/2-d)=
      -A*Real.sin d-t.coe*v*Real.cos d+(|Real.sin d|+|Real.cos d|)/2 :=
    support_three_half_sub A (t.coe*v) d
  have h2 : support A (t.coe*v) (2*Real.pi-d)=
      A*Real.cos d-t.coe*v*Real.sin d+(|Real.cos d|+|Real.sin d|)/2 :=
    support_two_pi_sub A (t.coe*v) d
  have h3 : support A (t.coe*v) (5*Real.pi/2-d)=
      A*Real.sin d+t.coe*v*Real.cos d+(|Real.sin d|+|Real.cos d|)/2 := by
    have hang : 5*Real.pi/2-d=2*Real.pi+(Real.pi/2-d) := by ring
    rw [hang]
    simp only [support,Real.cos_add,Real.sin_add,Real.cos_two_pi,Real.sin_two_pi,
      one_mul,zero_mul,sub_zero,zero_add,Real.cos_pi_div_two_sub,Real.sin_pi_div_two_sub]
  constructor
  · rw [pairSupport,he]
    norm_num only [cardinalAngle,Fin.val_zero,Nat.cast_zero,zero_mul,zero_div,zero_add,support_zero]
    rw [h0]
    dsimp [pairWidth,centerDX,d]
    ring
  constructor
  · rw [pairSupport,he]
    have hk : cardinalAngle (1:Fin 4)=Real.pi/2 := by norm_num [cardinalAngle]
    rw [hk,support_half_pi,show Real.pi/2+Real.pi-d=3*Real.pi/2-d by ring,h1]
    dsimp [pairWidth,centerDY,d]
    ring
  constructor
  · rw [pairSupport,he]
    have hk : cardinalAngle (2:Fin 4)=Real.pi := by norm_num [cardinalAngle]
    rw [hk,support_pi,show Real.pi+Real.pi-d=2*Real.pi-d by ring,h2]
    dsimp [pairWidth,centerDX,d]
    ring
  · rw [pairSupport,he]
    have hk : cardinalAngle (3:Fin 4)=3*Real.pi/2 := by norm_num [cardinalAngle]
    rw [hk,support_three_half_pi,show 3*Real.pi/2+Real.pi-d=5*Real.pi/2-d by ring,h3]
    dsimp [pairWidth,centerDY,d]
    ring

lemma first_two_axes_inside {a u A v g : ℝ} (s t : TransverseSign)
    (h : StrictlyAdmissible a u) (h' : StrictlyAdmissible A v)
    (hg : 0≤g ∧ g≤gap) :
    |centerDX a u A v g s t|<pairWidth (relativePhase a u A v g s t) ∧
    |centerDY a u A v g s t|<pairWidth (relativePhase a u A v g s t) := by
  have h0 := all_gap_support_pos s t 0 h h' hg
  have h1 := all_gap_support_pos s t 1 h h' hg
  have h2 := all_gap_support_pos s t 2 h h' hg
  have h3 := all_gap_support_pos s t 3 h h' hg
  have he := pair_support_axis_values a u A v g s t
  rw [he.1] at h0
  rw [he.2.1] at h1
  rw [he.2.2.1] at h2
  rw [he.2.2.2] at h3
  exact ⟨abs_lt.mpr ⟨by linarith,by linarith⟩,abs_lt.mpr ⟨by linarith,by linarith⟩⟩

lemma reverse_reflected_phase (a u A v g : ℝ) (s t : TransverseSign) :
    relativePhase A v a u g t.flip s.flip=relativePhase a u A v g s t := by
  dsimp [relativePhase]
  rw [TransverseSign.coe_flip,TransverseSign.coe_flip]
  ring

lemma all_four_axes_inside {a u A v g : ℝ} (s t : TransverseSign)
    (h : StrictlyAdmissible a u) (h' : StrictlyAdmissible A v)
    (hg : 0≤g ∧ g≤gap) :
    SAT.AxisInside (Real.cos (relativePhase a u A v g s t))
      (Real.sin (relativePhase a u A v g s t))
      (centerDX a u A v g s t,centerDY a u A v g s t) := by
  have hfirst := first_two_axes_inside s t h h' hg
  have hsecond := first_two_axes_inside t.flip s.flip h' h hg
  rw [reverse_reflected_phase] at hsecond
  let d := relativePhase a u A v g s t
  have hu := Real.sin_sq_add_cos_sq d
  have hx : Real.cos d*centerDX a u A v g s t+Real.sin d*centerDY a u A v g s t =
      -centerDX A v a u g t.flip s.flip := by
    dsimp [centerDX,centerDY]
    rw [reverse_reflected_phase]
    simp only [TransverseSign.coe_flip]
    change Real.cos d*(A*Real.cos d-t.coe*v*Real.sin d-a)+
      Real.sin d*(A*Real.sin d+t.coe*v*Real.cos d-s.coe*u)=_
    nlinarith [congrArg (fun x : ℝ => A*x) hu]
  have hy : -Real.sin d*centerDX a u A v g s t+Real.cos d*centerDY a u A v g s t =
      centerDY A v a u g t.flip s.flip := by
    dsimp [centerDX,centerDY]
    rw [reverse_reflected_phase]
    simp only [TransverseSign.coe_flip]
    change -Real.sin d*(A*Real.cos d-t.coe*v*Real.sin d-a)+
      Real.cos d*(A*Real.sin d+t.coe*v*Real.cos d-s.coe*u)=_
    nlinarith [congrArg (fun x : ℝ => t.coe*v*x) hu]
  change |centerDX a u A v g s t|<pairWidth d ∧
    |centerDY a u A v g s t|<pairWidth d ∧
    |Real.cos d*centerDX a u A v g s t+Real.sin d*centerDY a u A v g s t|<pairWidth d ∧
    |-Real.sin d*centerDX a u A v g s t+Real.cos d*centerDY a u A v g s t|<pairWidth d
  rw [hx,hy,abs_neg]
  exact ⟨hfirst.1,hfirst.2,hsecond.1,hsecond.2⟩

def rotatedState (a b d : ℝ) : UnitSquare where
  center := (a*Real.cos d-b*Real.sin d,a*Real.sin d+b*Real.cos d)
  cosine := Real.cos d
  sine := Real.sin d
  unit := by nlinarith [Real.sin_sq_add_cos_sq d]

lemma rotatedState_local (a b d : ℝ) (p : Point) :
    localX (rotatedState a b d) p=Real.cos d*p.1+Real.sin d*p.2-a ∧
    localY (rotatedState a b d) p= -Real.sin d*p.1+Real.cos d*p.2-b := by
  have hu := Real.sin_sq_add_cos_sq d
  constructor
  · dsimp [localX,rotatedState]
    nlinarith [congrArg (fun x : ℝ => a*x) hu]
  · dsimp [localY,rotatedState]
    nlinarith [congrArg (fun x : ℝ => b*x) hu]

/-- The open squares of a canonical pair with a gap in `[0, π/3]` meet. -/
theorem canonical_pair_overlap {a u A v g : ℝ} (s t : TransverseSign)
    (h : StrictlyAdmissible a u) (h' : StrictlyAdmissible A v)
    (hg : 0≤g ∧ g≤gap) :
    ∃ x y : ℝ,
      (|x-a|<1/2 ∧ |y-s.coe*u|<1/2) ∧
      (|Real.cos (relativePhase a u A v g s t)*x+
        Real.sin (relativePhase a u A v g s t)*y-A|<1/2 ∧
       |-Real.sin (relativePhase a u A v g s t)*x+
        Real.cos (relativePhase a u A v g s t)*y-t.coe*v|<1/2) := by
  let d := relativePhase a u A v g s t
  let S := rotatedState a (s.coe*u) 0
  let T := rotatedState A (t.coe*v) d
  have hi := all_four_axes_inside s t h h' hg
  have hrc : SAT.relativeCos S T=Real.cos d := by norm_num [SAT.relativeCos,S,T,rotatedState]
  have hrs : SAT.relativeSin S T=Real.sin d := by norm_num [SAT.relativeSin,S,T,rotatedState]
  have hwidth : SAT.threshold S T=pairWidth d := by rw [SAT.threshold,hrc,hrs]; rfl
  have hdx : frameX S (sub T.center S.center)=centerDX a u A v g s t := by
    norm_num [frameX,S,T,rotatedState,sub,centerDX,d]
  have hdy : frameY S (sub T.center S.center)=centerDY a u A v g s t := by
    norm_num [frameY,S,T,rotatedState,sub,centerDY,d]
  have htx := SAT.relative_frameX S T (sub T.center S.center)
  have hty := SAT.relative_frameY S T (sub T.center S.center)
  rw [hrc,hrs,hdx,hdy] at htx hty
  have hex : ∃p,openSquare S p ∧ openSquare T p := by
    by_contra hn
    have hd : ∀p,¬(openSquare S p∧openSquare T p) := by simpa only [not_exists] using hn
    have hsat := SAT.separating_axes S T hd
    rw [hwidth,hdx,hdy,←htx,←hty] at hsat
    change |centerDX a u A v g s t|<pairWidth d ∧
      |centerDY a u A v g s t|<pairWidth d ∧
      |Real.cos d*centerDX a u A v g s t+Real.sin d*centerDY a u A v g s t|<pairWidth d ∧
      |-Real.sin d*centerDX a u A v g s t+Real.cos d*centerDY a u A v g s t|<pairWidth d at hi
    rcases hsat with hx | hy | hx | hy
    · exact (not_le_of_gt hi.1) hx
    · exact (not_le_of_gt hi.2.1) hy
    · exact (not_le_of_gt hi.2.2.1) hx
    · exact (not_le_of_gt hi.2.2.2) hy
  obtain ⟨p,hS,hT⟩ := hex
  have hSl := rotatedState_local a (s.coe*u) 0 p
  have hTl := rotatedState_local A (t.coe*v) d p
  change |localX S p|<1/2 ∧ |localY S p|<1/2 at hS
  change |localX T p|<1/2 ∧ |localY T p|<1/2 at hT
  dsimp [S] at hS
  dsimp [T] at hT
  rw [hSl.1,hSl.2] at hS
  rw [hTl.1,hTl.2] at hT
  refine ⟨p.1,p.2,?_,hT⟩
  simpa only [Real.cos_zero,Real.sin_zero,one_mul,zero_mul,zero_add,add_zero,neg_zero] using hS

end SquaresInCircles.Seven
