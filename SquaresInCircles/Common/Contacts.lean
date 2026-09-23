import SquaresInCircles.Common.NormalForm

/-! Rigidity of two unit squares at center distance one.  The supporting
functional comes from the already compiled separation theorem. -/
noncomputable section
namespace SquaresInCircles

def relativeC (S T : UnitSquare) : ℝ := S.cosine*T.cosine+S.sine*T.sine
def relativeS (S T : UnitSquare) : ℝ := -S.sine*T.cosine+S.cosine*T.sine

def SameAxes (S T : UnitSquare) : Prop := relativeC S T=0 ∨ relativeS S T=0

lemma relative_unit (S T : UnitSquare) : (relativeC S T)^2+(relativeS S T)^2=1 := by
  calc
    _ = (S.cosine^2+S.sine^2)*(T.cosine^2+T.sine^2) := by
      dsimp [relativeC,relativeS]; ring
    _ = 1 := by rw [S.unit,T.unit]; ring

lemma relative_normal (S T : UnitSquare) (n : Point) :
    frameX T n=relativeC S T*frameX S n+relativeS S T*frameY S n ∧
    frameY T n= -relativeS S T*frameX S n+relativeC S T*frameY S n := by
  constructor
  · calc
      _ = (S.cosine^2+S.sine^2)*frameX T n := by rw [S.unit]; ring
      _ = _ := by dsimp [frameX,frameY,relativeC,relativeS]; ring
  · calc
      _ = (S.cosine^2+S.sine^2)*frameY T n := by rw [S.unit]; ring
      _ = _ := by dsimp [frameX,frameY,relativeC,relativeS]; ring

lemma same_axes_from_normal (S T : UnitSquare) {n : Point} (hn : n ≠ (0,0))
    (hS : frameX S n*frameY S n=0) (hT : frameX T n*frameY T n=0) : SameAxes S T := by
  have hpos := frame_abs_sum_pos S hn
  have he := relative_normal S T n
  rcases mul_eq_zero.mp hS with hx | hy
  · have hy : frameY S n ≠ 0 := by intro hy; simp [hx,hy] at hpos
    rcases mul_eq_zero.mp hT with ht | ht
    · have hh : relativeS S T*frameY S n=0 := by rw [hx,ht] at he; simpa using he.1.symm
      exact Or.inr ((mul_eq_zero.mp hh).resolve_right hy)
    · have hh : relativeC S T*frameY S n=0 := by rw [hx,ht] at he; simpa using he.2.symm
      exact Or.inl ((mul_eq_zero.mp hh).resolve_right hy)
  · have hx : frameX S n ≠ 0 := by intro hx; simp [hx,hy] at hpos
    rcases mul_eq_zero.mp hT with ht | ht
    · have hh : relativeC S T*frameX S n=0 := by rw [hy,ht] at he; simpa using he.1.symm
      exact Or.inl ((mul_eq_zero.mp hh).resolve_right hx)
    · have hh : -relativeS S T*frameX S n=0 := by rw [hy,ht] at he; simpa using he.2.symm
      exact Or.inr (neg_eq_zero.mp ((mul_eq_zero.mp hh).resolve_right hx))

lemma cardinal_box {c s X Y : ℝ} (hu : c^2+s^2=1) (hz : c=0 ∨ s=0) :
    (|c*X+s*Y| < 1/2 ∧ |-s*X+c*Y| < 1/2) ↔ (|X| < 1/2 ∧ |Y| < 1/2) := by
  rcases hz with rfl | rfl
  · rcases le_total 0 s with hs | hs
    · have he : s=1 := by nlinarith
      simp [he,and_comm,abs_neg]
    · have he : s= -1 := by nlinarith
      simp [he,and_comm,abs_neg]
  · rcases le_total 0 c with hc | hc
    · have he : c=1 := by nlinarith
      simp [he]
    · have he : c= -1 := by nlinarith
      simp [he,abs_neg]

lemma same_axes_represents (S T : UnitSquare) (o : Point) (φ : Direction)
    (hc : φ.cos=S.cosine) (hs : φ.sin=S.sine) (haxes : SameAxes S T) :
    Represents T o φ (frameX S (sub T.center o),frameY S (sub T.center o)) := by
  intro x y
  have heX : localX T (pointInDirection o φ x y)=
      relativeC S T*(x-frameX S (sub T.center o))+
      relativeS S T*(y-frameY S (sub T.center o)) := by
    have hu := S.unit
    dsimp [localX,pointInDirection,relativeC,relativeS,frameX,frameY,sub]
    rw [hc,hs]
    nlinarith only [congrArg (fun z : ℝ => z*T.cosine*(T.center.1-o.1)) hu,
      congrArg (fun z : ℝ => z*T.sine*(T.center.2-o.2)) hu]
  have heY : localY T (pointInDirection o φ x y)=
      -relativeS S T*(x-frameX S (sub T.center o))+
      relativeC S T*(y-frameY S (sub T.center o)) := by
    have hu := S.unit
    dsimp [localY,pointInDirection,relativeC,relativeS,frameX,frameY,sub]
    rw [hc,hs]
    nlinarith only [congrArg (fun z : ℝ => z*T.sine*(T.center.1-o.1)) hu,
      congrArg (fun z : ℝ => z*T.cosine*(T.center.2-o.2)) hu]
  simp only [openSquare,heX,heY]
  exact cardinal_box (relative_unit S T) haxes

lemma self_represents (S : UnitSquare) (o : Point) (φ : Direction)
    (hc : φ.cos=S.cosine) (hs : φ.sin=S.sine) :
    Represents S o φ (frameX S (sub S.center o),frameY S (sub S.center o)) := by
  apply same_axes_represents S S o φ hc hs
  right
  dsimp [relativeS]; ring

lemma centers_distance_sq_ge_one (S T : UnitSquare)
    (hd : ∀ p, ¬ (openSquare S p ∧ openSquare T p)) :
    1 ≤ normSq (sub T.center S.center) := by
  by_contra hn
  let m : Point := scale (1/2) (add S.center T.center)
  have heS : normSq (sub m S.center)=normSq (sub T.center S.center)/4 := by
    dsimp [m,scale,add,sub,normSq]; ring
  have heT : normSq (sub m T.center)=normSq (sub T.center S.center)/4 := by
    dsimp [m,scale,add,sub,normSq]; ring
  exact hd m ⟨small_disk_in_openSquare S (by rw [heS]; linarith),
    small_disk_in_openSquare T (by rw [heT]; linarith)⟩

lemma cauchy_sq (u v : Point) : (dot u v)^2 ≤ normSq u*normSq v := by
  have h := sq_nonneg (u.1*v.2-u.2*v.1)
  dsimp [dot,normSq]
  nlinarith

lemma width_lower (S : UnitSquare) (n : Point) :
    Real.sqrt (normSq n) ≤ |frameX S n|+|frameY S n| := by
  have hu := frame_norm S n
  have hr := Real.sq_sqrt (normSq_nonneg n)
  have h0 := Real.sqrt_nonneg (normSq n)
  have hp := mul_nonneg (abs_nonneg (frameX S n)) (abs_nonneg (frameY S n))
  nlinarith [sq_abs (frameX S n),sq_abs (frameY S n),
    abs_nonneg (frameX S n),abs_nonneg (frameY S n)]

/-- Equality of center distance forces parallel axes and a cardinal displacement. -/
lemma unit_contact (S T : UnitSquare)
    (hd : ∀ p, ¬ (openSquare S p ∧ openSquare T p))
    (hunit : normSq (sub T.center S.center)=1) :
    SameAxes S T ∧
      ((frameX S (sub T.center S.center)=1 ∧ frameY S (sub T.center S.center)=0) ∨
       (frameX S (sub T.center S.center)=0 ∧ frameY S (sub T.center S.center)=1) ∨
       (frameX S (sub T.center S.center)= -1 ∧ frameY S (sub T.center S.center)=0) ∨
       (frameX S (sub T.center S.center)=0 ∧ frameY S (sub T.center S.center)= -1)) := by
  obtain ⟨e⟩ := separation_exists S T hd
  let n := e.normal
  let d := sub T.center S.center
  let r := Real.sqrt (normSq n)
  have hr : 0 < r := Real.sqrt_pos.mpr (normSq_pos_of_ne e.nonzero)
  have hr2 : r^2=normSq n := Real.sq_sqrt (normSq_nonneg n)
  have hCS := cauchy_sq n d
  change normSq d=1 at hunit
  rw [hunit] at hCS
  have hdot : dot n d ≤ r := by nlinarith
  have hS := width_lower S n
  have hT := width_lower T n
  have hsep := e.separates
  change width S n+width T n ≤ dot n d at hsep
  dsimp [width] at hsep
  have hSumS : |frameX S n|+|frameY S n|=r := by linarith
  have hSumT : |frameX T n|+|frameY T n|=r := by linarith
  have hDot : dot n d=r := by linarith
  have hprodS : frameX S n*frameY S n=0 := by
    have hu := frame_norm S n
    have ha : |frameX S n| * |frameY S n|=0 := by
      nlinarith [sq_abs (frameX S n),sq_abs (frameY S n)]
    exact abs_eq_zero.mp (by simpa only [abs_mul] using ha)
  have hprodT : frameX T n*frameY T n=0 := by
    have hu := frame_norm T n
    have ha : |frameX T n| * |frameY T n|=0 := by
      nlinarith [sq_abs (frameX T n),sq_abs (frameY T n)]
    exact abs_eq_zero.mp (by simpa only [abs_mul] using ha)
  have hnd : n=scale r d := by
    have hh : (n.1-r*d.1)^2+(n.2-r*d.2)^2=0 := by
      dsimp [normSq,dot] at hr2 hunit hDot
      nlinarith [congrArg (fun z : ℝ => r*z) hDot,
        congrArg (fun z : ℝ => r^2*z) hunit]
    apply Prod.ext <;> dsimp [scale] <;>
      nlinarith [sq_nonneg (n.1-r*d.1),sq_nonneg (n.2-r*d.2)]
  have hx : frameX S n=r*frameX S d := by rw [hnd]; dsimp [frameX,scale]; ring
  have hy : frameY S n=r*frameY S d := by rw [hnd]; dsimp [frameY,scale]; ring
  have hdprod : frameX S d=0 ∨ frameY S d=0 := by
    rcases mul_eq_zero.mp hprodS with hh | hh
    · left
      rw [hx] at hh
      exact (mul_eq_zero.mp hh).resolve_left (ne_of_gt hr)
    · right
      rw [hy] at hh
      exact (mul_eq_zero.mp hh).resolve_left (ne_of_gt hr)
  refine ⟨same_axes_from_normal S T e.nonzero hprodS hprodT,?_⟩
  have hu := frame_norm S d
  rw [hunit] at hu
  rcases hdprod with hx0 | hy0
  · have h1 : frameY S d^2=1 := by rw [hx0] at hu; linarith
    rcases le_total 0 (frameY S d) with hy0 | hy0
    · exact Or.inr (Or.inl ⟨hx0,by nlinarith only [h1,hy0]⟩)
    · exact Or.inr (Or.inr (Or.inr ⟨hx0,by nlinarith only [h1,hy0]⟩))
  · have h1 : frameX S d^2=1 := by rw [hy0] at hu; linarith
    rcases le_total 0 (frameX S d) with hx0 | hx0
    · exact Or.inl ⟨by nlinarith only [h1,hx0],hy0⟩
    · exact Or.inr (Or.inr (Or.inl ⟨by nlinarith only [h1,hx0],hy0⟩))

end SquaresInCircles
