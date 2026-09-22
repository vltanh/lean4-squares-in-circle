import ThreeUnitSquaresInCircle.Unified.AngularBudget

/-!
# Square-local circle charts

A chart records a phase and a possible reversal of angular orientation.
It is an equality of actual point-membership predicates, not a statement
about an angular shadow.  The two absolute center coordinates can then be
sorted without changing the planar square.
-/
noncomputable section
open Set
namespace ThreeUnitSquaresInCircle.Unified

lemma frame_angle (S : UnitSquare) :
    ∃ t : ℝ, Real.cos t=S.cosine ∧ Real.sin t=S.sine := by
  have hc0 : -1 ≤ S.cosine := by nlinarith [S.unit,sq_nonneg S.sine]
  have hc1 : S.cosine ≤ 1 := by nlinarith [S.unit,sq_nonneg S.sine]
  let t := Real.arccos S.cosine
  have hcos : Real.cos t=S.cosine := Real.cos_arccos hc0 hc1
  have hsin0 : 0 ≤ Real.sin t := Real.sin_nonneg_of_nonneg_of_le_pi
    (Real.arccos_nonneg _) (Real.arccos_le_pi _)
  have hu := Real.sin_sq_add_cos_sq t
  rw [hcos] at hu
  by_cases hs : 0 ≤ S.sine
  · exact ⟨t,hcos,by nlinarith [S.unit]⟩
  · refine ⟨-t,by simpa using hcos,?_⟩
    rw [Real.sin_neg]
    nlinarith [S.unit]

lemma local_circle (S : UnitSquare) (o : Point) (r θ t : ℝ)
    (hc : Real.cos θ=S.cosine) (hs : Real.sin θ=S.sine) :
    localX S (circlePoint o r ((θ:Direction)+(t:Direction))) =
      r*Real.cos t-frameX S (sub S.center o) ∧
    localY S (circlePoint o r ((θ:Direction)+(t:Direction))) =
      r*Real.sin t-frameY S (sub S.center o) := by
  have hx : localX S (circlePoint o r ((θ:Direction)+(t:Direction))) =
      r*Real.cos t*(S.cosine^2+S.sine^2)-frameX S (sub S.center o) := by
    simp only [circlePoint,localX,Real.Angle.cos_add,Real.Angle.sin_add,
      Real.Angle.cos_coe,Real.Angle.sin_coe,hc,hs,frameX,sub]
    ring
  have hy : localY S (circlePoint o r ((θ:Direction)+(t:Direction))) =
      r*Real.sin t*(S.cosine^2+S.sine^2)-frameY S (sub S.center o) := by
    simp only [circlePoint,localY,Real.Angle.cos_add,Real.Angle.sin_add,
      Real.Angle.cos_coe,Real.Angle.sin_coe,hc,hs,frameY,sub]
    ring
  exact ⟨by simpa only [S.unit,mul_one] using hx,
    by simpa only [S.unit,mul_one] using hy⟩

lemma local_circle_shift (S : UnitSquare) (o : Point) (r θ t m : ℝ)
    (hc : Real.cos θ=S.cosine) (hs : Real.sin θ=S.sine) :
    localX S (sub (circlePoint o r ((θ:Direction)+(t:Direction)))
      (scale m (sub S.center o))) = r*Real.cos t-(1+m)*frameX S (sub S.center o) ∧
    localY S (sub (circlePoint o r ((θ:Direction)+(t:Direction)))
      (scale m (sub S.center o))) = r*Real.sin t-(1+m)*frameY S (sub S.center o) := by
  rcases local_circle S o r θ t hc hs with ⟨hx,hy⟩
  have ex (p : Point) : localX S (sub p (scale m (sub S.center o))) =
      localX S p-m*frameX S (sub S.center o) := by
    dsimp [localX,sub,scale,frameX]; ring
  have ey (p : Point) : localY S (sub p (scale m (sub S.center o))) =
      localY S p-m*frameY S (sub S.center o) := by
    dsimp [localY,sub,scale,frameY]; ring
  rw [ex,ey,hx,hy]
  constructor <;> ring

def chartAngle (phase : Direction) (rev : Bool) (t : ℝ) : Direction :=
  phase+((if rev then -t else t : ℝ) : Direction)

structure SquareChart (S : UnitSquare) (o : Point) where
  a : ℝ
  b : ℝ
  phase : Direction
  reversed : Bool
  coordinates : (a=alpha S o ∧ b=beta S o) ∨ (a=beta S o ∧ b=alpha S o)
  shifted_membership : ∀ r t m, openSquare S
    (sub (circlePoint o r (chartAngle phase reversed t)) (scale m (sub S.center o))) ↔
    |r*Real.cos t-(1+m)*a| < 1/2 ∧ |r*Real.sin t-(1+m)*b| < 1/2


lemma SquareChart.membership {S : UnitSquare} {o : Point} (C : SquareChart S o)
    (r t : ℝ) : openSquare S (circlePoint o r (chartAngle C.phase C.reversed t)) ↔
      |r*Real.cos t-C.a| < 1/2 ∧ |r*Real.sin t-C.b| < 1/2 := by
  simpa [sub,scale] using C.shifted_membership r t 0

lemma SquareChart.ray_mem {S : UnitSquare} {o : Point} (C : SquareChart S o)
    {r t : ℝ} (h : ∃ m : ℝ, 0 ≤ m ∧
      |r*Real.cos t-(1+m)*C.a| < 1/2 ∧ |r*Real.sin t-(1+m)*C.b| < 1/2) :
    circlePoint o r (chartAngle C.phase C.reversed t) ∈ openRay S o := by
  obtain ⟨m,hm,hx,hy⟩ := h
  refine ⟨m,hm,_,(C.shifted_membership r t m).mpr ⟨hx,hy⟩,?_⟩
  apply Prod.ext <;> dsimp [add,sub,scale] <;> ring

lemma SquareChart.nonneg {S : UnitSquare} {o : Point} (C : SquareChart S o) :
    0 ≤ C.a ∧ 0 ≤ C.b := by
  rcases C.coordinates with ⟨ha,hb⟩ | ⟨ha,hb⟩ <;>
    rw [ha,hb] <;> exact ⟨abs_nonneg _,abs_nonneg _⟩

lemma square_chart (S : UnitSquare) (o : Point) : Nonempty (SquareChart S o) := by
  obtain ⟨θ,hcos,hsin⟩ := frame_angle S
  have hX : |frameX S (sub S.center o)|=alpha S o := abs_frame_centerX S o
  have hY : |frameY S (sub S.center o)|=beta S o := abs_frame_centerY S o
  have hc := local_circle_shift S o
  generalize frameX S (sub S.center o) = X at hc hX
  generalize frameY S (sub S.center o) = Y at hc hY
  by_cases hx : 0 ≤ X <;> by_cases hy : 0 ≤ Y
  · refine ⟨⟨|X|,|Y|,(θ:Direction),false,Or.inl ⟨hX,hY⟩,?_⟩⟩
    intro r t m
    rcases hc r θ t m hcos hsin with ⟨h₁,h₂⟩
    simp only [chartAngle,Bool.false_eq_true,ite_false,openSquare,h₁,h₂,
      abs_of_nonneg hx,abs_of_nonneg hy]
  · refine ⟨⟨|X|,|Y|,(θ:Direction),true,Or.inl ⟨hX,hY⟩,?_⟩⟩
    intro r t m
    rcases hc r θ (-t) m hcos hsin with ⟨h₁,h₂⟩
    have hneg : r*Real.sin (-t)-(1+m)*Y = -(r*Real.sin t-(1+m)*(-Y)) := by
      rw [Real.sin_neg]; ring
    simp only [chartAngle,ite_true,openSquare,h₁,h₂,Real.cos_neg,hneg,abs_neg,
      abs_of_nonneg hx,abs_of_neg (lt_of_not_ge hy)]
  · refine ⟨⟨|X|,|Y|,((θ+Real.pi:ℝ):Direction),true,Or.inl ⟨hX,hY⟩,?_⟩⟩
    intro r t m
    have hang : chartAngle ((θ+Real.pi:ℝ):Direction) true t =
        (θ:Direction)+((Real.pi-t:ℝ):Direction) := by
      simp only [chartAngle,ite_true,Real.Angle.coe_add,Real.Angle.coe_sub,
        Real.Angle.coe_neg]; abel
    rcases hc r θ (Real.pi-t) m hcos hsin with ⟨h₁,h₂⟩
    have hneg : r*Real.cos (Real.pi-t)-(1+m)*X = -(r*Real.cos t-(1+m)*(-X)) := by
      rw [Real.cos_pi_sub]; ring
    rw [hang]
    simp only [openSquare,h₁,h₂,hneg,Real.sin_pi_sub,abs_neg,
      abs_of_neg (lt_of_not_ge hx),abs_of_nonneg hy]
  · refine ⟨⟨|X|,|Y|,((θ+Real.pi:ℝ):Direction),false,Or.inl ⟨hX,hY⟩,?_⟩⟩
    intro r t m
    have hang : chartAngle ((θ+Real.pi:ℝ):Direction) false t =
        (θ:Direction)+((Real.pi+t:ℝ):Direction) := by
      simp only [chartAngle,Bool.false_eq_true,ite_false,Real.Angle.coe_add]; abel
    rcases hc r θ (Real.pi+t) m hcos hsin with ⟨h₁,h₂⟩
    have hneg₁ : r*Real.cos (Real.pi+t)-(1+m)*X = -(r*Real.cos t-(1+m)*(-X)) := by
      rw [Real.cos_add]; simp; ring
    have hneg₂ : r*Real.sin (Real.pi+t)-(1+m)*Y = -(r*Real.sin t-(1+m)*(-Y)) := by
      rw [Real.sin_add]; simp; ring
    rw [hang]
    simp only [openSquare,h₁,h₂,hneg₁,hneg₂,abs_neg,
      abs_of_neg (lt_of_not_ge hx),abs_of_neg (lt_of_not_ge hy)]

def SquareChart.swap {S : UnitSquare} {o : Point} (C : SquareChart S o) : SquareChart S o where
  a := C.b
  b := C.a
  phase := chartAngle C.phase C.reversed (Real.pi/2)
  reversed := !C.reversed
  coordinates := by
    rcases C.coordinates with ⟨ha,hb⟩ | ⟨ha,hb⟩
    · exact Or.inr ⟨hb,ha⟩
    · exact Or.inl ⟨hb,ha⟩
  shifted_membership := by
    intro r t m
    have he : chartAngle (chartAngle C.phase C.reversed (Real.pi/2)) (!C.reversed) t =
        chartAngle C.phase C.reversed (Real.pi/2-t) := by
      cases C.reversed <;>
        simp only [chartAngle,Bool.not_false,Bool.not_true,Bool.false_eq_true,
          ite_false,ite_true,Real.Angle.coe_sub,Real.Angle.coe_neg] <;> abel
    rw [he,C.shifted_membership,Real.cos_pi_div_two_sub,Real.sin_pi_div_two_sub]
    exact and_comm

lemma sorted_square_chart (S : UnitSquare) (o : Point) :
    ∃ C : SquareChart S o, C.b ≤ C.a := by
  obtain ⟨C⟩ := square_chart S o
  by_cases h : C.b ≤ C.a
  · exact ⟨C,h⟩
  · exact ⟨C.swap,le_of_lt (lt_of_not_ge h)⟩

lemma SquareChart.origin {S : UnitSquare} {o : Point} (C : SquareChart S o) :
    openSquare S o ↔ C.a < 1/2 ∧ C.b < 1/2 := by
  have hh := C.membership 0 0
  simpa only [circlePoint,zero_mul,add_zero,zero_sub,abs_neg,
    abs_of_nonneg C.nonneg.1,abs_of_nonneg C.nonneg.2] using hh

lemma SquareChart.exterior {S : UnitSquare} {o : Point} (C : SquareChart S o)
    (hsort : C.b ≤ C.a) (hout : ¬ openSquare S o) : 1/2 ≤ C.a := by
  by_contra hn
  exact hout (C.origin.mpr ⟨lt_of_not_ge hn,lt_of_le_of_lt hsort (lt_of_not_ge hn)⟩)

/-- Build an arc from a canonical coordinate interval, with either orientation. -/
lemma SquareChart.arc {S : UnitSquare} {o : Point} (C : SquareChart S o)
    (r l u : ℝ) (hlu : l < u) (hlen : u-l ≤ 2*Real.pi)
    (hmem : ∀ t ∈ Ioo l u,
      |r*Real.cos t-C.a| < 1/2 ∧ |r*Real.sin t-C.b| < 1/2) :
    ∃ A : OpenArc o r {p | openSquare S p}, A.halfWidth=(u-l)/2 := by
  cases hrev : C.reversed
  · let A := arcOfInterval o r {p | openSquare S p} C.phase l u hlu hlen
      (fun t ht => by
        have hm := (C.membership r t).mpr (hmem t ht)
        simpa only [chartAngle,hrev,Bool.false_eq_true,ite_false,Set.mem_ofPred_eq] using hm)
    refine ⟨A,rfl⟩
  · let A := arcOfInterval o r {p | openSquare S p} C.phase (-u) (-l)
      (by linarith) (by linarith) (fun t ht => by
        have hm := (C.membership r (-t)).mpr
          (hmem (-t) ⟨by linarith [ht.2],by linarith [ht.1]⟩)
        simpa only [chartAngle,hrev,ite_true,neg_neg,Set.mem_ofPred_eq] using hm)
    refine ⟨A,?_⟩
    dsimp [A,arcOfInterval]; ring


lemma arcFromChartInterval (o : Point) (r : ℝ) (U : Set Point)
    (phase : Direction) (rev : Bool) (l u : ℝ) (hlu : l < u) (hlen : u-l ≤ 2*Real.pi)
    (hmem : ∀ t ∈ Ioo l u, circlePoint o r (chartAngle phase rev t) ∈ U) :
    ∃ A : OpenArc o r U, A.halfWidth=(u-l)/2 := by
  cases rev
  · exact ⟨arcOfInterval o r U phase l u hlu hlen
      (fun t ht => by simpa [chartAngle] using hmem t ht),rfl⟩
  · let A := arcOfInterval o r U phase (-u) (-l) (by linarith) (by linarith)
      (fun t ht => by
        have hm := hmem (-t) ⟨by linarith [ht.2],by linarith [ht.1]⟩
        simpa only [chartAngle,ite_true,neg_neg] using hm)
    exact ⟨A,by dsimp [A,arcOfInterval]; ring⟩

end ThreeUnitSquaresInCircle.Unified
