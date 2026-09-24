import SquaresInCircles.Seven.Uniqueness.CentralStripRigidity
import SquaresInCircles.Seven.SeparatingAxes

/-! Pullback and quarter-turn identities for geometric equality statements. -/
noncomputable section
namespace SquaresInCircles.Seven.Equality

def pullSquare (S : UnitSquare) (o : Point) (φ : Direction) : UnitSquare where
  center := ((frameEquiv o φ).symm S.center)
  cosine := φ.cos*S.cosine+φ.sin*S.sine
  sine := φ.cos*S.sine-φ.sin*S.cosine
  unit := by
    calc
      _=(φ.cos^2+φ.sin^2)*(S.cosine^2+S.sine^2) := by ring
      _=1 := by rw [Real.Angle.cos_sq_add_sin_sq,S.unit]; ring

lemma pullSquare_local (S : UnitSquare) (o : Point) (φ : Direction) (p : Point) :
    localX (pullSquare S o φ) p=localX S (pointInDirection o φ p.1 p.2) ∧
    localY (pullSquare S o φ) p=localY S (pointInDirection o φ p.1 p.2) := by
  have hu : 1-φ.cos^2-φ.sin^2=0 := by nlinarith [Real.Angle.cos_sq_add_sin_sq φ]
  constructor
  · calc
      _=localX S (pointInDirection o φ p.1 p.2)+(1-φ.cos^2-φ.sin^2)*
          (S.cosine*(S.center.1-o.1)+S.sine*(S.center.2-o.2)) := by
        dsimp [pullSquare,frameEquiv,localX,pointInDirection]
        ring
      _=_ := by rw [hu]; ring
  · calc
      _=localY S (pointInDirection o φ p.1 p.2)+(1-φ.cos^2-φ.sin^2)*
          (-S.sine*(S.center.1-o.1)+S.cosine*(S.center.2-o.2)) := by
        dsimp [pullSquare,frameEquiv,localY,pointInDirection]
        ring
      _=_ := by rw [hu]; ring

lemma pullSquare_open (S : UnitSquare) (o : Point) (φ : Direction) (p : Point) :
    openSquare (pullSquare S o φ) p ↔ openSquare S (pointInDirection o φ p.1 p.2) := by
  rw [openSquare,openSquare,(pullSquare_local S o φ p).1,(pullSquare_local S o φ p).2]

lemma pullSquare_closed (S : UnitSquare) (o : Point) (φ : Direction) (p : Point) :
    closedSquare (pullSquare S o φ) p ↔ closedSquare S (pointInDirection o φ p.1 p.2) := by
  rw [closedSquare,closedSquare,(pullSquare_local S o φ p).1,(pullSquare_local S o φ p).2]

lemma pullSquare_contained (S : UnitSquare) (o : Point) (φ : Direction) (R : ℝ)
    (h : ∀p,closedSquare S p → inDisk o R p) :
    ∀p,closedSquare (pullSquare S o φ) p → inDisk (0,0) R p := by
  intro p hp
  have hh := h _ ((pullSquare_closed S o φ p).mp hp)
  change normSq (sub (pointInDirection o φ p.1 p.2) o)≤R^2 at hh
  rw [pointInDirection_norm] at hh
  simpa [inDisk,normSq,sub] using hh

lemma represents_quarter {S : UnitSquare} {o : Point} {φ : Direction}
    (k : Fin 4) (a b : ℝ)
    (h : Represents S o (φ+((cardinalAngle k : ℝ):Direction)) (a,b)) :
    Represents S o φ (SAT.qturns k.val (a,b)) := by
  intro x y
  rw [pointInDirection_transition o φ (φ+((cardinalAngle k : ℝ):Direction)) x y]
  rw [show φ+((cardinalAngle k : ℝ):Direction)-φ=((cardinalAngle k : ℝ):Direction) by abel]
  rw [Real.Angle.cos_coe,Real.Angle.sin_coe,h]
  fin_cases k
  · simp [cardinalAngle,OpenRect,SAT.qturns]
  · have hx : -x-b= -(x+b) := by ring
    simp [cardinalAngle,OpenRect,SAT.qturns,SAT.qturn,hx,abs_neg,sub_neg_eq_add,and_comm]
  · have hx : -x-a= -(x+a) := by ring
    have hy : -y-b= -(y+b) := by ring
    simp [cardinalAngle,OpenRect,SAT.qturns,SAT.qturn,hx,hy,abs_neg,sub_neg_eq_add]
  · have hx : -y-a= -(y+a) := by ring
    have hang : (3 : ℝ)*Real.pi/2=Real.pi+Real.pi/2 := by ring
    simp [cardinalAngle,OpenRect,SAT.qturns,SAT.qturn,hang,
      Real.cos_add,Real.sin_add,hx,abs_neg,sub_neg_eq_add,and_comm]

/-- A square containing o and disjoint from the four side squares has one
remaining coordinate in the common frame. This does not use disk containment. -/
theorem central_represents (S : UnitSquare) (T : Fin 4 → UnitSquare)
    (o : Point) (φ : Direction) (ho : openSquare S o)
    (hT : ∀i,Represents (T i) o φ (sideCenter i))
    (hd : ∀i,∀p,¬(openSquare S p∧openSquare (T i) p)) :
    ∃ z : ℝ, |z|<1/2 ∧ Represents S o φ (0,z) := by
  let U := pullSquare S o φ
  have h0 : openSquare U (0,0) := by
    rw [pullSquare_open]
    simpa [pointInDirection] using ho
  have hwall : ∀i : Fin 4,∀p,¬(openSquare U p∧openSquare (axisSquare (sideCenter i)) p) := by
    intro i p hp
    apply hd i (pointInDirection o φ p.1 p.2)
    refine ⟨(pullSquare_open S o φ p).mp hp.1,?_⟩
    apply (hT i p.1 p.2).mpr
    simpa [openSquare,axisSquare,OpenRect,localX,localY] using hp.2
  have hs := containing_strip U h0 hwall
  obtain ⟨hx,haxis,hm⟩ := containing_strip_rigid U h0 hs
  refine ⟨U.center.2,?_,?_⟩
  · have hh := (hm (0,0)).mp h0
    simpa [OpenRect,abs_neg] using hh.2
  · intro x y
    rw [←pullSquare_open S o φ (x,y)]
    exact hm (x,y)

lemma aligned_vertical_separation {S T : UnitSquare} {o : Point} {φ : Direction}
    {y z : ℝ} (hS : Represents S o φ (0,y)) (hT : Represents T o φ (0,z))
    (hd : ∀p,¬(openSquare S p∧openSquare T p)) : 1≤|z-y| := by
  by_contra hn
  have hab : |z-y|<1 := lt_of_not_ge hn
  have hpm := abs_lt.mp hab
  let p := pointInDirection o φ 0 ((y+z)/2)
  apply hd p
  constructor
  · apply (hS _ _).mpr
    dsimp [OpenRect]
    constructor <;> apply abs_lt.mpr <;> constructor <;> linarith
  · apply (hT _ _).mpr
    dsimp [OpenRect]
    constructor <;> apply abs_lt.mpr <;> constructor <;> linarith

end SquaresInCircles.Seven.Equality
