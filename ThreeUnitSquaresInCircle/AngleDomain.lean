import ThreeUnitSquaresInCircle.Geometry

/-!
# Exact covers of the normalized angle triangle

Coordinates here are `(a/pi,b/pi)`. Membership is exhibited by nonnegative
barycentric coordinates, rather than inferred from equality of areas.
These lemmas do not prove that a packing admits normalized angles.
Status: compiles against Lean 4.34.0 / mathlib v4.34.0.
-/
noncomputable section
namespace ThreeUnitSquaresInCircle.AngleDomain

def Domain (a b : ℝ) : Prop := 0 ≤ a ∧ 2*a ≤ b ∧ 2*b-a ≤ 1/2

def O : Point := (0,0)
def V : Point := (0,1/4)
def W : Point := (1/6,1/3)
def P : Point := (0,1/8)
def Z : Point := (1/12,1/6)

def InTriangle (p q r x : Point) : Prop :=
  ∃ u v w : ℝ, 0 ≤ u ∧ 0 ≤ v ∧ 0 ≤ w ∧ u+v+w=1 ∧
    x.1 = u*p.1 + v*q.1 + w*r.1 ∧
    x.2 = u*p.2 + v*q.2 + w*r.2

lemma in_full {a b : ℝ} (h : Domain a b) : InTriangle O V W (a,b) := by
  rcases h with ⟨ha,hb,hc⟩
  refine ⟨1-4*b+2*a, 4*b-8*a, 6*a,
    by linarith, by linarith, by linarith, by ring, ?_, ?_⟩
  · dsimp [O,V,W]; ring
  · dsimp [O,V,W]; ring

lemma in_OVZ {a b : ℝ} (h : Domain a b) (hcut : 4*a+4*b ≤ 1) :
    InTriangle O V Z (a,b) := by
  rcases h with ⟨ha,hb,hc⟩
  refine ⟨1-4*b-4*a, 4*b-8*a, 12*a,
    by linarith, by linarith, by linarith, by ring, ?_, ?_⟩
  · dsimp [O,V,Z]; ring
  · dsimp [O,V,Z]; ring

lemma in_VWZ {a b : ℝ} (h : Domain a b) (hcut : 1 ≤ 4*a+4*b) :
    InTriangle V W Z (a,b) := by
  rcases h with ⟨ha,hb,hc⟩
  refine ⟨4*b-8*a, 4*a+4*b-1, 4*a-8*b+2,
    by linarith, by linarith, by linarith, by ring, ?_, ?_⟩
  · dsimp [V,W,Z]; ring
  · dsimp [V,W,Z]; ring

lemma cover_G {a b : ℝ} (h : Domain a b) :
    InTriangle O V Z (a,b) ∨ InTriangle V W Z (a,b) := by
  by_cases hcut : 4*a+4*b ≤ 1
  · exact Or.inl (in_OVZ h hcut)
  · exact Or.inr (in_VWZ h (by linarith))

lemma in_OPW {a b : ℝ} (h : Domain a b) (hcut : 8*b-10*a ≤ 1) :
    InTriangle O P W (a,b) := by
  rcases h with ⟨ha,hb,hc⟩
  refine ⟨1-8*b+10*a, 8*b-16*a, 6*a,
    by linarith, by linarith, by linarith, by ring, ?_, ?_⟩
  · dsimp [O,P,W]; ring
  · dsimp [O,P,W]; ring

lemma in_PVW {a b : ℝ} (h : Domain a b) (hcut : 1 ≤ 8*b-10*a) :
    InTriangle P V W (a,b) := by
  rcases h with ⟨ha,hb,hc⟩
  refine ⟨2-8*b+4*a, 8*b-10*a-1, 6*a,
    by linarith, by linarith, by linarith, by ring, ?_, ?_⟩
  · dsimp [P,V,W]; ring
  · dsimp [P,V,W]; ring

lemma cover_H {a b : ℝ} (h : Domain a b) :
    InTriangle O P W (a,b) ∨ InTriangle P V W (a,b) := by
  by_cases hcut : 8*b-10*a ≤ 1
  · exact Or.inl (in_OPW h hcut)
  · exact Or.inr (in_PVW h (by linarith))

lemma in_OPZ {a b : ℝ} (h : Domain a b) (hcut : 8*b-4*a ≤ 1) :
    InTriangle O P Z (a,b) := by
  rcases h with ⟨ha,hb,hc⟩
  refine ⟨1-8*b+4*a, 8*b-16*a, 12*a,
    by linarith, by linarith, by linarith, by ring, ?_, ?_⟩
  · dsimp [O,P,Z]; ring
  · dsimp [O,P,Z]; ring

lemma in_PWZ {a b : ℝ} (h : Domain a b)
    (hcut0 : 1 ≤ 8*b-4*a) (hcut1 : 8*b-10*a ≤ 1) :
    InTriangle P W Z (a,b) := by
  rcases h with ⟨ha,hb,hc⟩
  refine ⟨8*b-16*a, 8*b-4*a-1, 20*a-16*b+2,
    by linarith, by linarith, by linarith, by ring, ?_, ?_⟩
  · dsimp [P,W,Z]; ring
  · dsimp [P,W,Z]; ring

/-- The second and third triangles triangulate the supplementary quadrilateral. -/
lemma cover_J_special {a b : ℝ} (h : Domain a b) :
    InTriangle O P Z (a,b) ∨
    InTriangle P V W (a,b) ∨ InTriangle P W Z (a,b) := by
  by_cases hcut0 : 8*b-4*a ≤ 1
  · exact Or.inl (in_OPZ h hcut0)
  · by_cases hcut1 : 8*b-10*a ≤ 1
    · exact Or.inr (Or.inr (in_PWZ h (by linarith) hcut1))
    · exact Or.inr (Or.inl (in_PVW h (by linarith)))

end ThreeUnitSquaresInCircle.AngleDomain
