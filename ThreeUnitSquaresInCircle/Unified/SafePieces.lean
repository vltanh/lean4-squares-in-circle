import ThreeUnitSquaresInCircle.Unified.Support
import ThreeUnitSquaresInCircle.Unified.AngularMeasure

/-! # A common measurable decomposition for the four- and five-square proofs -/

noncomputable section
namespace ThreeUnitSquaresInCircle.Unified
open Set MeasureTheory
open scoped BigOperators

/-- Only an origin-containing square is extended. We use the INTERIOR of the
extension, which is measurable without any projection-measurability argument. -/
def safePiece {ι : Type*} (S : ι → UnitSquare) (o : Point) (i : ι) : Set Point :=
  if openSquare (S i) o then interior (RadialExtension (S i) o)
  else {p | openSquare (S i) p}

lemma safePiece_measurable {ι : Type*} (S : ι → UnitSquare) (o : Point) (i : ι) :
    MeasurableSet (safePiece S o i) := by
  unfold safePiece
  split_ifs
  · exact isOpen_interior.measurableSet
  · exact openSquare_measurable _

lemma safePieces_pairwise {ι : Type*} (S : ι → UnitSquare) (o : Point)
    (hd : Nonoverlapping S) (hP : ∀ i, CenterBody Octagon (S i) o) :
    Pairwise (fun i j => Disjoint (safePiece S o i) (safePiece S o j)) := by
  intro i j hij
  by_cases hi : openSquare (S i) o
  · have hj : ¬ openSquare (S j) o := fun hj => hd i j hij o ⟨hi,hj⟩
    simp only [safePiece, if_pos hi, if_neg hj]
    exact (radial_extension_safe (S i) (S j) o (hd i j hij) (hP j)).mono_left
      interior_subset
  · by_cases hj : openSquare (S j) o
    · simp only [safePiece, if_neg hi, if_pos hj]
      exact ((radial_extension_safe (S j) (S i) o (hd j i hij.symm) (hP i)).mono_left
        interior_subset).symm
    · simp only [safePiece, if_neg hi, if_neg hj]
      rw [Set.disjoint_left]
      exact fun p hp hq => hd i j hij p ⟨hp,hq⟩

lemma safePieces_budget {ι : Type*} [Fintype ι] (S : ι → UnitSquare) (o : Point)
    (hd : Nonoverlapping S) (hP : ∀ i, CenterBody Octagon (S i) o) (r : ℝ) :
    (∑ i, angularMass (safePiece S o i) o r) ≤ 2*Real.pi :=
  angular_budget _ (safePiece_measurable S o) (safePieces_pairwise S o hd hP) o r

lemma centers_ne_of_strict_octagon {ι : Type*} [Nontrivial ι]
    (S : ι → UnitSquare) (o : Point) (hd : Nonoverlapping S)
    (hP : ∀ i, CenterBody OctagonStrict (S i) o) (i : ι) : (S i).center ≠ o := by
  obtain ⟨j,hji⟩ := exists_ne i
  intro hc
  exact centered_impossible (S i) (S j) o (hd i j hji.symm) (hP j) hc

end ThreeUnitSquaresInCircle.Unified
