import ThreeUnitSquaresInCircle.Unified.Basic

/-!
# Actual occupied arcs, not angular shadows

Angles are measured on one half-open fundamental interval of length 2π.
Using OPEN squares makes the occupied sets genuinely disjoint. No theorem that
closed-square boundary intersections have measure zero is needed for the budget.
-/

noncomputable section
namespace ThreeUnitSquaresInCircle.Unified

open Set MeasureTheory
open scoped BigOperators ENNReal

def circlePoint (o : Point) (r t : ℝ) : Point :=
  (o.1 + r*Real.cos t, o.2 + r*Real.sin t)

def angleWindow : Set ℝ := Ioc (-Real.pi) Real.pi

def angularSet (A : Set Point) (o : Point) (r : ℝ) : Set ℝ :=
  angleWindow ∩ circlePoint o r ⁻¹' A

def angularMass (A : Set Point) (o : Point) (r : ℝ) : ℝ :=
  (volume (angularSet A o r)).toReal

def occupied (S : UnitSquare) (o : Point) (r : ℝ) : ℝ :=
  angularMass {p | openSquare S p} o r

theorem circlePoint_continuous (o : Point) (r : ℝ) : Continuous (circlePoint o r) := by
  unfold circlePoint
  fun_prop

theorem circlePoint_norm (o : Point) (r t : ℝ) :
    normSq (sub (circlePoint o r t) o) = r^2 := by
  have hu := Real.sin_sq_add_cos_sq t
  dsimp [normSq, sub, circlePoint]
  nlinarith [congrArg (fun z : ℝ => r^2*z) hu]

theorem angularSet_measurable {A : Set Point} (hA : MeasurableSet A)
    (o : Point) (r : ℝ) : MeasurableSet (angularSet A o r) :=
  measurableSet_Ioc.inter (hA.preimage (circlePoint_continuous o r).measurable)

theorem angularSet_finite (A : Set Point) (o : Point) (r : ℝ) :
    volume (angularSet A o r) ≠ ∞ := by
  apply ne_of_lt
  exact lt_of_le_of_lt (measure_mono (inter_subset_left)) (by
    simp [angleWindow])

theorem angularMass_nonneg (A : Set Point) (o : Point) (r : ℝ) :
    0 ≤ angularMass A o r := ENNReal.toReal_nonneg

theorem angularMass_mono {A B : Set Point} (h : A ⊆ B) (o : Point) (r : ℝ) :
    angularMass A o r ≤ angularMass B o r := by
  apply ENNReal.toReal_mono (angularSet_finite B o r)
  exact measure_mono (inter_subset_inter_right _ (preimage_mono h))

theorem angularMass_univ (o : Point) (r : ℝ) :
    angularMass univ o r = 2*Real.pi := by
  simp [angularMass, angularSet, angleWindow, Real.volume_Ioc,
    show Real.pi - -Real.pi = 2*Real.pi by ring,
    ENNReal.toReal_ofReal (show 0 ≤ 2*Real.pi by positivity)]

theorem openSquare_measurable (S : UnitSquare) : MeasurableSet {p | openSquare S p} := by
  have hx : Continuous fun p => |localX S p| := by
    unfold localX
    fun_prop
  have hy : Continuous fun p => |localY S p| := by
    unfold localY
    fun_prop
  exact ((isOpen_lt hx continuous_const).inter
    (isOpen_lt hy continuous_const)).measurableSet

/-- A finite boundary-measure budget, independent of the shape of the pieces. -/
theorem angular_budget {ι : Type*} [Fintype ι]
    (A : ι → Set Point) (hA : ∀ i, MeasurableSet (A i))
    (hd : Pairwise (fun i j => Disjoint (A i) (A j))) (o : Point) (r : ℝ) :
    (∑ i, angularMass (A i) o r) ≤ 2*Real.pi := by
  classical
  have hd' : Pairwise (fun i j => Disjoint (angularSet (A i) o r)
      (angularSet (A j) o r)) := by
    intro i j hij
    rw [Set.disjoint_left]
    intro t ht hu
    exact Set.disjoint_left.mp (hd hij) ht.2 hu.2
  have hm : ∀ i, MeasurableSet (angularSet (A i) o r) :=
    fun i => angularSet_measurable (hA i) o r
  have he : (∑ i, volume (angularSet (A i) o r)) =
      volume (⋃ i, angularSet (A i) o r) := by
    rw [measure_iUnion hd' hm, tsum_fintype]
  have hbound : (∑ i, volume (angularSet (A i) o r)) ≤
      ENNReal.ofReal (2*Real.pi) := by
    rw [he]
    calc
      _ ≤ volume angleWindow := measure_mono (iUnion_subset fun i => inter_subset_left)
      _ = _ := by
        simp only [angleWindow, Real.volume_Ioc]
        congr 1
        ring
  have hr := ENNReal.toReal_mono ENNReal.ofReal_ne_top hbound
  rw [ENNReal.toReal_sum (fun i _ => angularSet_finite (A i) o r)] at hr
  simpa only [angularMass, ENNReal.toReal_ofReal (show 0 ≤ 2*Real.pi by positivity)] using hr

/-- The master packing inequality. It is for arbitrary finite cardinality. -/
theorem occupied_budget {ι : Type*} [Fintype ι] {S : ι → UnitSquare}
    (hd : Nonoverlapping S) (o : Point) (r : ℝ) :
    (∑ i, occupied (S i) o r) ≤ 2*Real.pi := by
  apply angular_budget _ (fun i => openSquare_measurable (S i))
  intro i j hij
  rw [Set.disjoint_left]
  exact fun p hp hq => hd i j hij p ⟨hp, hq⟩

/-- Strict finite budgets cannot fit in 2π. -/
theorem no_uniform_strict_budget {n : ℕ} (hn : 0 < n)
    (f : Fin n → ℝ) (hb : (∑ i, f i) ≤ 2*Real.pi)
    (hf : ∀ i, 2*Real.pi/n < f i) : False := by
  haveI : Nonempty (Fin n) := ⟨⟨0,hn⟩⟩
  have hs : (∑ _i : Fin n, 2*Real.pi/n) < ∑ i, f i :=
    Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty (fun i _ => hf i)
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hs
  have he : (n : ℝ) * (2*Real.pi/n) = 2*Real.pi := by field_simp
  rw [he] at hs
  linarith

end ThreeUnitSquaresInCircle.Unified
