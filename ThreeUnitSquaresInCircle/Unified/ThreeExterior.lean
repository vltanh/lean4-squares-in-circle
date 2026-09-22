import ThreeUnitSquaresInCircle.Unified.RectangleArcs

/-!
# Three-square exterior arcs

This is the part of the independent three-square arc proof supplied in this
extension. It does not invoke the original certificate theorem. It proves
that a hypothetical strict contact-polygon packing must have the tested point
inside one square. The other alternative is developed in `ThreeContaining.lean`;
`ThreeArc.lean` is the independent, standalone optimality entry point.
-/
noncomputable section
open Set
namespace ThreeUnitSquaresInCircle.Unified

def auxThree : ℝ := 3/8

lemma arcsin_lt_sixth {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1/2) :
    Real.arcsin u < Real.pi/6 := by
  apply (Real.arcsin_lt_iff_lt_sin
    (show u ∈ Icc (-1:ℝ) 1 by constructor <;> linarith)
    (show Real.pi/6 ∈ Icc (-(Real.pi/2)) (Real.pi/2) by constructor <;> linarith [Real.pi_pos])).mpr
  simpa only [Real.sin_pi_div_six] using hu1

lemma three_truncated_gap {u v : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1/2)
    (hv : 1/2+u < v) :
    2*Real.pi/3 < Real.arccos u+Real.arcsin v := by
  have hA := arcsin_lt_sixth hu0 hu1
  have hA0 := Real.arcsin_nonneg.mpr hu0
  have hsin : Real.sin (Real.arcsin u+Real.pi/6) < v := by
    rw [Real.sin_add,Real.sin_arcsin (by linarith) (by linarith),Real.sin_pi_div_six]
    have hp := mul_nonneg hu0 (sub_nonneg.mpr (Real.cos_le_one (Real.pi/6)))
    nlinarith [Real.cos_le_one (Real.arcsin u)]
  have hh := (Real.lt_arcsin_iff_sin_lt'
    (show Real.arcsin u+Real.pi/6 ∈ Ico (-(Real.pi/2)) (Real.pi/2) by
      constructor <;> linarith [Real.pi_pos])).mpr hsin
  dsimp [Real.arccos]
  linarith

lemma three_cap_interval {a b : ℝ} (ha : 1/2 ≤ a) (hb : 0 ≤ b)
    (hpoly : P3Strict a b) :
    ∃ l u : ℝ, 2*Real.pi/3 < u-l ∧ u-l ≤ 2*Real.pi ∧
      ∀ t ∈ Ioo l u, |auxThree*Real.cos t-a| < 1/2 ∧
        |auxThree*Real.sin t-b| < 1/2 := by
  let x := (a-1/2)/auxThree
  let v := (1/2-b)/auxThree
  have hx0 : 0 ≤ x := by dsimp [x,auxThree]; linarith
  have hx1 : x < 1/2 := by dsimp [x,auxThree]; linarith [hpoly.2.2.1]
  have hv : 1/2+x < v := by dsimp [x,v,auxThree]; linarith [hpoly.1]
  let A := Real.arccos x
  let l := max (-A) (-Real.arcsin v)
  have hA : Real.pi/3 < A := by
    have hh := arcsin_lt_sixth hx0 hx1
    dsimp [A,Real.arccos]; linarith
  have hAp : A ≤ Real.pi/2 := by
    have hh := Real.arcsin_nonneg.mpr hx0
    dsimp [A,Real.arccos]; linarith
  have hB := three_truncated_gap hx0 hx1 hv
  have hgap : 2*Real.pi/3 < A-l := by
    have hh : l < A-2*Real.pi/3 := by
      dsimp [l]
      exact max_lt (by linarith) (by dsimp [A] at *; linarith)
    linarith
  refine ⟨l,A,hgap,?_,?_⟩
  · have hh : -A ≤ l := le_max_left _ _
    linarith [Real.pi_pos]
  · intro t ht
    have ht0 : -A < t := (le_max_left _ _).trans_lt ht.1
    have ht1 : t < A := ht.2
    have htdom : t ∈ Ioo (-(Real.pi/2)) (Real.pi/2) :=
      ⟨by linarith,by linarith⟩
    have hcos : x < Real.cos t := by
      have hh := Real.cos_lt_cos_of_nonneg_of_le_pi (abs_nonneg t)
        (show A ≤ Real.pi by linarith [Real.pi_pos]) (abs_lt.mpr ⟨ht0,ht1⟩)
      rw [Real.cos_arccos (by linarith [hx0]) (by linarith [hx1])] at hh
      simpa only [Real.cos_abs] using hh
    have hts : Real.arcsin (-v) < t := by
      rw [Real.arcsin_neg]
      exact (le_max_right _ _).trans_lt ht.1
    have hsin : -v < Real.sin t :=
      (Real.arcsin_lt_iff_lt_sin' ⟨htdom.1,htdom.2.le⟩).mp hts
    have hcos1 := Real.cos_le_one t
    have hsin1 := Real.sin_le_one t
    dsimp [x,v,auxThree] at hcos hsin ⊢
    exact ⟨abs_lt.mpr ⟨by linarith,by linarith⟩,
      abs_lt.mpr ⟨by linarith,by linarith⟩⟩

lemma three_exterior_arc (S : UnitSquare) (o : Point)
    (hp : P3Strict (alpha S o) (beta S o)) (hout : ¬ openSquare S o) :
    ∃ A : OpenArc o auxThree {p | openSquare S p}, Real.pi/3 < A.halfWidth := by
  obtain ⟨C,hsort⟩ := sorted_square_chart S o
  have hC : P3Strict C.a C.b := by
    rcases C.coordinates with ⟨ha,hb⟩ | ⟨ha,hb⟩
    · simpa only [ha,hb] using hp
    · rw [ha,hb]
      exact ⟨by linarith [hp.2.1],by linarith [hp.1],
        by linarith [hp.2.2.2],by linarith [hp.2.2.1]⟩
  obtain ⟨l,u,hlen,hwide,hmem⟩ := three_cap_interval (C.exterior hsort hout) C.nonneg.2 hC
  obtain ⟨A,hA⟩ := C.arc auxThree l u (by linarith [Real.pi_pos]) hwide hmem
  exact ⟨A,by rw [hA]; linarith⟩

/-- The exterior-only case of the three-square polygon theorem is complete. -/
theorem three_exterior_reduction (S : Fin 3 → UnitSquare) (o : Point)
    (hd : InteriorDisjoint S) (hp : ∀ i, P3Strict (alpha (S i) o) (beta (S i) o)) :
    ∃ i, openSquare (S i) o := by
  classical
  by_contra hn
  push_neg at hn
  choose A hA using (fun i => three_exterior_arc (S i) o (hp i) (hn i))
  have hregions : Pairwise (fun i j => Disjoint {p | openSquare (S i) p} {p | openSquare (S j) p}) := by
    intro i j hij
    rw [Set.disjoint_left]
    exact fun p hpi hpj => hd i j hij p ⟨hpi,hpj⟩
  exact uniform_arc_excess (n := 3) (by decide) A hregions (fun i => (hA i).le) ⟨0,hA 0⟩

/-- The strict projection margins used in the remaining two-exterior-square contradiction. -/
lemma three_projection_margins {C S : ℝ} (hC0 : 1/2 ≤ C) (hC1 : C < 3/5)
    (hS0 : 4/5 < S) (hS1 : S ≤ 1) :
    (11/16)*(1+C)+S/16 < (1+C+S)/2 ∧
    (11/16)*S+(1+C)/16 < (1+C+S)/2 := by
  constructor <;> linarith

end ThreeUnitSquaresInCircle.Unified
