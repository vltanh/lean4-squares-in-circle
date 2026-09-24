import SquaresInCircles.Seven.SectorBounds

/-!
# Capped labels

Where the label is `π/4` the support sums are affine in the state, and the
capped region is a triangle whose vertices are strictly admissible ties. So a
support sum at a capped state is a convex combination of its values at active
states, and nonnegativity and strict positivity both pass over.
-/
noncomputable section
open scoped BigOperators
namespace SquaresInCircles.Seven

def ActiveLabel (a u : ℝ) : Prop := label a u = axial u ∨ label a u = side a u

def capVertex : Fin 3 → Point :=
  ![(Real.pi/5,Real.pi/5),
    ((7-Real.pi/5)/9,Real.pi/5),
    ((7-Real.pi)/5,(7-Real.pi)/5)]

def capDen : ℝ := 7-2*Real.pi

lemma capDen_pos : 0 < capDen := by
  dsimp [capDen]
  linarith [pi_lt_22_over_7]

lemma label_eq_cap_of {a u : ℝ}
    (hA : Real.pi/4 ≤ axial u) (hT : Real.pi/4 ≤ side a u) :
    label a u = Real.pi/4 := by
  exact min_eq_right (le_min hA hT)

lemma cap_constraints {a u : ℝ} (h : Admissible a u)
    (hcap : label a u = Real.pi/4) :
    Real.pi ≤ 5*u ∧ 9*a-4*u ≤ 7-Real.pi := by
  have hA := h.label_le_axial
  have hT := h.label_le_side
  rw [hcap] at hA hT
  dsimp [axial,side] at hA hT
  constructor <;> linarith

lemma capVertex_strict (i : Fin 3) :
    StrictlyAdmissible (capVertex i).1 (capVertex i).2 := by
  have hp0 := pi_lower_157
  have hp1 := pi_lt_22_over_7
  have hr (a u : ℝ) (ha0 : 1/2 ≤ a) (hu0 : 0 ≤ u)
      (hau : u ≤ a) (ha1 : a < 193/250) (hu1 : u < 193/250) :
      StrictlyAdmissible a u := by
    refine ⟨hu0,hau,ha0,?_⟩
    have hA := mul_nonneg (show 0 ≤ 193/250-a by linarith)
      (show 0 ≤ 193/250+a+1 by linarith)
    have hU := mul_nonneg (show 0 ≤ 193/250-u by linarith)
      (show 0 ≤ 193/250+u+1 by linarith)
    dsimp [phi,targetSq]
    nlinarith
  fin_cases i <;> apply hr <;> norm_num [capVertex] <;> linarith

@[simp] lemma capVertex_label (i : Fin 3) :
    label (capVertex i).1 (capVertex i).2 = Real.pi/4 := by
  apply label_eq_cap_of
  · fin_cases i <;> norm_num [capVertex,axial] <;> linarith [pi_lt_22_over_7]
  · fin_cases i <;> norm_num [capVertex,side] <;> linarith [pi_lt_22_over_7]

lemma capVertex_active (i : Fin 3) : ActiveLabel (capVertex i).1 (capVertex i).2 := by
  fin_cases i
  · left
    rw [capVertex_label]
    dsimp [capVertex,axial]
    ring
  · left
    rw [capVertex_label]
    dsimp [capVertex,axial]
    ring
  · right
    rw [capVertex_label]
    dsimp [capVertex,side]
    ring

def capWeights (a u : ℝ) : Fin 3 → ℝ :=
  ![1-9*(a-u)/capDen-(5*u-Real.pi)/capDen,
    9*(a-u)/capDen,(5*u-Real.pi)/capDen]

lemma capWeights_sum (a u : ℝ) : ∑ i, capWeights a u i = 1 := by
  simp [capWeights,Fin.sum_univ_succ]

lemma capWeights_nonneg {a u : ℝ} (h : Admissible a u)
    (hcap : label a u = Real.pi/4) (i : Fin 3) : 0 ≤ capWeights a u i := by
  have hc := cap_constraints h hcap
  have hD := capDen_pos
  fin_cases i
  · have he : capWeights a u 0 = (7-Real.pi-9*a+4*u)/capDen := by
      dsimp [capWeights]
      field_simp [ne_of_gt capDen_pos]
      dsimp [capDen]
      ring
    change 0 ≤ capWeights a u 0
    rw [he]
    exact div_nonneg (by linarith [hc.2]) hD.le
  · dsimp [capWeights]
    exact div_nonneg (by linarith [h.2.1]) hD.le
  · dsimp [capWeights]
    exact div_nonneg (by linarith [hc.1]) hD.le

lemma capWeights_center (a u : ℝ) :
    (∑ i,capWeights a u i*(capVertex i).1) = a ∧
    (∑ i,capWeights a u i*(capVertex i).2) = u := by
  have hD : capDen ≠ 0 := ne_of_gt capDen_pos
  constructor <;>
    simp [capWeights,capVertex,Fin.sum_univ_succ] <;>
    field_simp [hD] <;> dsimp [capDen] <;> ring

lemma capWeights_some_pos {a u : ℝ} (h : Admissible a u)
    (hcap : label a u = Real.pi/4) : ∃ i,0 < capWeights a u i := by
  by_contra hn
  push Not at hn
  have he (i : Fin 3) : capWeights a u i = 0 :=
    le_antisymm (hn i) (capWeights_nonneg h hcap i)
  have hs := capWeights_sum a u
  simp only [he,Finset.sum_const_zero] at hs
  norm_num at hs

lemma support_barycentric (w x y : Fin 3 → ℝ) (hw : ∑ i,w i=1) (c z : ℝ) :
    support (∑ i,w i*x i) (c*∑ i,w i*y i) z =
      ∑ i,w i*support (x i) (c*y i) z := by
  have hconst := congrArg (fun t : ℝ =>
    t*((|Real.cos z|+|Real.sin z|)/2)) hw
  simp only [Fin.sum_univ_three] at hw hconst ⊢
  dsimp [support]
  nlinarith [hconst]

lemma cap_pair_first {a u : ℝ} (hcap : label a u = Real.pi/4)
    (A v : ℝ) (s t : TransverseSign) (k : Fin 4) (g : ℝ) :
    pairSupport a u A v s t k g =
      ∑ i,capWeights a u i *
        pairSupport (capVertex i).1 (capVertex i).2 A v s t k g := by
  have hm := support_barycentric (capWeights a u)
    (fun i => (capVertex i).1) (fun i => (capVertex i).2)
    (capWeights_sum a u) s.coe (cardinalAngle k)
  rw [(capWeights_center a u).1,(capWeights_center a u).2] at hm
  have hc := congrArg (fun w : ℝ => w * support A (t.coe*v)
    (cardinalAngle k+Real.pi-g-s.coe*(Real.pi/4)+t.coe*label A v))
    (capWeights_sum a u)
  simp only [pairSupport,hcap,capVertex_label,Fin.sum_univ_three] at hm hc ⊢
  nlinarith [hm,hc]

lemma cap_pair_second {A v : ℝ} (hcap : label A v = Real.pi/4)
    (a u : ℝ) (s t : TransverseSign) (k : Fin 4) (g : ℝ) :
    pairSupport a u A v s t k g =
      ∑ i,capWeights A v i *
        pairSupport a u (capVertex i).1 (capVertex i).2 s t k g := by
  have hm := support_barycentric (capWeights A v)
    (fun i => (capVertex i).1) (fun i => (capVertex i).2)
    (capWeights_sum A v) t.coe
    (cardinalAngle k+Real.pi-g-s.coe*label a u+t.coe*(Real.pi/4))
  rw [(capWeights_center A v).1,(capWeights_center A v).2] at hm
  have hc := congrArg (fun w : ℝ => w*support a (s.coe*u) (cardinalAngle k))
    (capWeights_sum A v)
  simp only [pairSupport,hcap,capVertex_label,Fin.sum_univ_three] at hm hc ⊢
  nlinarith [hm,hc]

private lemma cap_weighted_pos {a u : ℝ} (h : Admissible a u)
    (hcap : label a u = Real.pi/4) (f : Fin 3 → ℝ) (hf : ∀ i,0 < f i) :
    0 < ∑ i,capWeights a u i*f i := by
  obtain ⟨i,hi⟩ := capWeights_some_pos h hcap
  have hterm := mul_pos hi (hf i)
  apply hterm.trans_le
  exact Finset.single_le_sum
    (fun j _ => mul_nonneg (capWeights_nonneg h hcap j) (hf j).le)
    (Finset.mem_univ i)

/-- The exact support assertion propagated through a capped state. -/
def PairProperty (a u A v : ℝ) (s t : TransverseSign) (k : Fin 4) : Prop :=
  0 ≤ pairSupport a u A v s t k gap ∧
    (StrictlyAdmissible a u → StrictlyAdmissible A v →
      0 < pairSupport a u A v s t k gap)

lemma pairProperty_cap_first {a u A v : ℝ}
    (h : Admissible a u) (hcap : label a u = Real.pi/4)
    (s t : TransverseSign) (k : Fin 4)
    (hv : ∀ i,PairProperty (capVertex i).1 (capVertex i).2 A v s t k) :
    PairProperty a u A v s t k := by
  constructor
  · rw [cap_pair_first hcap]
    exact Finset.sum_nonneg (fun i _ =>
      mul_nonneg (capWeights_nonneg h hcap i) (hv i).1)
  · intro ha hb
    rw [cap_pair_first hcap]
    exact cap_weighted_pos h hcap _
      (fun i => (hv i).2 (capVertex_strict i) hb)

lemma pairProperty_cap_second {a u A v : ℝ}
    (h : Admissible A v) (hcap : label A v = Real.pi/4)
    (s t : TransverseSign) (k : Fin 4)
    (hv : ∀ i,PairProperty a u (capVertex i).1 (capVertex i).2 s t k) :
    PairProperty a u A v s t k := by
  constructor
  · rw [cap_pair_second hcap]
    exact Finset.sum_nonneg (fun i _ =>
      mul_nonneg (capWeights_nonneg h hcap i) (hv i).1)
  · intro ha hb
    rw [cap_pair_second hcap]
    exact cap_weighted_pos h hcap _
      (fun i => (hv i).2 ha (capVertex_strict i))

/-- It is enough to prove the support property for active labels. -/
theorem fixed_gap_of_active_cases
    (H : ∀ (a u A v : ℝ) (s t : TransverseSign) (k : Fin 4),
      Admissible a u → Admissible A v → ActiveLabel a u → ActiveLabel A v →
      PairProperty a u A v s t k) :
    ∀ (a u A v : ℝ) (s t : TransverseSign) (k : Fin 4),
      Admissible a u → Admissible A v → PairProperty a u A v s t k := by
  have target (a u A v : ℝ) (s t : TransverseSign) (k : Fin 4)
      (ha : Admissible a u) (hb : Admissible A v) (hact : ActiveLabel a u) :
      PairProperty a u A v s t k := by
    rcases hb.selected with hA | hT | hcap
    · exact H a u A v s t k ha hb hact (Or.inl hA)
    · exact H a u A v s t k ha hb hact (Or.inr hT)
    · exact pairProperty_cap_second hb hcap s t k (fun i =>
        H a u (capVertex i).1 (capVertex i).2 s t k ha
          (capVertex_strict i).admissible hact (capVertex_active i))
  intro a u A v s t k ha hb
  rcases ha.selected with hA | hT | hcap
  · exact target a u A v s t k ha hb (Or.inl hA)
  · exact target a u A v s t k ha hb (Or.inr hT)
  · exact pairProperty_cap_first ha hcap s t k (fun i =>
      target (capVertex i).1 (capVertex i).2 A v s t k
        (capVertex_strict i).admissible hb (capVertex_active i))

end SquaresInCircles.Seven
