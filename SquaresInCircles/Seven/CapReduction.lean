import SquaresInCircles.Seven.Contacts

/-!
# Capped labels

Where the label is `π/4` the support sums are affine in the state, and the
capped region is a triangle whose vertices are admissible ties. So a support
sum at a capped state is a convex combination of its values at the vertices,
and at least one of them. Nonnegativity passes over, and a zero would pass to
a vertex as a contact with a capped label, which does not exist.
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

lemma capVertex_admissible (i : Fin 3) :
    Admissible (capVertex i).1 (capVertex i).2 := by
  have hp0 := pi_lower_157
  have hp1 := pi_lt_22_over_7
  have hr (a u : ℝ) (ha0 : 1/2 ≤ a) (hu0 : 0 ≤ u)
      (hau : u ≤ a) (ha1 : a < 193/250) (hu1 : u < 193/250) :
      Admissible a u := by
    refine ⟨hu0,hau,ha0,?_⟩
    have hA := mul_nonneg (show 0 ≤ 193/250-a by linarith)
      (show 0 ≤ 193/250+a+1 by linarith)
    have hU := mul_nonneg (show 0 ≤ 193/250-u by linarith)
      (show 0 ≤ 193/250+u+1 by linarith)
    dsimp [phi,targetSq]
    linarith
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

lemma support_barycentric (w x y : Fin 3 → ℝ) (hw : ∑ i,w i=1) (c z : ℝ) :
    support (∑ i,w i*x i) (c*∑ i,w i*y i) z =
      ∑ i,w i*support (x i) (c*y i) z := by
  have hconst := congrArg (fun t : ℝ =>
    t*((|Real.cos z|+|Real.sin z|)/2)) hw
  simp only [Fin.sum_univ_three] at hw hconst ⊢
  dsimp [support]
  linarith [hconst]

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
  linarith [hm,hc]

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
  linarith [hm,hc]

/-- A convex combination of three values is at least one of them. -/
lemma exists_le_weighted_sum {w f : Fin 3 → ℝ} (hw : ∀ i,0 ≤ w i) (hs : ∑ i,w i = 1) :
    ∃ i,f i ≤ ∑ j,w j*f j := by
  obtain ⟨i,-,hi⟩ := Finset.exists_min_image Finset.univ f Finset.univ_nonempty
  refine ⟨i,?_⟩
  calc f i = ∑ j,w j*f i := by rw [← Finset.sum_mul,hs,one_mul]
    _ ≤ ∑ j,w j*f j := Finset.sum_le_sum fun j _ =>
      mul_le_mul_of_nonneg_left (hi j (Finset.mem_univ j)) (hw j)

/-- The support assertion at the gap `π/3`: nonnegative, and zero only at a
contact. -/
def PairProperty (a u A v : ℝ) (s t : TransverseSign) (k : Fin 4) : Prop :=
  0 ≤ pairSupport a u A v s t k gap ∧
    (pairSupport a u A v s t k gap = 0 → Equality.OrderedContact a u A v s t)

lemma PairProperty.of_pos {a u A v : ℝ} {s t : TransverseSign} {k : Fin 4}
    (hp : 0 < pairSupport a u A v s t k gap) : PairProperty a u A v s t k :=
  ⟨hp.le,fun hz => absurd hz hp.ne'⟩

lemma pairProperty_cap_first {a u A v : ℝ}
    (h : Admissible a u) (h' : Admissible A v) (hcap : label a u = Real.pi/4)
    (s t : TransverseSign) (k : Fin 4)
    (hv : ∀ i,PairProperty (capVertex i).1 (capVertex i).2 A v s t k) :
    PairProperty a u A v s t k := by
  obtain ⟨i,hi⟩ := exists_le_weighted_sum
    (f := fun i => pairSupport (capVertex i).1 (capVertex i).2 A v s t k gap)
    (capWeights_nonneg h hcap) (capWeights_sum a u)
  rw [← cap_pair_first hcap] at hi
  refine ⟨(hv i).1.trans hi,fun hz => ?_⟩
  have hc := (hv i).2 (le_antisymm (hi.trans hz.le) (hv i).1)
  exact absurd (capVertex_label i)
    (Equality.contact_label_not_cap (capVertex_admissible i) h' hc).1

lemma pairProperty_cap_second {a u A v : ℝ}
    (h : Admissible a u) (h' : Admissible A v) (hcap : label A v = Real.pi/4)
    (s t : TransverseSign) (k : Fin 4)
    (hv : ∀ i,PairProperty a u (capVertex i).1 (capVertex i).2 s t k) :
    PairProperty a u A v s t k := by
  obtain ⟨i,hi⟩ := exists_le_weighted_sum
    (f := fun i => pairSupport a u (capVertex i).1 (capVertex i).2 s t k gap)
    (capWeights_nonneg h' hcap) (capWeights_sum A v)
  rw [← cap_pair_second hcap] at hi
  refine ⟨(hv i).1.trans hi,fun hz => ?_⟩
  have hc := (hv i).2 (le_antisymm (hi.trans hz.le) (hv i).1)
  exact absurd (capVertex_label i)
    (Equality.contact_label_not_cap h (capVertex_admissible i) hc).2

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
    · exact pairProperty_cap_second ha hb hcap s t k (fun i =>
        H a u (capVertex i).1 (capVertex i).2 s t k ha
          (capVertex_admissible i) hact (capVertex_active i))
  intro a u A v s t k ha hb
  rcases ha.selected with hA | hT | hcap
  · exact target a u A v s t k ha hb (Or.inl hA)
  · exact target a u A v s t k ha hb (Or.inr hT)
  · exact pairProperty_cap_first ha hb hcap s t k (fun i =>
      target (capVertex i).1 (capVertex i).2 A v s t k
        (capVertex_admissible i) hb (capVertex_active i))

end SquaresInCircles.Seven
