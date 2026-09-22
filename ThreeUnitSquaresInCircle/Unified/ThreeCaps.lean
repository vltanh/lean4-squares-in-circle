import ThreeUnitSquaresInCircle.Unified.ThreeScalar

/-!
# Concrete arc witnesses for the remaining three-square case

The containing witness is only an interval known to lie in the square. We
never assume that it is the entire intersection. The exterior witness has a
specified clipped-cap length; once clipping is excluded, its center is retained.
-/
noncomputable section
open Set
namespace ThreeUnitSquaresInCircle.Unified

def threeCapA (a : ℝ) : ℝ := Real.arccos ((a-1/2)/auxThree)
def threeCapV (b : ℝ) : ℝ := Real.arcsin ((1/2-b)/auxThree)
def threeCapLength (a b : ℝ) : ℝ :=
  min (2*threeCapA a) (threeCapA a+threeCapV b)
def threeContainingLength (a b : ℝ) : ℝ :=
  Real.pi/2+Real.arcsin ((1/2-a)/auxThree)+Real.arcsin ((1/2-b)/auxThree)

lemma three_cap_data {a b : ℝ} (ha : 1/2 ≤ a) (hb : 0 ≤ b)
    (hp : P3Strict a b) :
    0 ≤ (a-1/2)/auxThree ∧ (a-1/2)/auxThree < 1/2 ∧
    1/2+(16/13)*((a-1/2)/auxThree) < (1/2-b)/auxThree ∧
    Real.pi/3 < threeCapA a ∧ threeCapA a ≤ Real.pi/2 ∧
    2*Real.pi/3 < threeCapLength a b := by
  have hx0 : 0 ≤ (a-1/2)/auxThree := by dsimp [auxThree]; linarith
  have hx1 : (a-1/2)/auxThree < 1/2 := by
    dsimp [auxThree]; linarith [hp.2.2.1]
  have hv : 1/2+(16/13)*((a-1/2)/auxThree) < (1/2-b)/auxThree := by
    dsimp [auxThree]; linarith [hp.1]
  have hAsmall := arcsin_lt_sixth hx0 hx1
  have hA0 := Real.arcsin_nonneg.mpr hx0
  have hA : Real.pi/3 < threeCapA a := by
    dsimp [threeCapA,Real.arccos]; linarith
  have hAp : threeCapA a ≤ Real.pi/2 := by
    dsimp [threeCapA,Real.arccos]; linarith
  have hB := three_truncated_gap hx0 hx1
    (show 1/2+(a-1/2)/auxThree < (1/2-b)/auxThree by linarith)
  refine ⟨hx0,hx1,hv,hA,hAp,?_⟩
  exact lt_min (by linarith) hB

lemma three_cap_mem {a b t : ℝ} (ha : 1/2 ≤ a) (hb : 0 ≤ b)
    (hp : P3Strict a b)
    (ht : t ∈ Ioo (max (-threeCapA a) (-threeCapV b)) (threeCapA a)) :
    |auxThree*Real.cos t-a| < 1/2 ∧ |auxThree*Real.sin t-b| < 1/2 := by
  obtain ⟨hx0,hx1,hv,hA,hAp,hgap⟩ := three_cap_data ha hb hp
  have ht0 : -threeCapA a < t := (le_max_left _ _).trans_lt ht.1
  have ht1 : t < threeCapA a := ht.2
  have htdom : t ∈ Ioo (-(Real.pi/2)) (Real.pi/2) :=
    ⟨by linarith,by linarith⟩
  have hcos : (a-1/2)/auxThree < Real.cos t := by
    have h := Real.cos_lt_cos_of_nonneg_of_le_pi (abs_nonneg t)
      (show threeCapA a ≤ Real.pi by linarith [Real.pi_pos])
      (abs_lt.mpr ⟨ht0,ht1⟩)
    rw [threeCapA,Real.cos_arccos (by linarith) (by linarith)] at h
    simpa only [Real.cos_abs] using h
  have hasin : Real.arcsin (-((1/2-b)/auxThree)) < t := by
    rw [Real.arcsin_neg]
    exact (le_max_right _ _).trans_lt ht.1
  have hsin := (Real.arcsin_lt_iff_lt_sin' ⟨htdom.1,htdom.2.le⟩).mp hasin
  have hcos1 := Real.cos_le_one t
  have hsin1 := Real.sin_le_one t
  dsimp [auxThree] at hcos hsin ⊢
  exact ⟨abs_lt.mpr ⟨by linarith,by linarith⟩,
    abs_lt.mpr ⟨by linarith,by linarith⟩⟩

lemma cap_length_identity (A V : ℝ) : A-max (-A) (-V)=min (2*A) (A+V) := by
  by_cases h : A ≤ V
  · rw [max_eq_left (by linarith),min_eq_left (by linarith)]
    ring
  · rw [max_eq_right (by linarith),min_eq_right (by linarith)]
    ring

lemma three_cap_arc_formula {S : UnitSquare} {o : Point} (C : SquareChart S o)
    (ha : 1/2 ≤ C.a) (hp : P3Strict C.a C.b) :
    ∃ B : OpenArc o auxThree {z | openSquare S z},
      2*B.halfWidth=threeCapLength C.a C.b := by
  obtain ⟨hx0,hx1,hv,hA,hAp,hgap⟩ := three_cap_data ha C.nonneg.2 hp
  have hlen := cap_length_identity (threeCapA C.a) (threeCapV C.b)
  change threeCapA C.a-max (-threeCapA C.a) (-threeCapV C.b)=
    threeCapLength C.a C.b at hlen
  obtain ⟨B,hB⟩ := C.arc auxThree
    (max (-threeCapA C.a) (-threeCapV C.b)) (threeCapA C.a)
    (by linarith [Real.pi_pos])
    (by have h := le_max_left (-threeCapA C.a) (-threeCapV C.b)
        linarith [Real.pi_pos])
    (fun t ht => three_cap_mem ha C.nonneg.2 hp ht)
  exact ⟨B,by rw [hB]; linarith⟩

lemma three_containing_mem {a b t : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (ha1 : a < 1/2) (hb1 : b < 1/2)
    (ht : t ∈ Ioo (-Real.arcsin ((1/2-b)/auxThree))
      (Real.pi/2+Real.arcsin ((1/2-a)/auxThree))) :
    |auxThree*Real.cos t-a| < 1/2 ∧ |auxThree*Real.sin t-b| < 1/2 := by
  have hp : 0 < (1/2-a)/auxThree := by dsimp [auxThree]; linarith
  have hq : 0 < (1/2-b)/auxThree := by dsimp [auxThree]; linarith
  have ht0 : -(Real.pi/2) < t := by
    linarith [Real.arcsin_le_pi_div_two ((1/2-b)/auxThree),ht.1]
  have ht1 : t < Real.pi := by
    linarith [Real.arcsin_le_pi_div_two ((1/2-a)/auxThree),ht.2]
  have hcos : -((1/2-a)/auxThree) < Real.cos t := by
    by_cases ht2 : t ≤ Real.pi/2
    · have hc := Real.cos_nonneg_of_mem_Icc ⟨ht0.le,ht2⟩
      linarith
    · have hdom : Real.pi/2-t ∈ Ioc (-(Real.pi/2)) (Real.pi/2) :=
        ⟨by linarith,by linarith [Real.pi_pos]⟩
      have haS : Real.arcsin (-((1/2-a)/auxThree)) < Real.pi/2-t := by
        rw [Real.arcsin_neg]
        linarith [ht.2]
      have h := (Real.arcsin_lt_iff_lt_sin' hdom).mp haS
      simpa only [Real.sin_pi_div_two_sub] using h
  have hsin : -((1/2-b)/auxThree) < Real.sin t := by
    by_cases ht2 : t ≤ Real.pi/2
    · have h := (Real.arcsin_lt_iff_lt_sin' ⟨ht0,ht2⟩).mp
        (show Real.arcsin (-((1/2-b)/auxThree)) < t by
          rw [Real.arcsin_neg]; exact ht.1)
      exact h
    · have hs := Real.sin_nonneg_of_nonneg_of_le_pi
        (by linarith [Real.pi_pos]) ht1.le
      linarith
  have hc1 := Real.cos_le_one t
  have hs1 := Real.sin_le_one t
  dsimp [auxThree] at hcos hsin ⊢
  exact ⟨abs_lt.mpr ⟨by linarith,by linarith⟩,
    abs_lt.mpr ⟨by linarith,by linarith⟩⟩

lemma three_containing_arc_formula {S : UnitSquare} {o : Point}
    (C : SquareChart S o) (ho : openSquare S o) :
    ∃ A : OpenArc o auxThree {z | openSquare S z},
      2*A.halfWidth=threeContainingLength C.a C.b := by
  have hc := C.origin.mp ho
  have hP0 := Real.arcsin_pos.mpr
    (show 0 < (1/2-C.a)/auxThree by dsimp [auxThree]; linarith [hc.1])
  have hQ0 := Real.arcsin_pos.mpr
    (show 0 < (1/2-C.b)/auxThree by dsimp [auxThree]; linarith [hc.2])
  obtain ⟨A,hA⟩ := C.arc auxThree
    (-Real.arcsin ((1/2-C.b)/auxThree))
    (Real.pi/2+Real.arcsin ((1/2-C.a)/auxThree))
    (by linarith [Real.pi_pos])
    (by linarith [Real.pi_pos,Real.arcsin_le_pi_div_two ((1/2-C.a)/auxThree),
      Real.arcsin_le_pi_div_two ((1/2-C.b)/auxThree)])
    (fun t ht => three_containing_mem C.nonneg.1 C.nonneg.2 hc.1 hc.2 ht)
  refine ⟨A,?_⟩
  rw [hA]
  dsimp [threeContainingLength]
  ring

/-- Disjointness from the inscribed disk forces the exterior radial gap. -/
lemma three_gap_from_containing {S T : UnitSquare} {o : Point}
    (C : SquareChart S o) (D : SquareChart T o)
    (hCsort : C.b ≤ C.a) (ho : openSquare S o)
    (hDa : 1/2 ≤ D.a) (hDp : P3Strict D.a D.b)
    (hd : Disjoint {z | openSquare S z} {z | openSquare T z}) :
    1/2-C.a ≤ D.a-1/2 := by
  by_contra hn
  have hxlt : D.a-1/2 < 1/2-C.a := lt_of_not_ge hn
  have hc := C.origin.mp ho
  have hdb : D.b < 1/2 := by
    have hsum := (p3_coordinates D.nonneg.1 D.nonneg.2 (p3Strict_to_p3 hDp)).2.2
    linarith
  let t := ((D.a-1/2)+(1/2-C.a))/2
  have ht0 : 0 < t := by dsimp [t]; linarith [hc.1]
  have htx : D.a-1/2 < t := by dsimp [t]; linarith
  have htp : t < 1/2-C.a := by dsimp [t]; linarith
  have ht1 : t < 1/2 := by linarith [C.nonneg.1]
  let z := pointInDirection o D.phase t 0
  have hzT : openSquare T z := by
    apply (D.cartesian t 0).mpr
    refine ⟨abs_lt.mpr ⟨by linarith,by linarith⟩,?_⟩
    simpa only [zero_sub,abs_neg,D.abs_signedB] using hdb
  have hα : alpha S o ≤ C.a := by
    rcases C.coordinates with ⟨ha,hb⟩ | ⟨ha,hb⟩ <;> linarith
  have hβ : beta S o ≤ C.a := by
    rcases C.coordinates with ⟨ha,hb⟩ | ⟨ha,hb⟩ <;> linarith
  have hzS : openSquare S z := by
    apply inscribed_disk_mem S o (a := C.a) (p := 1/2-C.a)
      (by linarith [hc.1]) (by ring) hα hβ
    rw [show z=pointInDirection o D.phase t 0 by rfl,pointInDirection_norm]
    nlinarith
  exact Set.disjoint_left.mp hd hzS hzT

/-- The budget excludes clipping, and forces a small transverse center coordinate. -/
lemma three_cap_reduction {a b P Q L δ : ℝ}
    (ha : 1/2 ≤ a) (hb : 0 ≤ b) (hp : P3Strict a b)
    (hP : 0 ≤ P) (hQ : Q ∈ Icc (0:ℝ) 1)
    (hcentral : 1/2 < (16/13)*P+Q)
    (hgap : P ≤ (a-1/2)/auxThree)
    (hL : L=Real.pi/2+Real.arcsin P+Real.arcsin Q)
    (hδ : δ=2*Real.pi/3-L) (hδsmall : δ < 1/12)
    (hbudget : threeCapLength a b+L < 4*Real.pi/3) :
    threeCapA a ≤ threeCapV b ∧ b < 1/16 ∧ a ≤ 11/16 := by
  obtain ⟨hx0,hx1,hv,hA,hAp,hmin⟩ := three_cap_data ha hb hp
  have hnotclip : threeCapA a ≤ threeCapV b := by
    by_contra hn
    have hclip : threeCapV b < threeCapA a := lt_of_not_ge hn
    have hv1 : (1/2-b)/auxThree < 1 := by
      apply Real.arcsin_lt_pi_div_two.mp
      exact hclip.trans_le hAp
    have hcomp := three_compensation hP hQ hcentral hgap hx1 hv hv1
    have he : threeCapLength a b=threeCapA a+threeCapV b := by
      unfold threeCapLength
      exact min_eq_right (by linarith)
    rw [he,hL] at hbudget
    dsimp [threeCapA,threeCapV,Real.arccos] at hbudget
    linarith
  have hlen : threeCapLength a b=2*threeCapA a := by
    unfold threeCapLength
    exact min_eq_left (by linarith)
  have hAnear : threeCapA a < Real.pi/3+1/24 := by
    rw [hlen] at hbudget
    linarith
  have hrad := three_cap_near_axis hx0 hx1 hAnear
  have hsmall : b < 1/16 := by
    dsimp [auxThree] at hrad
    linarith [hp.2.2.1]
  exact ⟨hnotclip,hsmall,by linarith [hp.2.2.1]⟩

/-- In the surviving alternative, a symmetric occupied cap has the actual radial phase. -/
def threeFullCap {S : UnitSquare} {o : Point} (C : SquareChart S o)
    (ha : 1/2 ≤ C.a) (hp : P3Strict C.a C.b)
    (hfull : threeCapA C.a ≤ threeCapV C.b) :
    OpenArc o auxThree {z | openSquare S z} :=
  symmetricChartArc C auxThree (threeCapA C.a)
    (lt_trans (by positivity) (three_cap_data ha C.nonneg.2 hp).2.2.2.1)
    (le_trans (three_cap_data ha C.nonneg.2 hp).2.2.2.2.1
      (by linarith [Real.pi_pos]))
    (fun t ht => three_cap_mem ha C.nonneg.2 hp
      (by rw [max_eq_left (by linarith)]; exact ht))

end ThreeUnitSquaresInCircle.Unified
