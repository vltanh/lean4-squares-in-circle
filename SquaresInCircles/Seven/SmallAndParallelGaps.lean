import SquaresInCircles.Seven.AngularMinima
import SquaresInCircles.Seven.ParallelLabels
import SquaresInCircles.Seven.EasySectors

/-!
# Small gaps and cardinal minima

For gaps up to 1 the two marker arcs share three points of the unit circle,
which forces every support sum to be positive. At a cardinal target direction
below the gap `π/3` the squares are parallel or quarter-turned, and the
parallel labels apply.
-/
noncomputable section
namespace SquaresInCircles.Seven

lemma small_gap_support_pos {a u A v g : ℝ} (s t : TransverseSign) (k : Fin 4)
    (h : Admissible a u) (h' : Admissible A v) (hg : 0≤g ∧ g≤1) :
    0<pairSupport a u A v s t k g := by
  let p := s.coe*label a u
  let r := t.coe*label A v
  let z := cardinalAngle k-p-g/2
  let h1 := support a (s.coe*u) (cardinalAngle k)
  let h2 := support A (t.coe*v) (cardinalAngle k+Real.pi-g-p+r)
  have hb (e : ℝ) (he : |e|≤1/3200) :
      Real.cos (z-e)≤h1 ∧ -Real.cos (z-e)≤h2 := by
    have he' := abs_le.mp he
    have hp : |(p+g/2+e)-signedLabel a (s.coe*u)|≤801/1600 := by
      rw [sign_label h s]
      change |(p+g/2+e)-p|≤801/1600
      apply abs_le.mpr
      constructor <;> linarith [hg.1,hg.2,he'.1,he'.2]
    have hr : |(r-g/2+e)-signedLabel A (t.coe*v)|≤801/1600 := by
      rw [sign_label h' t]
      change |(r-g/2+e)-r|≤801/1600
      apply abs_le.mpr
      constructor <;> linarith [hg.1,hg.2,he'.1,he'.2]
    have hfirst := marker_arc_support (sign_admissible h s) hp (cardinalAngle k)
    have hsecond := marker_arc_support (sign_admissible h' t) hr
      (cardinalAngle k+Real.pi-g-p+r)
    have e1 : cardinalAngle k-(p+g/2+e)=z-e := by dsimp [z]; ring
    have e2 : cardinalAngle k+Real.pi-g-p+r-(r-g/2+e)=(z-e)+Real.pi := by dsimp [z]; ring
    rw [e1] at hfirst
    rw [e2,Real.cos_add_pi] at hsecond
    exact ⟨hfirst,hsecond⟩
  by_contra hn
  have hsum : h1+h2≤0 := le_of_not_gt hn
  have heq (e : ℝ) (he : |e|≤1/3200) : Real.cos (z-e)=h1 := by
    have hh := hb e he
    linarith
  have h0 := heq 0 (by norm_num)
  have hp := heq (1/3200) (by norm_num)
  have hm := heq (-1/3200) (by norm_num)
  simp only [sub_zero] at h0
  have he : z-(-1/3200)=z+1/3200 := by ring
  rw [he,Real.cos_add] at hm
  rw [Real.cos_sub] at hp
  have hsin0 : 0<Real.sin (1/3200:ℝ) := Real.sin_pos_of_pos_of_lt_pi
    (by norm_num) (by linarith [pi_lower_157])
  have hcos1 : Real.cos (1/3200:ℝ)≠1 := by
    intro heq
    have hu := Real.sin_sq_add_cos_sq (1/3200:ℝ)
    rw [heq] at hu
    nlinarith
  have hsinProd : Real.sin z*Real.sin (1/3200)=0 := by linear_combination (hp-hm)/2
  have hcosProd : Real.cos z*(Real.cos (1/3200)-1)=0 := by linear_combination (hp+hm)/2-h0
  have hsz : Real.sin z=0 := (mul_eq_zero.mp hsinProd).resolve_right (ne_of_gt hsin0)
  have hcz : Real.cos z=0 := (mul_eq_zero.mp hcosProd).resolve_right (sub_ne_zero.mpr hcos1)
  have hu := Real.sin_sq_add_cos_sq z
  rw [hsz,hcz] at hu
  norm_num at hu

lemma support_add_pi (a b z : ℝ) : support a b (z+Real.pi)=support (-a) (-b) z := by
  simp [support,Real.cos_add,Real.sin_add,abs_neg]

lemma support_add_half_pi (a b z : ℝ) : support a b (z+Real.pi/2)=support b (-a) z := by
  simp [support,Real.cos_add,Real.sin_add,abs_neg]
  ring

lemma cardinal_support_sum (a b A B : ℝ) (k : Fin 4) :
    support a b (cardinalAngle k)+support A B (cardinalAngle k) =
    ![a+A+1,b+B+1,-a-A+1,-b-B+1] k := by
  fin_cases k <;> norm_num [cardinalAngle,support,
    show (3:ℝ)*Real.pi/2=Real.pi+Real.pi/2 by ring,Real.sin_add,Real.cos_add] <;> ring

lemma Equality.parallel_zero_pos_below {a u A v g : ℝ} (s t : TransverseSign) (k : Fin 4)
    (h : Admissible a u) (h' : Admissible A v) (hg : 0 < g ∧ g < gap)
    (he : g+s.coe*label a u-t.coe*label A v = 0) :
    0 < pairSupport a u A v s t k g := by
  have hang : cardinalAngle k+Real.pi-g-s.coe*label a u+t.coe*label A v =
      cardinalAngle k+Real.pi := by linarith
  rw [pairSupport,hang,support_add_pi,cardinal_support_sum]
  have h0 := h.label_nonneg
  have h1 := h'.label_nonneg
  have ha := h.a_lt_five_fourths
  have hA := h'.a_lt_five_fourths
  have hu := h.u_lt
  have hv := h'.u_lt
  fin_cases k
  · norm_num
    linarith [h.2.2.1]
  · by_contra hn
    cases s <;> cases t <;> norm_num [TransverseSign.coe] at hn he ⊢
    · linarith [h.1]
    · linarith [h.1,h'.1]
    · have hl := opposite_labels_ge h h' (show 1 ≤ u+v by linarith)
      linarith [hg.2]
    · linarith [h'.1]
  · norm_num
    linarith [h'.2.2.1]
  · cases s <;> cases t <;> norm_num [TransverseSign.coe] at he ⊢
    · linarith [h'.1]
    · linarith [hg.1]
    · linarith [h.1,h'.1]
    · linarith [h.1]

lemma Equality.parallel_quarter_pos_below {a u A v g : ℝ} (s t : TransverseSign) (k : Fin 4)
    (h : Admissible a u) (h' : Admissible A v) (hg : 0 < g ∧ g < gap)
    (he : g+s.coe*label a u-t.coe*label A v = Real.pi/2) :
    0 < pairSupport a u A v s t k g := by
  have hang : cardinalAngle k+Real.pi-g-s.coe*label a u+t.coe*label A v =
      cardinalAngle k+Real.pi/2 := by linarith
  rw [pairSupport,hang,support_add_half_pi,cardinal_support_sum]
  have hu : |s.coe*u| < 31/40 := by
    cases s <;> simpa [TransverseSign.coe,abs_of_nonneg h.1] using h.u_lt
  have hv : |t.coe*v| < 31/40 := by
    cases t <;> simpa [TransverseSign.coe,abs_of_nonneg h'.1] using h'.u_lt
  have hu' := abs_lt.mp hu
  have hv' := abs_lt.mp hv
  have hlabel (hh : 1 ≤ a+t.coe*v ∨ 1 ≤ A-s.coe*u) : False := by
    have hp := quarter_difference_le (sign_admissible h s) (sign_admissible h' t) hh
    rw [sign_label h s,sign_label h' t] at hp
    dsimp [gap] at hg
    linarith
  fin_cases k
  · norm_num
    linarith [h.2.2.1]
  · by_contra hn
    norm_num at hn
    exact hlabel (Or.inr (by linarith))
  · by_contra hn
    norm_num at hn
    exact hlabel (Or.inl (by linarith))
  · norm_num
    linarith [h'.2.2.1]

lemma cardinal_target_relative {d : ℝ} (k : Fin 4)
    (h : Real.sin (cardinalAngle k+Real.pi-d)=0 ∨
      Real.cos (cardinalAngle k+Real.pi-d)=0) :
    Real.sin d=0 ∨ Real.cos d=0 := by
  obtain rfl | rfl | rfl | rfl : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by fin_cases k <;> simp
  · simpa [cardinalAngle,Real.sin_pi_sub,Real.cos_pi_sub,or_comm] using h
  · have he : cardinalAngle (1:Fin 4)+Real.pi-d=Real.pi+(Real.pi/2-d) := by norm_num [cardinalAngle]; ring
    rw [he] at h
    simpa [Real.sin_add,Real.cos_add,Real.cos_pi_div_two_sub,Real.sin_pi_div_two_sub,or_comm] using h
  · have he : cardinalAngle (2:Fin 4)+Real.pi-d=2*Real.pi-d := by norm_num [cardinalAngle]; ring
    rw [he] at h
    simpa [Real.sin_sub,Real.cos_sub,Real.sin_two_pi,Real.cos_two_pi] using h
  · have he : cardinalAngle (3:Fin 4)+Real.pi-d=2*Real.pi+(Real.pi/2-d) := by norm_num [cardinalAngle]; ring
    rw [he] at h
    simpa [Real.sin_add,Real.cos_add,Real.sin_two_pi,Real.cos_two_pi,
      Real.cos_pi_div_two_sub,Real.sin_pi_div_two_sub,or_comm] using h

lemma Equality.cardinal_target_pos_below {a u A v g : ℝ} (s t : TransverseSign) (k : Fin 4)
    (h : Admissible a u) (h' : Admissible A v) (hg : 1 ≤ g ∧ g < gap)
    (hcard : Real.sin (cardinalAngle k+Real.pi-g-s.coe*label a u+t.coe*label A v) = 0 ∨
      Real.cos (cardinalAngle k+Real.pi-g-s.coe*label a u+t.coe*label A v) = 0) :
    0 < pairSupport a u A v s t k g := by
  let d := g+s.coe*label a u-t.coe*label A v
  have hr : -Real.pi/2 < d ∧ d < Real.pi := by
    have ht0 := h.label_nonneg
    have ht1 := h.label_le_quarter
    have hs0 := h'.label_nonneg
    have hs1 := h'.label_le_quarter
    cases s <;> cases t <;> dsimp [d,gap,TransverseSign.coe] at * <;>
      constructor <;> linarith [Real.pi_pos]
  have he : cardinalAngle k+Real.pi-g-s.coe*label a u+t.coe*label A v =
      cardinalAngle k+Real.pi-d := by dsimp [d]; ring
  rw [he] at hcard
  rcases cardinal_target_relative k hcard with hsin | hcos
  · have hd := sin_zero_between ⟨by linarith [hr.1,Real.pi_pos],hr.2⟩ hsin
    exact parallel_zero_pos_below s t k h h' ⟨by linarith [hg.1],hg.2⟩ hd
  · have hd := cos_zero_between hr hcos
    exact parallel_quarter_pos_below s t k h h' ⟨by linarith [hg.1],hg.2⟩ hd

end SquaresInCircles.Seven
