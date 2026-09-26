import SquaresInCircles.Seven.Support

/-!
# Support sums of a canonical pair

The support sum of a canonical pair on each of the four edge axes of the first
square, and its value on each axis. A sign `s` turns the state `(a, u)` into
the offset `s u` and the label `s * label a u`.
-/
noncomputable section
namespace SquaresInCircles.Seven

inductive TransverseSign where
  | positive
  | negative

def TransverseSign.coe : TransverseSign → ℝ
  | .positive => 1
  | .negative => -1

def cardinalAngle (k : Fin 4) : ℝ := (k.val : ℝ)*Real.pi/2

def pairSupport (a u A v : ℝ) (s t : TransverseSign) (k : Fin 4) (gamma : ℝ) : ℝ :=
  support a (s.coe*u) (cardinalAngle k) +
  support A (t.coe*v)
    (cardinalAngle k+Real.pi-gamma-s.coe*label a u+t.coe*label A v)

lemma sign_admissible {a u : ℝ} (h : Admissible a u) (s : TransverseSign) :
    Admissible a |s.coe*u| := by
  cases s <;> simpa [TransverseSign.coe,abs_of_nonneg h.1] using h

lemma sign_label {a u : ℝ} (h : Admissible a u) (s : TransverseSign) :
    signedLabel a (s.coe*u) = s.coe*label a u := by
  have hp : signedLabel a u = label a u := by
    simp [signedLabel,not_lt_of_ge h.1,abs_of_nonneg h.1]
  cases s
  · simpa [TransverseSign.coe] using hp
  · have hn := signedLabel_neg (a := a) (b := u)
      (by simpa only [abs_of_nonneg h.1] using h)
    simpa [TransverseSign.coe,hp] using hn

lemma support_zero (a b : ℝ) : support a b 0 = a+1/2 := by
  norm_num [support]

lemma support_half_pi (a b : ℝ) : support a b (Real.pi/2) = b+1/2 := by
  norm_num [support]

lemma support_pi (a b : ℝ) : support a b Real.pi = -a+1/2 := by
  norm_num [support]

lemma support_three_half_pi (a b : ℝ) : support a b (3*Real.pi/2) = -b+1/2 := by
  rw [show 3*Real.pi/2 = Real.pi+Real.pi/2 by ring]
  norm_num [support,Real.cos_add,Real.sin_add]

lemma support_three_half_sub (a b z : ℝ) :
    support a b (3*Real.pi/2-z) =
      -a*Real.sin z-b*Real.cos z+(|Real.sin z|+|Real.cos z|)/2 := by
  rw [show 3*Real.pi/2-z = (Real.pi/2-z)+Real.pi by ring]
  simp only [support,Real.cos_add_pi,Real.sin_add_pi,Real.cos_pi_div_two_sub,
    Real.sin_pi_div_two_sub,abs_neg]
  ring

lemma support_two_pi_sub (a b z : ℝ) :
    support a b (2*Real.pi-z) =
      a*Real.cos z-b*Real.sin z+(|Real.cos z|+|Real.sin z|)/2 := by
  simp only [support,Real.cos_two_pi_sub,Real.sin_two_pi_sub,abs_neg]
  ring

lemma cos_five_half_pi_sub (z : ℝ) : Real.cos (5*Real.pi/2-z) = Real.sin z := by
  rw [show 5*Real.pi/2-z = (Real.pi/2-z)+2*Real.pi by ring,Real.cos_add_two_pi,
    Real.cos_pi_div_two_sub]

lemma pairSupport_zero (a u A v gamma : ℝ) (s t : TransverseSign) :
    pairSupport a u A v s t 0 gamma =
      a+1/2+support A (t.coe*v)
        (Real.pi-gamma-s.coe*label a u+t.coe*label A v) := by
  simp only [pairSupport,cardinalAngle,Fin.val_zero,Nat.cast_zero,zero_mul,
    zero_div,zero_add,support_zero]

lemma pairSupport_three (a u A v gamma : ℝ) (s t : TransverseSign) :
    pairSupport a u A v s t 3 gamma =
      1/2-s.coe*u+support A (t.coe*v)
        (5*Real.pi/2-gamma-s.coe*label a u+t.coe*label A v) := by
  have hk : cardinalAngle (3 : Fin 4) = 3*Real.pi/2 := by norm_num [cardinalAngle]
  rw [pairSupport,hk,support_three_half_pi]
  congr 1
  · ring
  · congr 1
    ring

lemma pairSupport_two (a u A v gamma : ℝ) (s t : TransverseSign) :
    pairSupport a u A v s t 2 gamma =
      1/2-a+support A (t.coe*v)
        (2*Real.pi-gamma-s.coe*label a u+t.coe*label A v) := by
  have hk : cardinalAngle (2 : Fin 4) = Real.pi := by norm_num [cardinalAngle]
  rw [pairSupport,hk,support_pi]
  congr 1
  · ring
  · congr 1
    ring

lemma pairSupport_one (a u A v gamma : ℝ) (s t : TransverseSign) :
    pairSupport a u A v s t 1 gamma =
      1/2+s.coe*u+support A (t.coe*v)
        (3*Real.pi/2-gamma-s.coe*label a u+t.coe*label A v) := by
  have hk : cardinalAngle (1 : Fin 4) = Real.pi/2 := by norm_num [cardinalAngle]
  rw [pairSupport,hk,support_half_pi]
  congr 1
  · ring
  · congr 1
    ring

/-- The inward support sum with a positive source sign, in the turn
`label a u - t label A v - π/6`. -/
lemma pairSupport_inward {a u A v : ℝ} (t : TransverseSign)
    (h : Admissible a u) (h' : Admissible A v) :
    pairSupport a u A v .positive t 2 gap =
      1/2-a-A*Real.sin (label a u-t.coe*label A v-Real.pi/6)+
      |Real.sin (label a u-t.coe*label A v-Real.pi/6)|/2+
      (1/2-t.coe*v)*Real.cos (label a u-t.coe*label A v-Real.pi/6) := by
  have hc : 0 ≤ Real.cos (label a u-t.coe*label A v-Real.pi/6) := by
    have h0 := h.label_nonneg
    have h1 := h.label_le_quarter
    have h2 := h'.label_nonneg
    have h3 := h'.label_le_quarter
    apply Real.cos_nonneg_of_mem_Icc
    cases t <;> simp only [TransverseSign.coe] <;> constructor <;> linarith [Real.pi_pos]
  have he : 2*Real.pi-gap-TransverseSign.positive.coe*label a u+t.coe*label A v =
      3*Real.pi/2-(label a u-t.coe*label A v-Real.pi/6) := by
    simp only [gap,TransverseSign.coe]
    ring
  rw [pairSupport_two,he,support_three_half_sub,abs_of_nonneg hc]
  ring

end SquaresInCircles.Seven
