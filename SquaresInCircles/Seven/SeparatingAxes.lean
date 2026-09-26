import SquaresInCircles.Common.Separation
import SquaresInCircles.Common.Contacts

/-!
# The separating-axis theorem

Strict overlap on the two edge axes of each of two squares implies overlap
along every normal. With `support_separator`, disjoint squares are separated
along one of their four edge axes.
-/
noncomputable section
namespace SquaresInCircles.Seven.SAT

def axisInside (c s : ℝ) (d : Point) : Prop :=
  let H := (1+c+s)/2
  |d.1| < H ∧ |d.2| < H ∧ |c*d.1+s*d.2| < H ∧ |-s*d.1+c*d.2| < H

def octagonSupport (c s : ℝ) (n : Point) : ℝ :=
  (|n.1|+|n.2|+|c*n.1+s*n.2|+|-s*n.1+c*n.2|)/2

lemma octagon_first_quadrant {c s : ℝ} (hc : 0 < c) (hs : 0 ≤ s)
    (hunit : c^2+s^2=1) (d n : Point) (hd : axisInside c s d)
    (hx : 0 ≤ n.1) (hy : 0 ≤ n.2) (hn : 0 < n.1+n.2) :
    dot n d < octagonSupport c s n := by
  have hxD := (abs_lt.mp hd.1).2
  have hyD := (abs_lt.mp hd.2.1).2
  have hpD := (abs_lt.mp hd.2.2.1).2
  have hp : 0 ≤ c*n.1+s*n.2 := by positivity
  by_cases hs0 : s=0
  · have hc1 : c=1 := by nlinarith
    subst s; subst c
    have hh := weighted_strict hx hy hn hxD hyD
    simp only [dot,octagonSupport,abs_of_nonneg hx,abs_of_nonneg hy,one_mul,zero_mul,
      add_zero,zero_add,neg_zero] at hh ⊢
    linarith
  · have hsp : 0 < s := lt_of_le_of_ne hs (Ne.symm hs0)
    by_cases hw : -s*n.1+c*n.2 ≤ 0
    · let a := s*n.1-c*n.2
      have ha : 0 ≤ a := by dsimp [a]; linarith
      have hab : 0 < a+n.2 := by
        by_contra hh
        have hny : n.2=0 := by linarith
        have hnx : 0 < n.1 := by linarith
        have hh' := mul_pos hsp hnx
        dsimp [a] at *
        nlinarith
      have hlt := weighted_strict ha hy hab hxD hpD
      have he₁ : a*d.1+n.2*(c*d.1+s*d.2) = s*dot n d := by
        dsimp [a,dot]; ring
      have he₂ : (1+c+s)/2*(a+n.2) = s*octagonSupport c s n := by
        simp only [octagonSupport,abs_of_nonneg hx,abs_of_nonneg hy,
          abs_of_nonneg hp,abs_of_nonpos hw]
        dsimp [a]
        linear_combination -(n.2/2)*hunit
      rw [he₁,he₂] at hlt
      exact lt_of_mul_lt_mul_left hlt hsp.le
    · have hw0 : 0 ≤ -s*n.1+c*n.2 := le_of_lt (lt_of_not_ge hw)
      let b := c*n.2-s*n.1
      have hb : 0 ≤ b := by dsimp [b]; linarith
      have hab : 0 < n.1+b := by
        by_contra hh
        have hnx : n.1=0 := by linarith
        have hny : 0 < n.2 := by linarith
        have hh' := mul_pos hc hny
        dsimp [b] at *
        nlinarith
      have hlt := weighted_strict hx hb hab hpD hyD
      have he₁ : n.1*(c*d.1+s*d.2)+b*d.2 = c*dot n d := by
        dsimp [b,dot]; ring
      have he₂ : (1+c+s)/2*(n.1+b) = c*octagonSupport c s n := by
        simp only [octagonSupport,abs_of_nonneg hx,abs_of_nonneg hy,
          abs_of_nonneg hp,abs_of_nonneg hw0]
        dsimp [b]
        linear_combination -(n.1/2)*hunit
      rw [he₁,he₂] at hlt
      exact lt_of_mul_lt_mul_left hlt hc.le

def qturn (p : Point) : Point := (-p.2,p.1)
def qturns : ℕ → Point → Point
  | 0,p => p
  | n+1,p => qturn (qturns n p)

lemma qturn_axisInside {c s : ℝ} {d : Point} (hd : axisInside c s d) :
    axisInside c s (qturn d) := by
  have h₁ : c*(-d.2)+s*d.1 = -(-s*d.1+c*d.2) := by ring
  have h₂ : -s*(-d.2)+c*d.1 = c*d.1+s*d.2 := by ring
  simpa only [axisInside,qturn,abs_neg,h₁,h₂] using
    And.intro hd.2.1 (And.intro hd.1 (And.intro hd.2.2.2 hd.2.2.1))

lemma qturn_support (c s : ℝ) (n : Point) :
    octagonSupport c s (qturn n) = octagonSupport c s n := by
  have h₁ : c*(-n.2)+s*n.1 = -(-s*n.1+c*n.2) := by ring
  have h₂ : -s*(-n.2)+c*n.1 = c*n.1+s*n.2 := by ring
  simp only [octagonSupport,qturn,h₁,h₂,abs_neg]
  ring

lemma qturns_facts (k : ℕ) (c s : ℝ) (n d : Point) :
    (axisInside c s d → axisInside c s (qturns k d)) ∧
    octagonSupport c s (qturns k n) = octagonSupport c s n ∧
    dot (qturns k n) (qturns k d) = dot n d ∧
    normSq (qturns k n) = normSq n := by
  induction k with
  | zero => exact ⟨id,rfl,rfl,rfl⟩
  | succ k ih =>
    refine ⟨fun h => qturn_axisInside (ih.1 h), ?_, ?_, ?_⟩
    · rw [qturns,qturn_support,ih.2.1]
    · calc
        _ = dot (qturns k n) (qturns k d) := by dsimp [qturns,qturn,dot]; ring
        _ = dot n d := ih.2.2.1
    · calc
        _ = normSq (qturns k n) := by dsimp [qturns,qturn,normSq]; ring
        _ = normSq n := ih.2.2.2

lemma qturn_first_quadrant (n : Point) :
    ∃ k : Fin 4, 0 ≤ (qturns k.val n).1 ∧ 0 ≤ (qturns k.val n).2 := by
  by_cases hx : 0 ≤ n.1 <;> by_cases hy : 0 ≤ n.2
  · exact ⟨0,hx,hy⟩
  · refine ⟨1,?_,?_⟩ <;> dsimp [qturns,qturn] <;> linarith
  · refine ⟨3,?_,?_⟩ <;> dsimp [qturns,qturn] <;> linarith
  · refine ⟨2,?_,?_⟩ <;> dsimp [qturns,qturn] <;> linarith

lemma octagon_strict {c s : ℝ} (hc : 0 < c) (hs : 0 ≤ s)
    (hunit : c^2+s^2=1) {d n : Point} (hd : axisInside c s d) (hn : n ≠ (0,0)) :
    dot n d < octagonSupport c s n := by
  obtain ⟨k,hx,hy⟩ := qturn_first_quadrant n
  have hf := qturns_facts k.val c s n d
  have hpos : 0 < (qturns k.val n).1+(qturns k.val n).2 := by
    by_contra hh
    have hx0 : (qturns k.val n).1=0 := by linarith
    have hy0 : (qturns k.val n).2=0 := by linarith
    have hn0 : normSq n=0 := by
      rw [← hf.2.2.2]
      simp [normSq,hx0,hy0]
    apply hn
    apply Prod.ext <;> dsimp [normSq] at hn0 ⊢ <;>
      nlinarith [sq_nonneg n.1,sq_nonneg n.2]
  have hh := octagon_first_quadrant hc hs hunit (qturns k.val d)
    (qturns k.val n) (hf.1 hd) hx hy hpos
  simpa only [hf.2.1,hf.2.2.1] using hh

def AxisInside (c s : ℝ) (d : Point) : Prop :=
  let H := (1+|c|+|s|)/2
  |d.1| < H ∧ |d.2| < H ∧ |c*d.1+s*d.2| < H ∧ |-s*d.1+c*d.2| < H

def reflect (p : Point) : Point := (p.1,-p.2)

lemma axis_neg_frame {c s : ℝ} {d : Point} (hd : AxisInside c s d) :
    AxisInside (-c) (-s) d := by
  have h1 : (-c)*d.1+(-s)*d.2 = -(c*d.1+s*d.2) := by ring
  have h2 : -(-s)*d.1+(-c)*d.2 = -(-s*d.1+c*d.2) := by ring
  simpa only [AxisInside,abs_neg,h1,h2] using hd

lemma support_neg_frame (c s : ℝ) (n : Point) :
    octagonSupport (-c) (-s) n = octagonSupport c s n := by
  have h1 : (-c)*n.1+(-s)*n.2 = -(c*n.1+s*n.2) := by ring
  have h2 : -(-s)*n.1+(-c)*n.2 = -(-s*n.1+c*n.2) := by ring
  simp only [octagonSupport,h1,h2,abs_neg]

lemma axis_reflect {c s : ℝ} {d : Point} (hd : AxisInside c s d) :
    AxisInside c (-s) (reflect d) := by
  have h1 : c*d.1+(-s)*(-d.2) = c*d.1+s*d.2 := by ring
  have h2 : -(-s)*d.1+c*(-d.2) = -(-s*d.1+c*d.2) := by ring
  simpa only [AxisInside,reflect,abs_neg,h1,h2] using hd

lemma support_reflect (c s : ℝ) (n : Point) :
    octagonSupport c (-s) (reflect n) = octagonSupport c s n := by
  have h1 : c*n.1+(-s)*(-n.2) = c*n.1+s*n.2 := by ring
  have h2 : -(-s)*n.1+c*(-n.2) = -(-s*n.1+c*n.2) := by ring
  simp only [octagonSupport,reflect,h1,h2,abs_neg]

lemma reflect_dot (n d : Point) : dot (reflect n) (reflect d) = dot n d := by
  dsimp [reflect,dot]
  ring

lemma reflect_ne {n : Point} (hn : n ≠ (0,0)) : reflect n ≠ (0,0) := by
  intro he
  apply hn
  have hx := congrArg Prod.fst he
  have hy := congrArg Prod.snd he
  apply Prod.ext <;> dsimp [reflect] at * <;> linarith

lemma positive_cosine_strict {c s : ℝ} (hc : 0 < c) (hu : c^2+s^2=1)
    {d n : Point} (hd : AxisInside c s d) (hn : n ≠ (0,0)) :
    dot n d < octagonSupport c s n := by
  by_cases hs : 0 ≤ s
  · have hi : axisInside c s d := by
      simpa only [AxisInside,axisInside,abs_of_pos hc,abs_of_nonneg hs] using hd
    exact octagon_strict hc hs hu hi hn
  · have hs' : 0 ≤ -s := by linarith
    have hi := axis_reflect hd
    have hi' : axisInside c (-s) (reflect d) := by
      simpa only [AxisInside,axisInside,abs_of_pos hc,abs_of_nonneg hs'] using hi
    have hh := octagon_strict hc hs' (by nlinarith) hi' (reflect_ne hn)
    rw [reflect_dot,support_reflect] at hh
    exact hh

lemma zero_cosine_strict {s : ℝ} (hu : s^2=1)
    {d n : Point} (hd : AxisInside 0 s d) (hn : n ≠ (0,0)) :
    dot n d < octagonSupport 0 s n := by
  have habs : |s|=1 := by nlinarith [sq_abs s,abs_nonneg s]
  have hdx : |d.1| < 1 := by simpa [AxisInside,abs_zero,habs] using hd.1
  have hdy : |d.2| < 1 := by simpa [AxisInside,abs_zero,habs] using hd.2.1
  have hsum : 0 < |n.1|+|n.2| := by
    by_contra he
    apply hn
    have hnx : n.1=0 := abs_eq_zero.mp (by linarith [abs_nonneg n.1,abs_nonneg n.2])
    have hny : n.2=0 := abs_eq_zero.mp (by linarith [abs_nonneg n.1,abs_nonneg n.2])
    exact Prod.ext hnx hny
  have hh := weighted_strict (abs_nonneg n.1) (abs_nonneg n.2) hsum hdx hdy
  have hx : n.1*d.1 ≤ |n.1| * |d.1| := by simpa only [abs_mul] using le_abs_self (n.1*d.1)
  have hy : n.2*d.2 ≤ |n.2| * |d.2| := by simpa only [abs_mul] using le_abs_self (n.2*d.2)
  have he : octagonSupport 0 s n = |n.1|+|n.2| := by
    simp only [octagonSupport,zero_mul,zero_add,add_zero,abs_mul,abs_neg,habs,one_mul]
    ring
  rw [he]
  dsimp [dot]
  linarith

/-- Strict overlap on all four edge axes implies overlap on every normal. -/
theorem all_normals_strict {c s : ℝ} (hu : c^2+s^2=1)
    {d n : Point} (hd : AxisInside c s d) (hn : n ≠ (0,0)) :
    dot n d < octagonSupport c s n := by
  rcases lt_trichotomy c 0 with hc | hc | hc
  · have hi := axis_neg_frame hd
    have hh := positive_cosine_strict (show 0 < -c by linarith)
      (show (-c)^2+(-s)^2=1 by nlinarith) hi hn
    rw [support_neg_frame] at hh
    exact hh
  · subst c
    exact zero_cosine_strict (by nlinarith) hd hn
  · exact positive_cosine_strict hc hu hd hn

def threshold (S T : UnitSquare) : ℝ := (1+|relativeC S T|+|relativeS S T|)/2

/-- Ordinary non-overlap implies one of the four unsigned separating axes. -/
theorem separating_axes (S T : UnitSquare)
    (hd : ∀ p, ¬ (openSquare S p ∧ openSquare T p)) :
    threshold S T ≤ |frameX S (sub T.center S.center)| ∨
    threshold S T ≤ |frameY S (sub T.center S.center)| ∨
    threshold S T ≤ |frameX T (sub T.center S.center)| ∨
    threshold S T ≤ |frameY T (sub T.center S.center)| := by
  obtain ⟨e⟩ := support_separator S T hd
  let d : Point := (frameX S (sub T.center S.center),frameY S (sub T.center S.center))
  let n : Point := (frameX S e.normal,frameY S e.normal)
  have hn : n ≠ (0,0) := by
    intro he
    have hx := congrArg Prod.fst he
    have hy := congrArg Prod.snd he
    have hu := frame_norm S e.normal
    dsimp [n] at hx hy
    rw [hx,hy] at hu
    apply e.nonzero
    apply Prod.ext <;> dsimp [normSq] at hu ⊢ <;>
      nlinarith [sq_nonneg e.normal.1,sq_nonneg e.normal.2]
  by_contra hnot
  push Not at hnot
  have hi : AxisInside (relativeC S T) (relativeS S T) d := by
    dsimp [AxisInside,d]
    rw [← (relative_normal S T _).1,← (relative_normal S T _).2]
    exact hnot
  have hlt := all_normals_strict (relative_unit S T) hi hn
  have hdot : dot n d = dot e.normal (sub T.center S.center) := by
    exact frame_dot S _ _
  have hsup : octagonSupport (relativeC S T) (relativeS S T) n =
      width S e.normal+width T e.normal := by
    dsimp [octagonSupport,n]
    rw [← (relative_normal S T _).1,← (relative_normal S T _).2]
    dsimp [width]
    ring
  rw [hdot,hsup] at hlt
  exact (not_lt_of_ge e.separates) hlt

end SquaresInCircles.Seven.SAT
