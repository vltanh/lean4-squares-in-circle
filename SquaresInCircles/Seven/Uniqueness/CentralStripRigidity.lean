import SquaresInCircles.Seven.Uniqueness.NormalForm

/-!
# The containing square in the width-one central strip

No circle-height estimate is needed for this step. The center of a square
containing the origin has ordinate less than one in absolute value. A tilted
unit square has a horizontal section of width greater than one at that very
height. The fixed side columns therefore force an aligned central square.
-/
noncomputable section
open Set
namespace SquaresInCircles.Seven.Equality

lemma openSquare_isOpen (S : UnitSquare) : IsOpen {p : Point | openSquare S p} := by
  change IsOpen ({p | |localX S p|<1/2} ∩ {p | |localY S p|<1/2})
  exact (isOpen_lt (by unfold localX; fun_prop) continuous_const).inter
    (isOpen_lt (by unfold localY; fun_prop) continuous_const)

/-- Disjoint open interiors also exclude an open point of one square from the
closed other square. This deals with the seam between the two side squares. -/
lemma disjoint_open_closed (S T : UnitSquare)
    (hd : ∀p,¬(openSquare S p∧openSquare T p)) :
    ∀p,¬(openSquare S p∧closedSquare T p) := by
  intro p hp
  let f : ℝ → Point := fun t => add (scale (1-t) T.center) (scale t p)
  have hf : Continuous f := by dsimp [f,add,scale]; fun_prop
  have hpre : IsOpen {t : ℝ | openSquare S (f t)} := (openSquare_isOpen S).preimage hf
  have hone : openSquare S (f 1) := by simpa [f,add,scale] using hp.1
  obtain ⟨ε,hε,hball⟩ := Metric.isOpen_iff.mp hpre 1 hone
  let δ := min (ε/2) (1/2)
  have hδ : 0<δ := lt_min (by positivity) (by norm_num)
  have hδε : δ<ε := (min_le_left _ _).trans_lt (by linarith)
  have hδ1 : δ≤1/2 := min_le_right _ _
  have ht0 : 0≤1-δ := by linarith
  have ht1 : 1-δ<1 := by linarith
  have hnear : (1-δ)∈Metric.ball (1 : ℝ) ε := by
    rw [Metric.mem_ball,Real.dist_eq,show 1-δ-1=-δ by ring,abs_neg,abs_of_pos hδ]
    exact hδε
  have hS := hball hnear
  have hT := shrink_open T hp.2 ht0 ht1
  exact hd (f (1-δ)) ⟨hS,hT⟩

lemma open_segment_zero (S : UnitSquare) {p : Point}
    (h0 : openSquare S (0,0)) (hp : openSquare S p)
    {t : ℝ} (ht : 0≤t ∧ t<1) : openSquare S (scale t p) := by
  have he := local_affine S (0,0) p t
  have hpoint : add (scale (1-t) (0,0)) (scale t p)=scale t p := by
    simp [add,scale]
  rw [hpoint] at he
  constructor
  · rw [he.1]
    have htri := abs_add_le ((1-t)*localX S (0,0)) (t*localX S p)
    rw [abs_mul,abs_mul,abs_of_nonneg (by linarith : 0≤1-t),abs_of_nonneg ht.1] at htri
    have hfirst := mul_lt_mul_of_pos_left h0.1 (show 0<1-t by linarith)
    have hsecond := mul_le_mul_of_nonneg_left hp.1.le ht.1
    nlinarith
  · rw [he.2]
    have htri := abs_add_le ((1-t)*localY S (0,0)) (t*localY S p)
    rw [abs_mul,abs_mul,abs_of_nonneg (by linarith : 0≤1-t),abs_of_nonneg ht.1] at htri
    have hfirst := mul_lt_mul_of_pos_left h0.2 (show 0<1-t by linarith)
    have hsecond := mul_le_mul_of_nonneg_left hp.2.le ht.1
    nlinarith

def sideCenter : Fin 4 → Point := ![(1,-1/2),(1,1/2),(-1,-1/2),(-1,1/2)]

lemma containing_strip (S : UnitSquare) (h0 : openSquare S (0,0))
    (hwalls : ∀i : Fin 4,∀p,¬(openSquare S p∧openSquare (axisSquare (sideCenter i)) p)) :
    ∀p,openSquare S p → |p.2|<1 → |p.1|≤1/2 := by
  intro p hp hy
  by_contra hn
  have hx : 1/2<|p.1| := lt_of_not_ge hn
  let t := (1/2)/|p.1|
  have hpos : 0<|p.1| := by linarith
  have ht : 0<t ∧ t<1 := by
    dsimp [t]
    exact ⟨div_pos (by norm_num) hpos,(div_lt_one hpos).mpr hx⟩
  let z := scale t p
  have hz : openSquare S z := open_segment_zero S h0 hp ⟨ht.1.le,ht.2⟩
  have hzx : |z.1|=1/2 := by
    dsimp [z,scale]
    rw [abs_mul,abs_of_pos ht.1]
    exact div_mul_cancel₀ _ (ne_of_gt hpos)
  have hzy : |z.2|<1 := by
    dsimp [z,scale]
    rw [abs_mul,abs_of_pos ht.1]
    nlinarith [abs_nonneg p.2]
  have hcl (i : Fin 4) := disjoint_open_closed S (axisSquare (sideCenter i)) (hwalls i) z
  by_cases hx0 : 0≤z.1 <;> by_cases hy0 : 0≤z.2
  · have hxx : z.1=1/2 := by simpa [abs_of_nonneg hx0] using hzx
    apply hcl 1
    refine ⟨hz,?_⟩
    norm_num [sideCenter,axisSquare,closedSquare,localX,localY,hxx]
    exact abs_le.mpr ⟨by linarith,by rw [abs_of_nonneg hy0] at hzy; linarith⟩
  · have hxx : z.1=1/2 := by simpa [abs_of_nonneg hx0] using hzx
    apply hcl 0
    refine ⟨hz,?_⟩
    norm_num [sideCenter,axisSquare,closedSquare,localX,localY,hxx]
    exact abs_le.mpr ⟨by rw [abs_of_neg (lt_of_not_ge hy0)] at hzy; linarith,by linarith⟩
  · have hxx : z.1= -(1/2 : ℝ) := by
      rw [abs_of_neg (lt_of_not_ge hx0)] at hzx
      linarith
    apply hcl 3
    refine ⟨hz,?_⟩
    norm_num [sideCenter,axisSquare,closedSquare,localX,localY,hxx]
    exact abs_le.mpr ⟨by linarith,by rw [abs_of_nonneg hy0] at hzy; linarith⟩
  · have hxx : z.1= -(1/2 : ℝ) := by
      rw [abs_of_neg (lt_of_not_ge hx0)] at hzx
      linarith
    apply hcl 2
    refine ⟨hz,?_⟩
    norm_num [sideCenter,axisSquare,closedSquare,localX,localY,hxx]
    exact abs_le.mpr ⟨by rw [abs_of_neg (lt_of_not_ge hy0)] at hzy; linarith,by linarith⟩

lemma containing_center_y (S : UnitSquare) (h0 : openSquare S (0,0)) : |S.center.2|<1 := by
  have hu := frame_norm S (sub S.center (0,0))
  rw [frame_centerX,frame_centerY] at hu
  have hx := abs_lt.mp h0.1
  have hy := abs_lt.mp h0.2
  have hx2 : (localX S (0,0))^2<1/4 := by nlinarith
  have hy2 : (localY S (0,0))^2<1/4 := by nlinarith
  apply abs_lt.mpr
  dsimp [normSq,sub] at hu
  constructor <;> nlinarith [sq_nonneg S.center.1]

lemma axis_frame_open (S : UnitSquare) (haxis : S.cosine=0 ∨ S.sine=0) (p : Point) :
    openSquare S p ↔ OpenRect S.center p.1 p.2 := by
  rcases haxis with hc | hs
  · have ha : |S.sine|=1 := by nlinarith [S.unit,abs_nonneg S.sine,sq_abs S.sine]
    have hx : localX S p=(p.2-S.center.2)*S.sine := by dsimp [localX]; rw [hc]; ring
    have hy : localY S p= -((p.1-S.center.1)*S.sine) := by dsimp [localY]; rw [hc]; ring
    simp only [openSquare,OpenRect,hx,hy,abs_mul,abs_neg,ha,mul_one,and_comm]
  · have ha : |S.cosine|=1 := by nlinarith [S.unit,abs_nonneg S.cosine,sq_abs S.cosine]
    have hx : localX S p=(p.1-S.center.1)*S.cosine := by dsimp [localX]; rw [hs]; ring
    have hy : localY S p=(p.2-S.center.2)*S.cosine := by dsimp [localY]; rw [hs]; ring
    simp only [openSquare,OpenRect,hx,hy,abs_mul,ha,mul_one]

/-- The strip forces a containing unit square to be geometrically axis aligned. -/
theorem containing_strip_rigid (S : UnitSquare) (h0 : openSquare S (0,0))
    (hstrip : ∀p,openSquare S p → |p.2|<1 → |p.1|≤1/2) :
    S.center.1=0 ∧ (S.cosine=0 ∨ S.sine=0) ∧
    ∀p,openSquare S p ↔ OpenRect (0,S.center.2) p.1 p.2 := by
  have hcy := containing_center_y S h0
  have haxis : S.cosine=0 ∨ S.sine=0 := by
    by_contra hn
    push_neg at hn
    have hc0 : 0<|S.cosine| := abs_pos.mpr hn.1
    have hs0 : 0<|S.sine| := abs_pos.mpr hn.2
    have hc1 : |S.cosine|<1 := by nlinarith [S.unit,sq_abs S.cosine,sq_abs S.sine]
    have hs1 : |S.sine|<1 := by nlinarith [S.unit,sq_abs S.cosine,sq_abs S.sine]
    let M := max |S.cosine| |S.sine|
    let r := 1/(1+M)
    have hM : 0<M ∧ M<1 := ⟨hc0.trans_le (le_max_left _ _),max_lt hc1 hs1⟩
    have hr0 : 0<r := div_pos (by norm_num) (by linarith)
    have hre : (1+M)*r=1 := by dsimp [r]; field_simp; ring
    have hr : 1/2<r := by nlinarith
    have hMr : M*r<1/2 := by nlinarith
    have hcr : |S.cosine|*r<1/2 :=
      (mul_le_mul_of_nonneg_right (le_max_left _ _) hr0.le).trans_lt hMr
    have hsr : |S.sine|*r<1/2 :=
      (mul_le_mul_of_nonneg_right (le_max_right _ _) hr0.le).trans_lt hMr
    have hright : openSquare S (S.center.1+r,S.center.2) := by
      have hx : localX S (S.center.1+r,S.center.2)=S.cosine*r := by dsimp [localX]; ring
      have hy : localY S (S.center.1+r,S.center.2)= -S.sine*r := by dsimp [localY]; ring
      simpa only [openSquare,hx,hy,abs_mul,abs_neg,abs_of_pos hr0] using And.intro hcr hsr
    have hleft : openSquare S (S.center.1-r,S.center.2) := by
      have hx : localX S (S.center.1-r,S.center.2)= -(S.cosine*r) := by dsimp [localX]; ring
      have hy : localY S (S.center.1-r,S.center.2)=S.sine*r := by dsimp [localY]; ring
      simpa only [openSquare,hx,hy,abs_mul,abs_neg,abs_of_pos hr0] using And.intro hcr hsr
    have hR := (abs_le.mp (hstrip _ hright hcy)).2
    have hL := (abs_le.mp (hstrip _ hleft hcy)).1
    linarith
  have hopen := axis_frame_open S haxis
  have hcx : S.center.1=0 := by
    have hright : S.center.1+1/2≤1/2 := by
      apply affine_endpoint_le (A := S.center.1)
      intro t ht0 ht1
      have hp : openSquare S (S.center.1+t/2,S.center.2) := by
        apply (hopen _).mpr
        simp only [OpenRect]
        constructor <;> apply abs_lt.mpr <;> constructor <;> linarith
      have hh := (abs_le.mp (hstrip _ hp hcy)).2
      nlinarith
    have hleft : -S.center.1+1/2≤1/2 := by
      apply affine_endpoint_le (A := -S.center.1)
      intro t ht0 ht1
      have hp : openSquare S (S.center.1-t/2,S.center.2) := by
        apply (hopen _).mpr
        simp only [OpenRect]
        constructor <;> apply abs_lt.mpr <;> constructor <;> linarith
      have hh := (abs_le.mp (hstrip _ hp hcy)).1
      nlinarith
    linarith
  refine ⟨hcx,haxis,?_⟩
  intro p
  simpa only [OpenRect,hcx] using hopen p

end SquaresInCircles.Seven.Equality
