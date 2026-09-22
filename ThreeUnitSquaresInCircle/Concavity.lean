import ThreeUnitSquaresInCircle.RealPolynomial

/-!
Concavity of the certificate polynomial on the angle domain, proved by
restricting to an arbitrary line segment and bounding the second derivative.
-/
noncomputable section
open scoped BigOperators
namespace ThreeUnitSquaresInCircle.Cert
open RatData

def domain : Set Point := {x | AngleDomain.Domain x.1 x.2}

lemma domain_convex : Convex ℝ domain := by
  intro x hx y hy u v hu hv huv
  rcases hx with ⟨hx0,hx1,hx2⟩
  rcases hy with ⟨hy0,hy1,hy2⟩
  change 0 ≤ u*x.1+v*y.1 ∧
    2*(u*x.1+v*y.1) ≤ u*x.2+v*y.2 ∧
    2*(u*x.2+v*y.2)-(u*x.1+v*y.1) ≤ 1/2
  refine ⟨add_nonneg (mul_nonneg hu hx0) (mul_nonneg hv hy0), ?_, ?_⟩
  · nlinarith [mul_nonneg hu (sub_nonneg.mpr hx1),
      mul_nonneg hv (sub_nonneg.mpr hy1)]
  · nlinarith [mul_nonneg hu (sub_nonneg.mpr hx2),
      mul_nonneg hv (sub_nonneg.mpr hy2)]

lemma corners_in_domain (p : Corner) : cornerPoint p ∈ domain := by
  cases p <;> norm_num [domain, cornerPoint, AngleDomain.Domain,
    AngleDomain.O, AngleDomain.V, AngleDomain.W, AngleDomain.P, AngleDomain.Z]

def segmentPoint (x y : Point) (t : ℝ) : Point := (1-t) • x + t • y

def segmentValue (c : Certificate) (x y : Point) (t : ℝ) : ℝ :=
  polynomial c (segmentPoint x y t)

def segmentSlope (x y : Point) : Fin 3 → ℝ :=
  ![Real.pi*(y.1-x.1), Real.pi*(y.2-x.2),
    Real.pi*(y.2-x.2)-Real.pi*(y.1-x.1)]

def segmentDeriv (c : Certificate) (x y : Point) (t : ℝ) : ℝ :=
  ∑ e, segmentSlope x y e *
    (-(A c e : ℝ) * Real.sin (arguments (segmentPoint x y t) e) +
      (B c e : ℝ) * Real.cos (arguments (segmentPoint x y t) e))

def segmentDeriv2 (c : Certificate) (x y : Point) (t : ℝ) : ℝ :=
  -(∑ e, curvature c (segmentPoint x y t) e * (segmentSlope x y e)^2)

lemma arguments_segment (x y : Point) (t : ℝ) (e : Fin 3) :
    arguments (segmentPoint x y t) e = arguments x e + segmentSlope x y e*t := by
  fin_cases e <;>
    simp [arguments, segmentPoint, segmentSlope, smul_eq_mul] <;> ring

lemma harmonic_deriv (A B p w t : ℝ) :
    HasDerivAt (fun z : ℝ => A*Real.cos (p+w*z)+B*Real.sin (p+w*z))
      (w*(-A*Real.sin (p+w*t)+B*Real.cos (p+w*t))) t := by
  have hd : HasDerivAt (fun z : ℝ => p+w*z) w t := by
    simpa using ((hasDerivAt_id t).const_mul w).const_add p
  convert (hd.cos.const_mul A).add (hd.sin.const_mul B) using 1; ring

lemma harmonic_deriv2 (A B p w t : ℝ) :
    HasDerivAt (fun z : ℝ => w*(-A*Real.sin (p+w*z)+B*Real.cos (p+w*z)))
      (-(A*Real.cos (p+w*t)+B*Real.sin (p+w*t))*w^2) t := by
  have hd : HasDerivAt (fun z : ℝ => p+w*z) w t := by
    simpa using ((hasDerivAt_id t).const_mul w).const_add p
  convert ((hd.sin.const_mul (-A)).add (hd.cos.const_mul B)).const_mul w
    using 1; ring

lemma segmentValue_hasDerivAt (c : Certificate) (x y : Point) (t : ℝ) :
    HasDerivAt (segmentValue c x y) (segmentDeriv c x y t) t := by
  have h0 := harmonic_deriv (A c 0) (B c 0) (arguments x 0) (segmentSlope x y 0) t
  have h1 := harmonic_deriv (A c 1) (B c 1) (arguments x 1) (segmentSlope x y 1) t
  have h2 := harmonic_deriv (A c 2) (B c 2) (arguments x 2) (segmentSlope x y 2) t
  convert ((h0.add h1).add h2).const_add (c.coeff 0 : ℝ) using 1
  · funext z
    simp [segmentValue, polynomial, Fin.sum_univ_succ, arguments_segment]
    ring
  · simp [segmentDeriv, Fin.sum_univ_succ, arguments_segment]
    ring

lemma segmentDeriv_hasDerivAt (c : Certificate) (x y : Point) (t : ℝ) :
    HasDerivAt (segmentDeriv c x y) (segmentDeriv2 c x y t) t := by
  have h0 := harmonic_deriv2 (A c 0) (B c 0) (arguments x 0) (segmentSlope x y 0) t
  have h1 := harmonic_deriv2 (A c 1) (B c 1) (arguments x 1) (segmentSlope x y 1) t
  have h2 := harmonic_deriv2 (A c 2) (B c 2) (arguments x 2) (segmentSlope x y 2) t
  convert (h0.add h1).add h2 using 1
  · funext z
    simp [segmentDeriv, Fin.sum_univ_succ, arguments_segment]
    ring
  · simp [segmentDeriv2, curvature, Fin.sum_univ_succ, arguments_segment]
    ring

lemma segment_in_domain {x y : Point} (hx : x ∈ domain) (hy : y ∈ domain)
    {t : ℝ} (ht : t ∈ Set.Icc (0:ℝ) 1) : segmentPoint x y t ∈ domain := by
  exact domain_convex hx hy (sub_nonneg.mpr ht.2) ht.1 (by ring)

lemma segmentDeriv2_nonpos (c : Certificate) (hc : arithmeticValid c)
    {x y : Point} (hx : x ∈ domain) (hy : y ∈ domain)
    {t : ℝ} (ht : t ∈ Set.Icc (0:ℝ) 1) : segmentDeriv2 c x y t ≤ 0 := by
  have h := curvature_form_nonneg c hc (segment_in_domain hx hy ht)
    (Real.pi*(y.1-x.1)) (Real.pi*(y.2-x.2))
  have h' := neg_nonpos.mpr h
  simp [segmentDeriv2, segmentSlope, Fin.sum_univ_succ]
  linarith [h]

/-- Concavity on the full two-dimensional angle domain, via every line segment. -/
theorem polynomial_concave (c : Certificate) (hc : arithmeticValid c) :
    ConcaveOn ℝ domain (polynomial c) := by
  refine ⟨domain_convex, ?_⟩
  intro x hx y hy u v hu hv huv
  have hf : ContinuousOn (segmentValue c x y) (Set.Icc (0:ℝ) 1) := by
    apply Continuous.continuousOn
    unfold segmentValue polynomial segmentPoint arguments
    fun_prop
  have hconc : ConcaveOn ℝ (Set.Icc (0:ℝ) 1) (segmentValue c x y) := by
    apply concaveOn_of_hasDerivWithinAt2_nonpos (convex_Icc 0 1) hf
      (f' := segmentDeriv c x y) (f'' := segmentDeriv2 c x y)
    · intro t _
      exact (segmentValue_hasDerivAt c x y t).hasDerivWithinAt
    · intro t _
      exact (segmentDeriv_hasDerivAt c x y t).hasDerivWithinAt
    · intro t ht
      exact segmentDeriv2_nonpos c hc hx hy (interior_subset ht)
  have hj := hconc.2 (show (0:ℝ) ∈ Set.Icc 0 1 by norm_num)
    (show (1:ℝ) ∈ Set.Icc 0 1 by norm_num) hu hv huv
  have hu' : u = 1-v := by linarith
  simpa [segmentValue, segmentPoint, hu', smul_eq_mul] using hj

/-- The superlevel set of a concave function is convex. -/
lemma superlevel_convex (c : Certificate) (hc : arithmeticValid c) :
    Convex ℝ {x : Point | x ∈ domain ∧ targetSq ≤ polynomial c x} := by
  intro x hx y hy u v hu hv huv
  refine ⟨domain_convex hx.1 hy.1 hu hv huv, ?_⟩
  have hj := (polynomial_concave c hc).2 hx.1 hy.1 hu hv huv
  have hm := add_le_add (mul_le_mul_of_nonneg_left hx.2 hu)
    (mul_le_mul_of_nonneg_left hy.2 hv)
  change targetSq ≤ polynomial c (u • x + v • y)
  change u * polynomial c x + v * polynomial c y ≤ _ at hj
  -- u*targetSq + v*targetSq = targetSq since u + v = 1
  have hT : u * targetSq + v * targetSq = targetSq := by
    have : (u + v) * targetSq = 1 * targetSq := by rw [huv]
    linarith [this]
  linarith

/-- Extends checked endpoint bounds to their entire convex hull. -/
theorem certificate_on_hull (c : Certificate) (hc : arithmeticValid c)
    (x : Point)
    (hx : x ∈ convexHull ℝ (cornerPoint '' {p | p ∈ c.corners})) :
    targetSq ≤ polynomial c x := by
  have hincl : convexHull ℝ (cornerPoint '' {p | p ∈ c.corners}) ⊆
      {x : Point | x ∈ domain ∧ targetSq ≤ polynomial c x} := by
    apply convexHull_min
    · rintro _ ⟨p,hp,rfl⟩
      exact ⟨corners_in_domain p, checked_corner_lower c hc p hp⟩
    · exact superlevel_convex c hc
  exact (hincl hx).2

/-- Barycentric coordinates from AngleDomain give actual convex-hull membership. -/
lemma triangle_subset_hull (ps : List Corner) (p q r : Corner)
    (hp : p ∈ ps) (hq : q ∈ ps) (hr : r ∈ ps)
    {x : Point}
    (hx : AngleDomain.InTriangle (cornerPoint p) (cornerPoint q) (cornerPoint r) x) :
    x ∈ convexHull ℝ (cornerPoint '' {s | s ∈ ps}) := by
  let K := convexHull ℝ (cornerPoint '' {s | s ∈ ps})
  have hK : Convex ℝ K := convex_convexHull ℝ _
  have hpK : cornerPoint p ∈ K := subset_convexHull ℝ _ ⟨p,hp,rfl⟩
  have hqK : cornerPoint q ∈ K := subset_convexHull ℝ _ ⟨q,hq,rfl⟩
  have hrK : cornerPoint r ∈ K := subset_convexHull ℝ _ ⟨r,hr,rfl⟩
  rcases hx with ⟨u,v,w,hu,hv,hw,hs,hx,hy⟩
  by_cases hz : v+w = 0
  · have hv0 : v=0 := by linarith
    have hw0 : w=0 := by linarith
    have hu1 : u=1 := by linarith
    have heq : x = cornerPoint p := by
      apply Prod.ext
      · simp_all
      · simp_all
    simpa [heq] using hpK
  · have hpos : 0 < v+w := lt_of_le_of_ne (add_nonneg hv hw) (Ne.symm hz)
    have hm : (v/(v+w)) • cornerPoint q + (w/(v+w)) • cornerPoint r ∈ K :=
      hK hqK hrK (div_nonneg hv hpos.le) (div_nonneg hw hpos.le)
        (by field_simp)
    have hout := hK hpK hm hu (add_nonneg hv hw) (by linarith)
    have heq : u • cornerPoint p + (v+w) •
        ((v/(v+w)) • cornerPoint q + (w/(v+w)) • cornerPoint r) = x := by
      apply Prod.ext
      · change u*(cornerPoint p).1 + (v+w)*
          ((v/(v+w))*(cornerPoint q).1+(w/(v+w))*(cornerPoint r).1)=x.1
        rw [hx]; field_simp; ring
      · change u*(cornerPoint p).2 + (v+w)*
          ((v/(v+w))*(cornerPoint q).2+(w/(v+w))*(cornerPoint r).2)=x.2
        rw [hy]; field_simp; ring
    exact heq ▸ hout

end ThreeUnitSquaresInCircle.Cert
