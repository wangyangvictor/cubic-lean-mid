import TranslatedDepthSeven.RankSevenDegreeOneLineIncidence

/-!
# The literal low directions on the fixed cone and in the projective star

This file uses the complete-line incidence theorem, without a line-counting
interface.  A primitive direction of one actual degree-one occurrence is a
rational point of the original fixed projective cone.  At low height it is
therefore one of the rational projective points counted by Salberger.  The
same direction is also a point of the equation-level projective star based
at the corresponding point of the original cone; this is the exact source
incidence needed before the separate proper-piece construction.
-/

namespace TranslatedDepthSeven

noncomputable section

open MvPolynomial Published
open scoped LinearAlgebra.Projectivization

attribute [local instance] MvPolynomial.gradedAlgebra

local instance rankSevenLowDirectionProjectiveDecidableEq :
    DecidableEq (Projectivization ℚ (Fin 13 → ℚ)) := Classical.decEq _

set_option maxHeartbeats 8000000

/-- A primitive integral common zero, with its actual primitive height, is
a point of the fixed rational projective variety.  The proof passes through
the projectivized finite equation family, so it is valid for the arbitrary
representative chosen by `Projectivization.rep`. -/
theorem primitiveDirection_mem_rationalProjectivePoints_of_commonZero
    (equations : Finset (MvPolynomial (Fin 13) ℤ))
    (hhomogeneous : ∀ f ∈ equations, ∃ e : ℕ, f.IsHomogeneous e)
    (h : IntVector 13) (hprimitive : PrimitiveDirection h)
    (hzero : IntegralCommonZero equations h) (B : ℝ)
    (hheight : (directionHeight h : ℝ) ≤ B) :
    integralProjectiveClassOrFirstRankSeven h ∈
      rationalProjectivePoints (rationalDepthSevenEquationIdeal equations) B := by
  classical
  have hh : h ≠ 0 := by
    intro hz
    obtain ⟨i, hi⟩ := hprimitive.exists_ne_zero
    exact hi (congrFun hz i)
  let degree : MvPolynomial (Fin 13) ℤ → ℕ := fun f ↦
    if hf : f ∈ equations then Classical.choose (hhomogeneous f hf) else 0
  have hdegree : ∀ f ∈ equations, f.IsHomogeneous (degree f) := by
    intro f hf
    simp only [degree, dif_pos hf]
    exact Classical.choose_spec (hhomogeneous f hf)
  have hcone : integralProjectiveClass h hh ∈
      integralProjectiveConeZeroSetOver ℚ equations := by
    apply (mk_mem_integralProjectiveConeZeroSetOver_iff
      equations degree hdegree (fun i ↦ (h i : ℚ))
        (intCast_ne_zero (K := ℚ) hh)).2
    exact intCast_mem_integralAffineConeZeroSetOver equations hzero
  have hrepCone : (integralProjectiveClass h hh).rep ∈
      integralAffineConeZeroSetOver ℚ equations :=
    (mem_integralProjectiveConeZeroSetOver_iff_rep
      equations degree hdegree (integralProjectiveClass h hh)).1 hcone
  rw [integralProjectiveClassOrFirstRankSeven, dif_pos hh]
  constructor
  · have hrepIdeal : (integralProjectiveClass h hh).rep ∈
        affineIdealZeroLocus (rationalDepthSevenEquationIdeal equations) := by
      rw [rationalDepthSevenEquationIdeal,
        affineIdealZeroLocus_finiteEquationIdeal]
      intro g hg
      rw [rationalizedEquationFinset, Finset.mem_image] at hg
      obtain ⟨f, hf, rfl⟩ := hg
      exact hrepCone f hf
    exact hrepIdeal
  · rw [primitiveRationalVectorHeight_integralProjectiveClass_eq_directionHeight
      hprimitive hh]
    exact hheight

/-- The exact finite set of low projective directions from the literal line
ledger is contained in the height-bounded rational point set of the fixed
original cone, once each active primitive direction has been shown to
satisfy the original equations. -/
theorem activeLowProjectiveDirections_subset_fixedConePoints
    { ι : Type*} [Fintype ι]
    (J : ι → Ideal (MvPolynomial (Fin 13) ℝ))
    (Y : ι → Finset (IntVector 13))
    (equations : Finset (MvPolynomial (Fin 13) ℤ))
    (hhomogeneous : ∀ f ∈ equations, ∃ e : ℕ, f.IsHomogeneous e)
    (lineDirection : TaggedLinearComponent J → IntVector 13)
    (T : NNReal)
    (hprimitive : ∀ o ∈ activeTaggedLinearComponents J Y,
      PrimitiveDirection (lineDirection o))
    (hzero : ∀ o ∈ activeTaggedLinearComponents J Y,
      IntegralCommonZero equations (lineDirection o)) :
    ↑(activeLowProjectiveDirections J Y lineDirection T) ⊆
      rationalProjectivePoints (rationalDepthSevenEquationIdeal equations)
        (xScale T : ℝ) := by
  intro h hh
  obtain ⟨o, ho, rfl⟩ := Finset.mem_image.mp hh
  have hoActive : o ∈ activeTaggedLinearComponents J Y :=
    (Finset.mem_filter.mp ho).1
  have hoHeight : directionHeight (lineDirection o) ≤
      lowDirectionNaturalRadius T := (Finset.mem_filter.mp ho).2
  apply primitiveDirection_mem_rationalProjectivePoints_of_commonZero
    equations hhomogeneous (lineDirection o) (hprimitive o hoActive)
      (hzero o hoActive) (xScale T : ℝ)
  calc
    (directionHeight (lineDirection o) : ℝ) ≤
        (lowDirectionNaturalRadius T : ℝ) := by exact_mod_cast hoHeight
    _ ≤ (xScale T : ℝ) := by
      simpa [lowDirectionNaturalRadius] using
        (Nat.floor_le (a := xScale T) (show 0 ≤ xScale T by positivity))

/-! ## The exact projective-star source incidence -/

/-- If the integral line with direction `m h` lies on the original
homogeneous equations and `m ≠ 0`, then the projective class of `h` lies in
the equation-level projective star at the displayed base point.  This is
just the polynomial identity principle followed by the rational change of
parameter `t ↦ t/m`. -/
theorem primitiveDirection_mem_projectiveStar_of_scaledIntegralLine
    (equations : Finset (MvPolynomial (Fin 13) ℤ))
    (degree : MvPolynomial (Fin 13) ℤ → ℕ)
    (hdegree : ∀ f ∈ equations, f.IsHomogeneous (degree f))
    (base h : IntVector 13) (m : ℕ) (hm : 0 < m)
    (hprimitive : PrimitiveDirection h)
    (hline : ∀ t : ℤ, IntegralCommonZero equations
      (fun i ↦ base i + t * ((m : ℤ) * h i))) :
    integralProjectiveClassOrFirstRankSeven h ∈
      integralProjectiveStarLocus equations degree base := by
  classical
  have hh : h ≠ 0 := by
    intro hz
    obtain ⟨i, hi⟩ := hprimitive.exists_ne_zero
    exact hi (congrFun hz i)
  rw [integralProjectiveClassOrFirstRankSeven, dif_pos hh]
  apply (mk_mem_integralProjectiveStarLocus_iff equations degree base hdegree
    (fun i ↦ (h i : ℚ)) (intCast_ne_zero (K := ℚ) hh)).2
  intro f hf t
  let scaledDirection : IntVector 13 := fun i ↦ (m : ℤ) * h i
  have hpoly : linePolynomial f base scaledDirection = 0 :=
    Polynomial.zero_of_eval_zero _ fun u ↦ by
      rw [linePolynomial_eval]
      exact hline u f hf
  have hvector :
      (fun i ↦ (base i : ℚ) + t * (h i : ℚ)) =
        (fun i ↦ (base i : ℚ) +
          (t / (m : ℚ)) * (scaledDirection i : ℚ)) := by
    funext i
    simp only [scaledDirection, Int.cast_mul, Int.cast_natCast]
    field_simp [show (m : ℚ) ≠ 0 by exact_mod_cast hm.ne']
  rw [hvector, ← eval_map_linePolynomial_at_rat,
    hpoly, Polynomial.map_zero, Polynomial.eval_zero]

/-- The symmetric form of the preceding line incidence.  If the integral
line through `base` in direction `m h` lies on the homogeneous cone, then
every nonzero point of that line, and in particular `base`, belongs to the
projective star whose centre is `[h]`.

This is the orientation needed when occurrences with a common projective
direction are grouped: the common direction is the centre of one fixed
star, while the original points supplied by all occurrences lie on that
star. -/
theorem basePoint_mem_projectiveStar_of_scaledIntegralLine
    (equations : Finset (MvPolynomial (Fin 13) ℤ))
    (degree : MvPolynomial (Fin 13) ℤ → ℕ)
    (hdegree : ∀ f ∈ equations, f.IsHomogeneous (degree f))
    (base h : IntVector 13) (m : ℕ) (hm : 0 < m)
    (hbase : base ≠ 0)
    (hline : ∀ t : ℤ, IntegralCommonZero equations
      (fun i ↦ base i + t * ((m : ℤ) * h i))) :
    integralProjectiveClass base hbase ∈
      integralProjectiveStarLocus equations degree h := by
  classical
  apply (mk_mem_integralProjectiveStarLocus_iff equations degree h hdegree
    (fun i ↦ (base i : ℚ)) (intCast_ne_zero (K := ℚ) hbase)).2
  intro f hf t
  let scaledDirection : IntVector 13 := fun i ↦ (m : ℤ) * h i
  have hspan := rationalSpanPoint_mem_integralAffineConeZeroSetOver
    equations degree base scaledDirection hdegree
      (fun f hf u ↦ hline u f hf) t ((m : ℚ)⁻¹)
  have hmQ : (m : ℚ) ≠ 0 := by exact_mod_cast hm.ne'
  have hvector :
      (fun i ↦ t * (base i : ℚ) + (m : ℚ)⁻¹ * (scaledDirection i : ℚ)) =
        (fun i ↦ (h i : ℚ) + t * (base i : ℚ)) := by
    funext i
    simp only [scaledDirection, Int.cast_mul, Int.cast_natCast]
    field_simp [hmQ]
    ring
  rw [hvector] at hspan
  exact hspan f hf

/-- The explicit equation-level star depends only on the projective class
of its centre.  This version records the elementary proportional-coordinate
calculation used below, rather than hiding it behind an abstract projective
star object. -/
theorem integralProjectiveStarLocus_eq_of_proportional_centers
    {n : ℕ}
    (equations : Finset (MvPolynomial (Fin n) ℤ))
    (degree : MvPolynomial (Fin n) ℤ → ℕ)
    (hdegree : ∀ f ∈ equations, f.IsHomogeneous (degree f))
    (h k : IntVector n) (q : ℚ) (hq : q ≠ 0)
    (hproportional : ∀ i, (k i : ℚ) = q * (h i : ℚ)) :
    integralProjectiveStarLocus equations degree h =
      integralProjectiveStarLocus equations degree k := by
  classical
  ext P
  let z : Fin n → ℚ := P.rep
  have hz : z ≠ 0 := P.rep_nonzero
  have hPmk : Projectivization.mk ℚ z hz = P := Projectivization.mk_rep P
  rw [← hPmk,
    mk_mem_integralProjectiveStarLocus_iff equations degree h hdegree z hz,
    mk_mem_integralProjectiveStarLocus_iff equations degree k hdegree z hz]
  constructor
  · intro hh f hf t
    have hzero := hh f hf (t / q)
    let fQ : MvPolynomial (Fin n) ℚ :=
      MvPolynomial.map (Int.castRingHom ℚ) f
    have hfQ : fQ.IsHomogeneous (degree f) := (hdegree f hf).map _
    have hscaled := eval_smul_of_isHomogeneous fQ
      (fun i ↦ (h i : ℚ) + (t / q) * z i) q (degree f) hfQ
    have hvector :
        (fun i ↦ q * ((h i : ℚ) + (t / q) * z i)) =
          (fun i ↦ (k i : ℚ) + t * z i) := by
      funext i
      rw [hproportional i]
      field_simp [hq]
    change MvPolynomial.eval
      (fun i ↦ (k i : ℚ) + t * z i) fQ = 0
    rw [← hvector, hscaled, hzero, mul_zero]
  · intro hk f hf t
    have hzero := hk f hf (q * t)
    let fQ : MvPolynomial (Fin n) ℚ :=
      MvPolynomial.map (Int.castRingHom ℚ) f
    have hfQ : fQ.IsHomogeneous (degree f) := (hdegree f hf).map _
    have hscaled := eval_smul_of_isHomogeneous fQ
      (fun i ↦ (k i : ℚ) + (q * t) * z i) q⁻¹ (degree f) hfQ
    have hvector :
        (fun i ↦ q⁻¹ * ((k i : ℚ) + (q * t) * z i)) =
          (fun i ↦ (h i : ℚ) + t * z i) := by
      funext i
      rw [hproportional i]
      field_simp [hq]
    change MvPolynomial.eval
      (fun i ↦ (h i : ℚ) + t * z i) fQ = 0
    rw [← hvector, hscaled, hzero, mul_zero]

/-- Specialization to the literal normalized line produced by the
rank-seven record construction.  Its image has base
`x₀ + p.m * base` and direction `p.m * direction`; the preceding theorem
removes the harmless nonzero scalar from the projective direction. -/
theorem rankSevenDegreeOne_activeDirection_mem_projectiveStar
    (p : Parameters) (x₀ : IntVector 13)
    (equations : Finset (MvPolynomial (Fin 13) ℤ))
    (degree : MvPolynomial (Fin 13) ℤ → ℕ)
    (hdegree : ∀ f ∈ equations, f.IsHomogeneous (degree f))
    { ι : Type*} [Fintype ι]
    (J : ι → Ideal (MvPolynomial (Fin 13) ℝ))
    (Y : ι → Finset (IntVector 13))
    (base direction : TaggedLinearComponent J → IntVector 13)
    (hprimitive : ∀ o ∈ activeTaggedLinearComponents J Y,
      PrimitiveDirection (direction o))
    (hline : ∀ o ∈ activeTaggedLinearComponents J Y, ∀ t : ℤ,
      IntegralCommonZero equations
        (integralAffineMap x₀
          (fun i ↦ base o i + t * direction o i) p.m))
    (o : TaggedLinearComponent J)
    (ho : o ∈ activeTaggedLinearComponents J Y) :
    integralProjectiveClassOrFirstRankSeven (direction o) ∈
      integralProjectiveStarLocus equations degree
        (integralAffineMap x₀ (base o) p.m) := by
  apply primitiveDirection_mem_projectiveStar_of_scaledIntegralLine
    equations degree hdegree (integralAffineMap x₀ (base o) p.m)
      (direction o) p.m p.hm (hprimitive o ho)
  intro t
  have ht := hline o ho t
  rw [show (fun i ↦ integralAffineMap x₀ (base o) p.m i +
        t * ((p.m : ℤ) * direction o i)) =
      integralAffineMap x₀
        (fun i ↦ base o i + t * direction o i) p.m by
    funext i
    simp [integralAffineMap]
    ring]
  exact ht

/-- The exact output furnished to the remaining proper-piece argument by
the complete-line ledger: all low directions lie on the one fixed
height-bounded projective cone, and every active occurrence direction lies
in the projective star at its explicitly displayed original base point. -/
theorem rankSevenDegreeOne_lowDirection_source_specialization
    (p : Parameters) (x₀ : IntVector 13)
    (equations : Finset (MvPolynomial (Fin 13) ℤ))
    (hhomogeneous : ∀ f ∈ equations, ∃ e : ℕ, f.IsHomogeneous e)
    (degree : MvPolynomial (Fin 13) ℤ → ℕ)
    (hdegree : ∀ f ∈ equations, f.IsHomogeneous (degree f))
    { ι : Type*} [Fintype ι]
    (J : ι → Ideal (MvPolynomial (Fin 13) ℝ))
    (Y : ι → Finset (IntVector 13))
    (base direction : TaggedLinearComponent J → IntVector 13)
    (hprimitive : ∀ o ∈ activeTaggedLinearComponents J Y,
      PrimitiveDirection (direction o))
    (hline : ∀ o ∈ activeTaggedLinearComponents J Y, ∀ t : ℤ,
      IntegralCommonZero equations
        (integralAffineMap x₀
          (fun i ↦ base o i + t * direction o i) p.m))
    (hzero : ∀ o ∈ activeTaggedLinearComponents J Y,
      IntegralCommonZero equations (direction o)) :
    ↑(activeLowProjectiveDirections J Y direction
        (surfaceTangentRealSide p)) ⊆
        rationalProjectivePoints (rationalDepthSevenEquationIdeal equations)
          (xScale (surfaceTangentRealSide p) : ℝ) ∧
      ∀ o ∈ activeTaggedLinearComponents J Y,
        integralProjectiveClassOrFirstRankSeven (direction o) ∈
          integralProjectiveStarLocus equations degree
            (integralAffineMap x₀ (base o) p.m) := by
  constructor
  · exact activeLowProjectiveDirections_subset_fixedConePoints
      J Y equations hhomogeneous direction (surfaceTangentRealSide p)
        hprimitive hzero
  · intro o ho
    exact rankSevenDegreeOne_activeDirection_mem_projectiveStar
      p x₀ equations degree hdegree J Y base direction hprimitive hline o ho

end

end TranslatedDepthSeven
