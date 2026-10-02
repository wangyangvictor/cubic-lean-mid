import TranslatedDepthSeven.AffineChartProjectionBoundaryTopPart
import TranslatedDepthSeven.BoundedIntegralDistinguishedNormalizationInternal
import TranslatedDepthSeven.FieldPolynomialKrullDimension
import TranslatedDepthSeven.SurjectiveDomainDimensionInternal

/-!
# Restricting a distinguished normalization to the boundary

A homogeneous linear normalization which literally retains `X₀` is
automatically finite after setting `X₀ = 0`.  The remaining rows then
normalize the projective boundary.  If that boundary is prime and has the
expected dimension, the restricted map is injective as well.

This removes any need to choose the normalization rows simultaneously on a
projective variety and its boundary.  Only the final primitive coordinate
still has to be chosen simultaneously.
-/

namespace TranslatedDepthSeven

noncomputable section

open MvPolynomial Published

attribute [local instance] MvPolynomial.gradedAlgebra

set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 500000

/-- Setting the first coordinate equal to zero is surjective. -/
theorem rationalSpecializeFirstCoordinate_zero_surjective (n : ℕ) :
    Function.Surjective
      (rationalSpecializeFirstCoordinate (d := n) 0) := by
  intro f
  refine ⟨rename Fin.succ f, ?_⟩
  rw [rationalSpecializeFirstCoordinate, aeval_rename]
  convert aeval_X_left_apply f using 1

/-- The quotient map from a homogeneous source to its boundary at infinity. -/
def projectiveBoundaryQuotientMap {N : ℕ}
    (I : Ideal (MvPolynomial (Fin (N + 1)) ℚ)) :
    (MvPolynomial (Fin (N + 1)) ℚ ⧸ I) →ₐ[ℚ]
      (MvPolynomial (Fin N) ℚ ⧸ projectiveBoundaryIdeal I) :=
  Ideal.quotientMapₐ (projectiveBoundaryIdeal I)
    (rationalSpecializeFirstCoordinate 0) Ideal.le_comap_map

theorem projectiveBoundaryQuotientMap_surjective {N : ℕ}
    (I : Ideal (MvPolynomial (Fin (N + 1)) ℚ)) :
    Function.Surjective (projectiveBoundaryQuotientMap I) := by
  unfold projectiveBoundaryQuotientMap
  exact Ideal.quotientMap_surjective
    (I := projectiveBoundaryIdeal I) (J := I)
    (f := (rationalSpecializeFirstCoordinate 0).toRingHom)
    (H := Ideal.le_comap_map)
    (rationalSpecializeFirstCoordinate_zero_surjective N)

/-- Delete the distinguished row and column from a normalization matrix. -/
def distinguishedNormalizationBoundaryMatrix {N r : ℕ}
    (A : Matrix (Fin (r + 1)) (Fin (N + 1)) ℚ) :
    Matrix (Fin r) (Fin N) ℚ :=
  fun i j ↦ A i.succ j.succ

/-- The normalization map on the boundary induced by the remaining rows. -/
def distinguishedNormalizationBoundaryHom {N r : ℕ}
    (I : Ideal (MvPolynomial (Fin (N + 1)) ℚ))
    (A : Matrix (Fin (r + 1)) (Fin (N + 1)) ℚ) :
    MvPolynomial (Fin r) ℚ →ₐ[ℚ]
      (MvPolynomial (Fin N) ℚ ⧸ projectiveBoundaryIdeal I) :=
  (Ideal.Quotient.mkₐ ℚ (projectiveBoundaryIdeal I)).comp
    (aeval (indexedMatrixRowLinearPolynomial
      (distinguishedNormalizationBoundaryMatrix A)))

/-- Specializing the full normalization at `X₀ = 0` is exactly the
normalization defined by the tail matrix. -/
theorem distinguishedNormalizationBoundaryHom_comp_specialize
    {N r : ℕ}
    (I : Ideal (MvPolynomial (Fin (N + 1)) ℚ))
    (A : Matrix (Fin (r + 1)) (Fin (N + 1)) ℚ)
    (hfirst : ∀ j, A 0 j = if j = 0 then 1 else 0) :
    (distinguishedNormalizationBoundaryHom I A).comp
        (rationalSpecializeFirstCoordinate 0) =
      (projectiveBoundaryQuotientMap I).comp
        ((Ideal.Quotient.mkₐ ℚ I).comp
          (aeval (indexedMatrixRowLinearPolynomial A))) := by
  apply MvPolynomial.algHom_ext
  intro i
  refine Fin.cases ?_ (fun k ↦ ?_) i
  · simp only [AlgHom.comp_apply]
    have hrow : indexedMatrixRowLinearPolynomial A 0 = X 0 := by
      rw [indexedMatrixRowLinearPolynomial, Fin.sum_univ_succ, hfirst 0]
      simp_rw [hfirst]
      simp
    simp [distinguishedNormalizationBoundaryHom,
      projectiveBoundaryQuotientMap, rationalSpecializeFirstCoordinate,
      hrow]
  · simp only [AlgHom.comp_apply]
    simp only [rationalSpecializeFirstCoordinate, aeval_X]
    rw [show projectiveBoundaryQuotientMap I
        (Ideal.Quotient.mkₐ ℚ I
          (indexedMatrixRowLinearPolynomial A k.succ)) =
        Ideal.Quotient.mk (projectiveBoundaryIdeal I)
          (rationalSpecializeFirstCoordinate 0
            (indexedMatrixRowLinearPolynomial A k.succ)) by
      simp [projectiveBoundaryQuotientMap]]
    apply congrArg (Ideal.Quotient.mk (projectiveBoundaryIdeal I))
    rw [indexedMatrixRowLinearPolynomial, Fin.sum_univ_succ]
    simp only [map_add, map_mul]
    simp [rationalSpecializeFirstCoordinate,
      distinguishedNormalizationBoundaryMatrix,
      indexedMatrixRowLinearPolynomial]

/-- Finiteness descends formally to the boundary: compose the original
finite map with the surjective boundary quotient, then remove the
surjective first-coordinate specialization from the source. -/
theorem distinguishedNormalizationBoundaryHom_finite
    {N r : ℕ}
    (I : Ideal (MvPolynomial (Fin (N + 1)) ℚ))
    (A : Matrix (Fin (r + 1)) (Fin (N + 1)) ℚ)
    (hfirst : ∀ j, A 0 j = if j = 0 then 1 else 0)
    (hfinite : ((Ideal.Quotient.mkₐ ℚ I).comp
      (aeval (indexedMatrixRowLinearPolynomial A))).Finite) :
    (distinguishedNormalizationBoundaryHom I A).Finite := by
  have hquotient : (projectiveBoundaryQuotientMap I).Finite :=
    AlgHom.Finite.of_surjective _ (projectiveBoundaryQuotientMap_surjective I)
  have hcomp : ((projectiveBoundaryQuotientMap I).comp
      ((Ideal.Quotient.mkₐ ℚ I).comp
        (aeval (indexedMatrixRowLinearPolynomial A)))).Finite :=
    AlgHom.Finite.comp hquotient hfinite
  refine AlgHom.Finite.of_comp_finite
    (f := rationalSpecializeFirstCoordinate (d := r) 0) ?_
  rw [distinguishedNormalizationBoundaryHom_comp_specialize I A hfirst]
  exact hcomp

/-- A finite map from an `r`-variable polynomial algebra to an
`r`-dimensional affine domain is injective. -/
theorem finitePolynomialAlgHom_injective_of_ringKrullDim_eq
    {K A : Type*} [Field K] [CharZero K]
    [CommRing A] [IsDomain A] [Algebra K A]
    {r : ℕ} (g : MvPolynomial (Fin r) K →ₐ[K] A)
    (hfinite : g.Finite)
    (hdim : ringKrullDim A = (r : WithBot ℕ∞)) :
    Function.Injective g := by
  let P := RingHom.ker g.toRingHom
  letI : P.IsPrime := RingHom.ker_isPrime g
  let q : (MvPolynomial (Fin r) K ⧸ P) →ₐ[K] A := Ideal.kerLiftAlg g
  letI : Algebra (MvPolynomial (Fin r) K ⧸ P) A := q.toRingHom.toAlgebra
  letI : FaithfulSMul (MvPolynomial (Fin r) K ⧸ P) A :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr
      (Ideal.kerLiftAlg_injective g)
  haveI : Module.Finite (MvPolynomial (Fin r) K ⧸ P) A :=
    kerLiftAlg_finite_of_finite g hfinite
  letI : Algebra.IsIntegral (MvPolynomial (Fin r) K ⧸ P) A :=
    Algebra.IsIntegral.of_finite _ _
  have hquotientDimension :
      ringKrullDim A = ringKrullDim (MvPolynomial (Fin r) K ⧸ P) :=
    ringKrullDim_eq_of_isIntegral_injective
      (Ideal.kerLiftAlg_injective g)
  have hsourceFinite : ringKrullDim (MvPolynomial (Fin r) K) < ⊤ := by
    rw [ringKrullDim_mvPolynomial_fin_eq_of_field K r]
    change ((r : ℕ∞) : WithBot ℕ∞) < ((⊤ : ℕ∞) : WithBot ℕ∞)
    exact WithBot.coe_lt_coe.mpr (WithTop.coe_lt_top r)
  have hdimensionLe : ringKrullDim (MvPolynomial (Fin r) K) ≤
      ringKrullDim (MvPolynomial (Fin r) K ⧸ P) := by
    rw [← hquotientDimension, hdim,
      ringKrullDim_mvPolynomial_fin_eq_of_field K r]
  have hmk : Function.Injective (Ideal.Quotient.mk P) :=
    injective_of_surjective_of_domain_dimension_le
      (Ideal.Quotient.mk P) Ideal.Quotient.mk_surjective
      hsourceFinite hdimensionLe
  apply (RingHom.injective_iff_ker_eq_bot g.toRingHom).mpr
  change P = ⊥
  have hk := (RingHom.injective_iff_ker_eq_bot
    (Ideal.Quotient.mk P)).mp hmk
  rwa [Ideal.mk_ker] at hk

/-- If the boundary has projective dimension `r-1`, the automatically
finite tail normalization is also injective. -/
theorem distinguishedNormalizationBoundaryHom_injective
    {N r degree : ℕ}
    (I : Ideal (MvPolynomial (Fin (N + 2)) ℚ))
    (A : Matrix (Fin (r + 1)) (Fin (N + 2)) ℚ)
    (hboundaryPrime : (projectiveBoundaryIdeal I).IsPrime)
    (hboundaryDegree : HasProjectiveDimensionDegree
      (projectiveBoundaryIdeal I) (r - 1) degree)
    (hr : 0 < r)
    (hfinite : (distinguishedNormalizationBoundaryHom I A).Finite) :
    Function.Injective (distinguishedNormalizationBoundaryHom I A) := by
  letI : (projectiveBoundaryIdeal I).IsPrime := hboundaryPrime
  apply finitePolynomialAlgHom_injective_of_ringKrullDim_eq
    (distinguishedNormalizationBoundaryHom I A) hfinite
  rw [hboundaryDegree.1]
  norm_cast
  omega

/-- Combined endpoint: a distinguished finite normalization of the source
restricts to a finite injective normalization of its prime boundary of the
expected dimension. -/
theorem distinguishedNormalizationBoundaryHom_finite_injective
    {N r degree : ℕ}
    (I : Ideal (MvPolynomial (Fin (N + 2)) ℚ))
    (A : Matrix (Fin (r + 1)) (Fin (N + 2)) ℚ)
    (hfirst : ∀ j, A 0 j = if j = 0 then 1 else 0)
    (hsourceFinite : ((Ideal.Quotient.mkₐ ℚ I).comp
      (aeval (indexedMatrixRowLinearPolynomial A))).Finite)
    (hboundaryPrime : (projectiveBoundaryIdeal I).IsPrime)
    (hboundaryDegree : HasProjectiveDimensionDegree
      (projectiveBoundaryIdeal I) (r - 1) degree)
    (hr : 0 < r) :
    Function.Injective (distinguishedNormalizationBoundaryHom I A) ∧
      (distinguishedNormalizationBoundaryHom I A).Finite := by
  have hfinite := distinguishedNormalizationBoundaryHom_finite
    I A hfirst hsourceFinite
  exact ⟨distinguishedNormalizationBoundaryHom_injective
    I A hboundaryPrime hboundaryDegree hr hfinite, hfinite⟩

/-- Package the tail rows of a distinguished source normalization as a
homogeneous linear normalization datum for the boundary.  Both finiteness
and injectivity are consequences of the source finiteness and the boundary
dimension; they are not additional choices. -/
def distinguishedNormalizationBoundaryData
    {N r degree : ℕ}
    (I : Ideal (MvPolynomial (Fin (N + 2)) ℚ))
    (A : Matrix (Fin (r + 1)) (Fin (N + 2)) ℚ)
    (hfirst : ∀ j, A 0 j = if j = 0 then 1 else 0)
    (hsourceFinite : ((Ideal.Quotient.mkₐ ℚ I).comp
      (aeval (indexedMatrixRowLinearPolynomial A))).Finite)
    (hboundaryPrime : (projectiveBoundaryIdeal I).IsPrime)
    (hboundaryDegree : HasProjectiveDimensionDegree
      (projectiveBoundaryIdeal I) (r - 1) degree)
    (hr : 0 < r) :
    HomogeneousLinearNormalizationData (projectiveBoundaryIdeal I) := by
  have h := distinguishedNormalizationBoundaryHom_finite_injective
    I A hfirst hsourceFinite hboundaryPrime hboundaryDegree hr
  exact
    { parameterCount := r
      forms := indexedMatrixRowLinearPolynomial
        (distinguishedNormalizationBoundaryMatrix A)
      forms_isHomogeneous :=
        indexedMatrixRowLinearPolynomial_isHomogeneous _
      injective := h.1
      finite := h.2 }

@[simp] theorem distinguishedNormalizationBoundaryData_parameterCount
    {N r degree : ℕ}
    (I : Ideal (MvPolynomial (Fin (N + 2)) ℚ))
    (A : Matrix (Fin (r + 1)) (Fin (N + 2)) ℚ)
    (hfirst : ∀ j, A 0 j = if j = 0 then 1 else 0)
    (hsourceFinite : ((Ideal.Quotient.mkₐ ℚ I).comp
      (aeval (indexedMatrixRowLinearPolynomial A))).Finite)
    (hboundaryPrime : (projectiveBoundaryIdeal I).IsPrime)
    (hboundaryDegree : HasProjectiveDimensionDegree
      (projectiveBoundaryIdeal I) (r - 1) degree)
    (hr : 0 < r) :
    (distinguishedNormalizationBoundaryData I A hfirst hsourceFinite
      hboundaryPrime hboundaryDegree hr).parameterCount = r := rfl

end

end TranslatedDepthSeven
