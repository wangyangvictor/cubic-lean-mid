import TranslatedDepthSeven.DistinguishedNormalizationBoundaryRestrictionInternal

/-!
# Restricting a distinguished normalization to a saturated boundary

Projective Bertini naturally produces a prime homogeneous saturation `B`
containing the literal boundary ideal obtained by setting `X₀ = 0`.  The
source normalization still restricts to `B`: finiteness first descends to
the literal boundary and then through the quotient by `B`; injectivity
follows from the expected dimension of the prime saturated boundary.
-/

namespace TranslatedDepthSeven

noncomputable section

open MvPolynomial Published

attribute [local instance] MvPolynomial.gradedAlgebra

set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 500000

/-- The tail normalization map with target an arbitrary ideal containing
the literal boundary ideal. -/
def distinguishedNormalizationSaturatedBoundaryHom {N r : ℕ}
    (B : Ideal (MvPolynomial (Fin N) ℚ))
    (A : Matrix (Fin (r + 1)) (Fin (N + 1)) ℚ) :
    MvPolynomial (Fin r) ℚ →ₐ[ℚ]
      (MvPolynomial (Fin N) ℚ ⧸ B) :=
  (Ideal.Quotient.mkₐ ℚ B).comp
    (aeval (indexedMatrixRowLinearPolynomial
      (distinguishedNormalizationBoundaryMatrix A)))

/-- The quotient map from the source to a saturated boundary containing
the literal specialization of the source ideal. -/
def projectiveSaturatedBoundaryQuotientMap {N : ℕ}
    (I : Ideal (MvPolynomial (Fin (N + 1)) ℚ))
    (B : Ideal (MvPolynomial (Fin N) ℚ))
    (hIB : projectiveBoundaryIdeal I ≤ B) :
    (MvPolynomial (Fin (N + 1)) ℚ ⧸ I) →ₐ[ℚ]
      (MvPolynomial (Fin N) ℚ ⧸ B) :=
  Ideal.quotientMapₐ B (rationalSpecializeFirstCoordinate 0)
    (Ideal.le_comap_map.trans (Ideal.comap_mono hIB))

theorem projectiveSaturatedBoundaryQuotientMap_surjective {N : ℕ}
    (I : Ideal (MvPolynomial (Fin (N + 1)) ℚ))
    (B : Ideal (MvPolynomial (Fin N) ℚ))
    (hIB : projectiveBoundaryIdeal I ≤ B) :
    Function.Surjective
      (projectiveSaturatedBoundaryQuotientMap I B hIB) := by
  unfold projectiveSaturatedBoundaryQuotientMap
  exact Ideal.quotientMap_surjective
    (I := B) (J := I)
    (f := (rationalSpecializeFirstCoordinate 0).toRingHom)
    (H := Ideal.le_comap_map.trans (Ideal.comap_mono hIB))
    (rationalSpecializeFirstCoordinate_zero_surjective N)

/-- Specializing the full normalization and then passing to `B` is the
tail normalization defined directly in the quotient by `B`. -/
theorem distinguishedNormalizationSaturatedBoundaryHom_comp_specialize
    {N r : ℕ}
    (I : Ideal (MvPolynomial (Fin (N + 1)) ℚ))
    (B : Ideal (MvPolynomial (Fin N) ℚ))
    (hIB : projectiveBoundaryIdeal I ≤ B)
    (A : Matrix (Fin (r + 1)) (Fin (N + 1)) ℚ)
    (hfirst : ∀ j, A 0 j = if j = 0 then 1 else 0) :
    (distinguishedNormalizationSaturatedBoundaryHom B A).comp
        (rationalSpecializeFirstCoordinate 0) =
      (projectiveSaturatedBoundaryQuotientMap I B hIB).comp
        ((Ideal.Quotient.mkₐ ℚ I).comp
          (aeval (indexedMatrixRowLinearPolynomial A))) := by
  apply MvPolynomial.algHom_ext
  intro i
  refine Fin.cases ?_ (fun k => ?_) i
  · simp only [AlgHom.comp_apply]
    have hrow : indexedMatrixRowLinearPolynomial A 0 = X 0 := by
      rw [indexedMatrixRowLinearPolynomial, Fin.sum_univ_succ, hfirst 0]
      simp_rw [hfirst]
      simp
    simp [distinguishedNormalizationSaturatedBoundaryHom,
      projectiveSaturatedBoundaryQuotientMap,
      rationalSpecializeFirstCoordinate, hrow]
  · simp only [AlgHom.comp_apply]
    simp only [rationalSpecializeFirstCoordinate, aeval_X]
    rw [show projectiveSaturatedBoundaryQuotientMap I B hIB
        (Ideal.Quotient.mkₐ ℚ I
          (indexedMatrixRowLinearPolynomial A k.succ)) =
        Ideal.Quotient.mk B
          (rationalSpecializeFirstCoordinate 0
            (indexedMatrixRowLinearPolynomial A k.succ)) by
      simp [projectiveSaturatedBoundaryQuotientMap]]
    apply congrArg (Ideal.Quotient.mk B)
    rw [indexedMatrixRowLinearPolynomial, Fin.sum_univ_succ]
    simp only [map_add, map_mul]
    simp [rationalSpecializeFirstCoordinate,
      distinguishedNormalizationBoundaryMatrix,
      indexedMatrixRowLinearPolynomial]

/-- A finite distinguished source normalization remains finite after
restriction to any quotient of its literal boundary. -/
theorem distinguishedNormalizationSaturatedBoundaryHom_finite
    {N r : ℕ}
    (I : Ideal (MvPolynomial (Fin (N + 1)) ℚ))
    (B : Ideal (MvPolynomial (Fin N) ℚ))
    (hIB : projectiveBoundaryIdeal I ≤ B)
    (A : Matrix (Fin (r + 1)) (Fin (N + 1)) ℚ)
    (hfirst : ∀ j, A 0 j = if j = 0 then 1 else 0)
    (hfinite : ((Ideal.Quotient.mkₐ ℚ I).comp
      (aeval (indexedMatrixRowLinearPolynomial A))).Finite) :
    (distinguishedNormalizationSaturatedBoundaryHom B A).Finite := by
  have hquotient : (projectiveSaturatedBoundaryQuotientMap I B hIB).Finite :=
    AlgHom.Finite.of_surjective _
      (projectiveSaturatedBoundaryQuotientMap_surjective I B hIB)
  have hcomp : ((projectiveSaturatedBoundaryQuotientMap I B hIB).comp
      ((Ideal.Quotient.mkₐ ℚ I).comp
        (aeval (indexedMatrixRowLinearPolynomial A)))).Finite :=
    AlgHom.Finite.comp hquotient hfinite
  refine AlgHom.Finite.of_comp_finite
    (f := rationalSpecializeFirstCoordinate (d := r) 0) ?_
  rw [distinguishedNormalizationSaturatedBoundaryHom_comp_specialize
    I B hIB A hfirst]
  exact hcomp

/-- At the expected dimension, the finite tail map to a prime saturated
boundary is injective. -/
theorem distinguishedNormalizationSaturatedBoundaryHom_injective
    {N r degree : ℕ}
    (B : Ideal (MvPolynomial (Fin (N + 1)) ℚ))
    (A : Matrix (Fin (r + 1)) (Fin (N + 2)) ℚ)
    (hBprime : B.IsPrime)
    (hBdegree : HasProjectiveDimensionDegree B (r - 1) degree)
    (hr : 0 < r)
    (hfinite : (distinguishedNormalizationSaturatedBoundaryHom B A).Finite) :
    Function.Injective
      (distinguishedNormalizationSaturatedBoundaryHom B A) := by
  letI : B.IsPrime := hBprime
  apply finitePolynomialAlgHom_injective_of_ringKrullDim_eq
    (distinguishedNormalizationSaturatedBoundaryHom B A) hfinite
  rw [hBdegree.1]
  norm_cast
  omega

/-- Package the restricted normalization as ordinary homogeneous
normalization data for the saturated boundary. -/
def distinguishedNormalizationSaturatedBoundaryData
    {N r degree : ℕ}
    (I : Ideal (MvPolynomial (Fin (N + 2)) ℚ))
    (B : Ideal (MvPolynomial (Fin (N + 1)) ℚ))
    (hIB : projectiveBoundaryIdeal I ≤ B)
    (A : Matrix (Fin (r + 1)) (Fin (N + 2)) ℚ)
    (hfirst : ∀ j, A 0 j = if j = 0 then 1 else 0)
    (hsourceFinite : ((Ideal.Quotient.mkₐ ℚ I).comp
      (aeval (indexedMatrixRowLinearPolynomial A))).Finite)
    (hBprime : B.IsPrime)
    (hBdegree : HasProjectiveDimensionDegree B (r - 1) degree)
    (hr : 0 < r) :
    HomogeneousLinearNormalizationData B := by
  have hfinite := distinguishedNormalizationSaturatedBoundaryHom_finite
    I B hIB A hfirst hsourceFinite
  have hinjective := distinguishedNormalizationSaturatedBoundaryHom_injective
    B A hBprime hBdegree hr hfinite
  exact
    { parameterCount := r
      forms := indexedMatrixRowLinearPolynomial
        (distinguishedNormalizationBoundaryMatrix A)
      forms_isHomogeneous :=
        indexedMatrixRowLinearPolynomial_isHomogeneous _
      injective := hinjective
      finite := hfinite }

@[simp] theorem distinguishedNormalizationSaturatedBoundaryData_parameterCount
    {N r degree : ℕ}
    (I : Ideal (MvPolynomial (Fin (N + 2)) ℚ))
    (B : Ideal (MvPolynomial (Fin (N + 1)) ℚ))
    (hIB : projectiveBoundaryIdeal I ≤ B)
    (A : Matrix (Fin (r + 1)) (Fin (N + 2)) ℚ)
    (hfirst : ∀ j, A 0 j = if j = 0 then 1 else 0)
    (hsourceFinite : ((Ideal.Quotient.mkₐ ℚ I).comp
      (aeval (indexedMatrixRowLinearPolynomial A))).Finite)
    (hBprime : B.IsPrime)
    (hBdegree : HasProjectiveDimensionDegree B (r - 1) degree)
    (hr : 0 < r) :
    (distinguishedNormalizationSaturatedBoundaryData I B hIB A hfirst
      hsourceFinite hBprime hBdegree hr).parameterCount = r := rfl

end

end TranslatedDepthSeven
