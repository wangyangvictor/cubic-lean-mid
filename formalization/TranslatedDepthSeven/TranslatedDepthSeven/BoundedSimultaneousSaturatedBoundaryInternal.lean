import TranslatedDepthSeven.BoundedSimultaneousAffineChartProjectionInternal
import TranslatedDepthSeven.DistinguishedNormalizationSaturatedBoundaryInternal

/-!
# Common projection coordinates for a saturated boundary

Projective Bertini supplies a homogeneous prime saturation `B` containing
the literal specialization of the source at `X₀ = 0`.  This file records
the elementary coordinate identities needed to use the same primitive row
for the source and for `B`.
-/

namespace TranslatedDepthSeven

noncomputable section

open MvPolynomial Matrix Published StandardAG

attribute [local instance] MvPolynomial.gradedAlgebra

set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 500000

/-- Source coordinates on an arbitrary saturated boundary, padded by zero
in the distinguished source position. -/
def paddedSaturatedBoundaryQuotientCoordinates {N : ℕ}
    (B : Ideal (MvPolynomial (Fin (N + 1)) ℚ)) :
    Fin (N + 2) → (MvPolynomial (Fin (N + 1)) ℚ ⧸ B) :=
  Fin.cases 0 (fun j ↦ Ideal.Quotient.mk B (X j))

/-- The padded coordinate family generates the fraction field of a prime
saturated boundary. -/
theorem adjoin_paddedSaturatedBoundaryQuotientCoordinates_eq_top
    {N : ℕ} (B : Ideal (MvPolynomial (Fin (N + 1)) ℚ))
    (hBprime : B.IsPrime)
    (F : Type*) [Field F] [Algebra ℚ F]
    [Algebra F (FractionRing (MvPolynomial (Fin (N + 1)) ℚ ⧸ B))]
    [IsScalarTower ℚ F (FractionRing
      (MvPolynomial (Fin (N + 1)) ℚ ⧸ B))] :
    IntermediateField.adjoin F (Set.range fun i ↦
      algebraMap (MvPolynomial (Fin (N + 1)) ℚ ⧸ B)
        (FractionRing (MvPolynomial (Fin (N + 1)) ℚ ⧸ B))
        (paddedSaturatedBoundaryQuotientCoordinates B i)) = ⊤ := by
  letI : B.IsPrime := hBprime
  have hcoordinates :=
    adjoin_fractionField_affineQuotient_coordinates_eq_top (F := F) B
  apply top_unique
  rw [← hcoordinates]
  apply IntermediateField.adjoin.mono F
  rintro _ ⟨j, rfl⟩
  exact ⟨j.succ, rfl⟩

/-- The common primitive polynomial represents the padded linear
combination in the quotient by any boundary ideal. -/
theorem mk_simultaneousSaturatedBoundaryPrimitivePolynomial
    {N : ℕ} (B : Ideal (MvPolynomial (Fin (N + 1)) ℚ))
    (c : Fin (N + 2) → ℕ) :
    Ideal.Quotient.mk B (simultaneousBoundaryPrimitivePolynomial c) =
      ∑ i, (c i : ℚ) • paddedSaturatedBoundaryQuotientCoordinates B i := by
  rw [Fin.sum_univ_succ]
  simp [simultaneousBoundaryPrimitivePolynomial,
    paddedSaturatedBoundaryQuotientCoordinates, Algebra.smul_def]

/-- The boundary coordinate map obtained from the common matrix is the
augmented normalization of the saturated boundary. -/
theorem simultaneousSaturatedBoundaryProjection_coordinateMap_eq_augmented
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
    (hr : 0 < r) (c : Fin (N + 2) → ℕ) :
    projectiveMatrixCoordinateMap B
        (simultaneousBoundaryProjectionMatrix A c) =
      augmentedLinearNormalizationHom
        (distinguishedNormalizationSaturatedBoundaryData
          I B hIB A hfirst hsourceFinite hBprime hBdegree hr)
        (Ideal.Quotient.mk B
          (simultaneousBoundaryPrimitivePolynomial c)) := by
  let D := distinguishedNormalizationSaturatedBoundaryData
    I B hIB A hfirst hsourceFinite hBprime hBdegree hr
  let u := Ideal.Quotient.mk B (simultaneousBoundaryPrimitivePolynomial c)
  apply MvPolynomial.algHom_ext
  intro i
  refine Fin.cases ?_ (fun k ↦ ?_) i
  · simp only [projectiveMatrixCoordinateMap, AlgHom.comp_apply, aeval_X]
    have hrhs : augmentedLinearNormalizationHom D u
        (X (0 : Fin (r + 1))) = u := by
      simpa [D] using augmentedLinearNormalizationHom_X_zero D u
    change _ = augmentedLinearNormalizationHom D u (X (0 : Fin (r + 1)))
    rw [hrhs]
    change Ideal.Quotient.mk B
        (projectiveMatrixLinearForm
          (simultaneousBoundaryProjectionMatrix A c) 0) =
      Ideal.Quotient.mk B (simultaneousBoundaryPrimitivePolynomial c)
    apply congrArg (Ideal.Quotient.mk B)
    simp [projectiveMatrixLinearForm, simultaneousBoundaryProjectionMatrix,
      indexedMatrixRowLinearPolynomial,
      simultaneousBoundaryPrimitivePolynomial]
  · simp only [projectiveMatrixCoordinateMap, AlgHom.comp_apply, aeval_X]
    have hrhs : augmentedLinearNormalizationHom D u (X k.succ) =
        D.hom (X k) := by
      simpa [D] using augmentedLinearNormalizationHom_X_succ D u k
    change _ = augmentedLinearNormalizationHom D u (X k.succ)
    rw [hrhs]
    simp [D, HomogeneousLinearNormalizationData.hom,
      distinguishedNormalizationSaturatedBoundaryData,
      distinguishedNormalizationSaturatedBoundaryHom,
      projectiveMatrixLinearForm, simultaneousBoundaryProjectionMatrix]
    rw [indexedMatrixRowLinearPolynomial, map_sum]
    simp only [map_mul]

end

end TranslatedDepthSeven
