import TranslatedDepthSeven.BoundedAffineChartProjectionPrimeInternal
import TranslatedDepthSeven.BoundedSimultaneousAffineProjectionMatricesInternal
import TranslatedDepthSeven.BoundedSimultaneousPrimitiveNormalizationCoordinateInternal
import TranslatedDepthSeven.DistinguishedNormalizationBoundaryRestrictionInternal
import TranslatedDepthSeven.ProjectiveBoundaryHomogeneousInternal

/-!
# One bounded projection for a source and its boundary

A distinguished normalization of the source fixes `X₀`; its tail is therefore
a normalization of the prime boundary `X₀ = 0`.  We choose one bounded
primitive linear form for the two resulting function-field extensions.  The
source projection and boundary projection consequently use the same literal
integral matrix.
-/

namespace TranslatedDepthSeven
noncomputable section

open MvPolynomial Matrix Published StandardAG

attribute [local instance] MvPolynomial.gradedAlgebra

set_option maxHeartbeats 8000000
set_option synthInstance.maxHeartbeats 700000

/-- The source-coordinate family after restriction to `X₀=0`, padded by a
zero in the first position so that it uses the source coefficient vector. -/
def paddedBoundaryQuotientCoordinates {N : ℕ}
    (I : Ideal (MvPolynomial (Fin (N + 2)) ℚ)) :
    Fin (N + 2) →
      (MvPolynomial (Fin (N + 1)) ℚ ⧸ projectiveBoundaryIdeal I) :=
  Fin.cases 0 (fun j ↦ Ideal.Quotient.mk (projectiveBoundaryIdeal I) (X j))

/-- Adding the padded zero coordinate does not change generation of the
boundary function field. -/
theorem adjoin_paddedBoundaryQuotientCoordinates_eq_top
    {N : ℕ} (I : Ideal (MvPolynomial (Fin (N + 2)) ℚ))
    (hboundaryPrime : (projectiveBoundaryIdeal I).IsPrime)
    (F : Type*) [Field F] [Algebra ℚ F]
    [Algebra F (FractionRing
      (MvPolynomial (Fin (N + 1)) ℚ ⧸ projectiveBoundaryIdeal I))]
    [IsScalarTower ℚ F (FractionRing
      (MvPolynomial (Fin (N + 1)) ℚ ⧸ projectiveBoundaryIdeal I))] :
    IntermediateField.adjoin F (Set.range fun i ↦
      algebraMap
        (MvPolynomial (Fin (N + 1)) ℚ ⧸ projectiveBoundaryIdeal I)
        (FractionRing
          (MvPolynomial (Fin (N + 1)) ℚ ⧸ projectiveBoundaryIdeal I))
        (paddedBoundaryQuotientCoordinates I i)) = ⊤ := by
  letI : (projectiveBoundaryIdeal I).IsPrime := hboundaryPrime
  have hcoordinates :=
    adjoin_fractionField_affineQuotient_coordinates_eq_top
      (F := F) (projectiveBoundaryIdeal I)
  apply top_unique
  rw [← hcoordinates]
  apply IntermediateField.adjoin.mono F
  rintro _ ⟨j, rfl⟩
  exact ⟨j.succ, rfl⟩

/-- The common primitive polynomial after restriction to the boundary. -/
def simultaneousBoundaryPrimitivePolynomial {N : ℕ}
    (c : Fin (N + 2) → ℕ) : MvPolynomial (Fin (N + 1)) ℚ :=
  ∑ j, C (c j.succ : ℚ) * X j

/-- The quotient element represented by the boundary primitive polynomial is
the common padded linear combination. -/
theorem mk_simultaneousBoundaryPrimitivePolynomial
    {N : ℕ} (I : Ideal (MvPolynomial (Fin (N + 2)) ℚ))
    (c : Fin (N + 2) → ℕ) :
    Ideal.Quotient.mk (projectiveBoundaryIdeal I)
        (simultaneousBoundaryPrimitivePolynomial c) =
      ∑ i, (c i : ℚ) • paddedBoundaryQuotientCoordinates I i := by
  rw [Fin.sum_univ_succ]
  simp [simultaneousBoundaryPrimitivePolynomial,
    paddedBoundaryQuotientCoordinates, Algebra.smul_def]

/-- The boundary matrix in augmented-normalization order: common primitive
row first, followed by the tail normalization rows. -/
def simultaneousBoundaryProjectionMatrix {N r : ℕ}
    (A : Matrix (Fin (r + 1)) (Fin (N + 2)) ℚ)
    (c : Fin (N + 2) → ℕ) : Matrix (Fin (r + 1)) (Fin (N + 1)) ℚ :=
  fun i ↦ Fin.cases (fun j ↦ (c j.succ : ℚ))
    (distinguishedNormalizationBoundaryMatrix A) i

/-- The boundary coordinate map is the augmented normalization homomorphism. -/
theorem simultaneousBoundaryProjection_coordinateMap_eq_augmented
    {N r degree : ℕ}
    (I : Ideal (MvPolynomial (Fin (N + 2)) ℚ))
    (A : Matrix (Fin (r + 1)) (Fin (N + 2)) ℚ)
    (hfirst : ∀ j, A 0 j = if j = 0 then 1 else 0)
    (hsourceFinite : ((Ideal.Quotient.mkₐ ℚ I).comp
      (aeval (indexedMatrixRowLinearPolynomial A))).Finite)
    (hboundaryPrime : (projectiveBoundaryIdeal I).IsPrime)
    (hboundaryDegree : HasProjectiveDimensionDegree
      (projectiveBoundaryIdeal I) (r - 1) degree)
    (hr : 0 < r) (c : Fin (N + 2) → ℕ) :
    projectiveMatrixCoordinateMap (projectiveBoundaryIdeal I)
        (simultaneousBoundaryProjectionMatrix A c) =
      augmentedLinearNormalizationHom
        (distinguishedNormalizationBoundaryData I A hfirst hsourceFinite
          hboundaryPrime hboundaryDegree hr)
        (Ideal.Quotient.mk (projectiveBoundaryIdeal I)
          (simultaneousBoundaryPrimitivePolynomial c)) := by
  let D := distinguishedNormalizationBoundaryData I A hfirst hsourceFinite
    hboundaryPrime hboundaryDegree hr
  let u := Ideal.Quotient.mk (projectiveBoundaryIdeal I)
    (simultaneousBoundaryPrimitivePolynomial c)
  apply MvPolynomial.algHom_ext
  intro i
  refine Fin.cases ?_ (fun k ↦ ?_) i
  · simp only [projectiveMatrixCoordinateMap, AlgHom.comp_apply, aeval_X]
    have hrhs : augmentedLinearNormalizationHom D u
        (X (0 : Fin (r + 1))) = u := by
      simpa [D] using augmentedLinearNormalizationHom_X_zero D u
    change _ = augmentedLinearNormalizationHom D u (X (0 : Fin (r + 1)))
    rw [hrhs]
    change Ideal.Quotient.mk (projectiveBoundaryIdeal I)
        (projectiveMatrixLinearForm
          (simultaneousBoundaryProjectionMatrix A c) 0) =
      Ideal.Quotient.mk (projectiveBoundaryIdeal I)
        (simultaneousBoundaryPrimitivePolynomial c)
    apply congrArg (Ideal.Quotient.mk (projectiveBoundaryIdeal I))
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
      distinguishedNormalizationBoundaryData,
      projectiveMatrixLinearForm, simultaneousBoundaryProjectionMatrix]
    rw [indexedMatrixRowLinearPolynomial, map_sum]
    simp only [map_mul]

/-- Deleting the distinguished source row and column from the actual common
integral projection gives the augmented boundary matrix. -/
theorem affineChartProjectionBoundaryMatrix_primitiveAffineProjectionMatrix
    {N r : ℕ}
    (A : Matrix (Fin (r + 1)) (Fin (N + 2)) ℤ)
    (c : Fin (N + 2) → ℕ) :
    affineChartProjectionBoundaryMatrix
        ((primitiveAffineProjectionMatrix A c).map (Int.castRingHom ℚ)) =
      simultaneousBoundaryProjectionMatrix
        (A.map (Int.castRingHom ℚ)) c := by
  funext i j
  refine Fin.cases ?_ (fun k ↦ ?_) i
  · simp [affineChartProjectionBoundaryMatrix,
      primitiveAffineProjectionMatrix,
      simultaneousBoundaryProjectionMatrix]
  · simp only [affineChartProjectionBoundaryMatrix, Matrix.map_apply,
      primitiveAffineProjectionMatrix, simultaneousBoundaryProjectionMatrix,
      Fin.cases_succ, Int.cast_id, RingHom.id_apply,
      distinguishedNormalizationBoundaryMatrix]
    have h0 : k.succ.succ ≠ (0 : Fin (r + 2)) := Fin.succ_ne_zero _
    have h1 : k.succ.succ ≠ (1 : Fin (r + 2)) := by
      intro h
      apply Fin.succ_ne_zero k
      exact Fin.succ_injective (n := r + 1) h
    rw [Equiv.swap_apply_of_ne_of_ne h0 h1]
    rfl

end
end TranslatedDepthSeven
