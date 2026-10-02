import TranslatedDepthSeven.ProjectiveConeSectionInternal
import TranslatedDepthSeven.IsolatedVertexQuotientLiteralExceptionalLift
import TranslatedDepthSeven.IsolatedVertexQuotientRelativeSourceSectionFamily

/-!
# Literal source-coordinate transport for the isolated-vertex quotient

The original source section is obtained from the coordinate-cone section
by the fixed unimodular linear substitution.  This file proves that ideal
identity and the associated preservation of projective Hilbert data.
-/

namespace TranslatedDepthSeven

noncomputable section

open MvPolynomial Published

attribute [local instance] MvPolynomial.gradedAlgebra

set_option maxHeartbeats 8000000
set_option synthInstance.maxHeartbeats 400000

universe u

/-- A homogeneous polynomial automorphism preserves the complete
projective dimension--degree certificate. -/
theorem hasProjectiveDimensionDegree_map_homogeneousAlgEquiv_iff
    (K : Type u) [Field K] {N r d : ℕ}
    (e : MvPolynomial (Fin (N + 1)) K ≃ₐ[K]
      MvPolynomial (Fin (N + 1)) K)
    (he : ∀ (k : ℕ) (f : MvPolynomial (Fin (N + 1)) K),
      f.IsHomogeneous k → (e f).IsHomogeneous k)
    (hesymm : ∀ (k : ℕ) (f : MvPolynomial (Fin (N + 1)) K),
      f.IsHomogeneous k → (e.symm f).IsHomogeneous k)
    (I : Ideal (MvPolynomial (Fin (N + 1)) K)) :
    HasProjectiveDimensionDegree (I.map e) r d ↔
      HasProjectiveDimensionDegree I r d := by
  have hEq : I.map e = I.comap e.symm := by
    apply le_antisymm
    · rw [Ideal.map_le_iff_le_comap]
      intro f hf
      simpa using hf
    · intro f hf
      have hef : e.symm f ∈ I := hf
      have hm : e (e.symm f) ∈ I.map e := Ideal.mem_map_of_mem e hef
      simpa using hm
  rw [hEq]
  exact hasProjectiveDimensionDegree_comap_surjective_iff
    e.symm.toAlgHom e.symm.surjective e.toAlgHom
    (by ext f; simp) hesymm he I r d

/-- A rectangular row polynomial is carried by matrix substitution to the
row polynomial whose coefficient row is right-multiplied by the
substitution matrix. -/
theorem polynomialMatrixSubstitution_matrixRowLinearPolynomial
    {K : Type u} [Field K] [Infinite K] {c N : ℕ}
    (M : Matrix (Fin N) (Fin N) K)
    (B : Matrix (Fin c) (Fin N) K) (i : Fin c) :
    polynomialMatrixSubstitution M (matrixRowLinearPolynomial B i) =
      matrixRowLinearPolynomial (B * M) i := by
  apply MvPolynomial.funext
  intro x
  rw [eval_polynomialMatrixSubstitution,
    eval_matrixRowLinearPolynomial, eval_matrixRowLinearPolynomial,
    Matrix.mulVec_mulVec]

/-- Matrix substitution transports the full row-generated ideal by right
matrix multiplication. -/
theorem map_matrixRowLinearIdeal_polynomialMatrixSubstitution
    {K : Type u} [Field K] [Infinite K] {c N : ℕ}
    (M : Matrix (Fin N) (Fin N) K)
    (B : Matrix (Fin c) (Fin N) K) :
    (matrixRowLinearIdeal B).map (polynomialMatrixSubstitution M) =
      matrixRowLinearIdeal (B * M) := by
  unfold matrixRowLinearIdeal
  rw [Ideal.map_span]
  apply congrArg Ideal.span
  ext f
  constructor
  · rintro ⟨g, ⟨i, rfl⟩, rfl⟩
    exact ⟨i, polynomialMatrixSubstitution_matrixRowLinearPolynomial
      M B i |>.symm⟩
  · rintro ⟨i, rfl⟩
    exact ⟨matrixRowLinearPolynomial B i, ⟨i, rfl⟩,
      polynomialMatrixSubstitution_matrixRowLinearPolynomial M B i⟩

/-- The original-coordinate rational row ideal returns to the displayed
coordinate row ideal under the unimodular substitution. -/
theorem map_originalSourceRowIdeal_rationalPolynomialEquiv
    {c : ℕ} (U : IntegralUnimodularChange 13)
    (B : Matrix (Fin c) (Fin 13) ℤ) :
    (matrixRowLinearIdeal
      ((integralQuotientOriginalSourceSectionMatrix U B).map
        (Int.castRingHom ℚ))).map U.rationalPolynomialEquiv =
      matrixRowLinearIdeal (B.map (Int.castRingHom ℚ)) := by
  rw [integralQuotientOriginalSourceSectionMatrix_map_intCast]
  change
    (matrixRowLinearIdeal
      (B.map (Int.castRingHom ℚ) * U.forward.map (Int.castRingHom ℚ))).map
        (polynomialMatrixSubstitution
          (U.inverse.map (Int.castRingHom ℚ))) = _
  rw [map_matrixRowLinearIdeal_polynomialMatrixSubstitution]
  rw [Matrix.mul_assoc, ← Matrix.map_mul, U.forward_mul_inverse]
  simp

/-- Exact rational source-section transport. -/
theorem map_rationalOriginalSourceSectionIdeal_eq_coordinateConeSection
    {c : ℕ}
    (equations : Finset (MvPolynomial (Fin 13) ℤ))
    (U : IntegralUnimodularChange 13)
    (lowerEquations : Finset (MvPolynomial (Fin 12) ℤ))
    (hfamily : U.transformEquationFinset equations =
      liftEquationFinsetAfterFirst lowerEquations)
    (B : Matrix (Fin c) (Fin 13) ℤ) :
    (finiteEquationIdeal (rationalizedEquationFinset equations) ⊔
      matrixRowLinearIdeal
        ((integralQuotientOriginalSourceSectionMatrix U B).map
          (Int.castRingHom ℚ))).map U.rationalPolynomialEquiv =
      projectiveConeFinIdeal ℚ 11
          (isolatedVertexLowerRationalIdeal lowerEquations) ⊔
        matrixRowLinearIdeal (B.map (Int.castRingHom ℚ)) := by
  rw [Ideal.map_sup, map_originalSourceRowIdeal_rationalPolynomialEquiv]
  have hbase :
    (finiteEquationIdeal (rationalizedEquationFinset equations)).map
        U.rationalPolynomialEquiv =
      finiteEquationIdeal
        (rationalizedEquationFinset (U.transformEquationFinset equations)) :=
      (finiteEquationIdeal_transform_rationalized U equations).symm
  have hbase' : (finiteEquationIdeal
        (rationalizedEquationFinset (U.transformEquationFinset equations))) =
      finiteEquationIdeal
        (rationalizedEquationFinset
          (liftEquationFinsetAfterFirst lowerEquations)) := by rw [hfamily]
  rw [hbase, hbase', finiteEquationIdeal_lift_rationalized]
  rfl

/-- Exact geometric source-section transport. -/
theorem map_geometricOriginalSourceSectionIdeal_eq_coordinateConeSection
    {c : ℕ}
    (equations : Finset (MvPolynomial (Fin 13) ℤ))
    (U : IntegralUnimodularChange 13)
    (lowerEquations : Finset (MvPolynomial (Fin 12) ℤ))
    (hfamily : U.transformEquationFinset equations =
      liftEquationFinsetAfterFirst lowerEquations)
    (B : Matrix (Fin c) (Fin 13) ℤ) :
    (finiteEquationIdeal
      (geometricLinearSectionEquationFinset equations
        ((integralQuotientOriginalSourceSectionMatrix U B).map
          (Int.castRingHom ℚ)))).map
        (U.coefficientFieldPolynomialEquiv Qbar) =
      projectiveConeFinIdeal Qbar 11
          (geometricIsolatedVertexLowerIdeal lowerEquations) ⊔
        matrixRowLinearIdeal (qbarIntMatrix B) := by
  let sourceRational :=
    finiteEquationIdeal (rationalizedEquationFinset equations) ⊔
      matrixRowLinearIdeal
        ((integralQuotientOriginalSourceSectionMatrix U B).map
          (Int.castRingHom ℚ))
  have hsourceGeom :
      finiteEquationIdeal
        (geometricLinearSectionEquationFinset equations
          ((integralQuotientOriginalSourceSectionMatrix U B).map
            (Int.castRingHom ℚ))) =
        sourceRational.map (MvPolynomial.map (algebraMap ℚ Qbar)) := by
    rw [geometricLinearSectionIdeal_eq_map_rationalLinearSectionIdeal,
      rationalLinearSectionIdeal_eq_sup_indexedRows,
      indexedMatrixRowLinearIdeal_eq_matrixRowLinearIdeal]
  rw [hsourceGeom]
  rw [← U.map_map_rationalPolynomialEquiv Qbar sourceRational]
  rw [map_rationalOriginalSourceSectionIdeal_eq_coordinateConeSection
    equations U lowerEquations hfamily B]
  rw [Ideal.map_sup, map_projectiveConeFinIdeal_coefficients,
    map_matrixRowLinearIdeal_coefficients]
  rfl

/-- Evaluation of the inverse coordinate substitution at an original point
is evaluation before substitution at the transformed point. -/
theorem eval_coefficientFieldPolynomialEquiv_symm
    (U : IntegralUnimodularChange 13)
    (x : Fin 13 → Qbar) (f : MvPolynomial (Fin 13) Qbar) :
    MvPolynomial.eval x
        ((U.coefficientFieldPolynomialEquiv Qbar).symm f) =
      MvPolynomial.eval
        (Matrix.mulVec (U.forward.map (Int.castRingHom Qbar)) x) f := by
  change MvPolynomial.eval x
      (polynomialMatrixSubstitution
        (U.forward.map (Int.castRingHom Qbar)) f) = _
  exact eval_polynomialMatrixSubstitution _ _ _

end

end TranslatedDepthSeven
