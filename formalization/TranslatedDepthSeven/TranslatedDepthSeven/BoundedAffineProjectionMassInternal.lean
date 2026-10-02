import TranslatedDepthSeven.BoundedAffineChartProjectionPrimeInternal
import TranslatedDepthSeven.ProjectedCurveSmallEquationSplit

/-!
# Explicit row-mass bounds for the internal affine projection menu

The internal BHB--Marmon projection menu is the full integer matrix box with
entry bound

`max ((D+1)^N) ((D^2+1)^(N+1))`.

This file records the elementary resulting row-mass bound and feeds it into
the already proved small-equation alternative for a projected curve.  In
particular, for fixed ambient dimension the projection loss is polynomial in
the curve degree.  No projection or height assertion is added as an input.
-/

namespace TranslatedDepthSeven

noncomputable section

open MvPolynomial Published StandardAG

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The literal entry bound used by the internal bounded affine projection
menu. -/
def boundedAffineProjectionEntryBound (N D : ℕ) : ℕ :=
  max ((D + 1) ^ N) ((D * D + 1) ^ (N + 1))

/-- The corresponding explicit row-mass bound. -/
def boundedAffineProjectionRowMassBound (N D : ℕ) : ℕ :=
  (N + 1) * boundedAffineProjectionEntryBound N D

theorem entry_natAbs_le_of_mem_boundedIntegralAffineProjectionMatrices
    {N r D : ℕ}
    {A : Matrix (Fin (r + 2)) (Fin (N + 1)) ℤ}
    (hA : A ∈ boundedIntegralAffineProjectionMatrices N r D)
    (i : Fin (r + 2)) (j : Fin (N + 1)) :
    (A i j).natAbs ≤ boundedAffineProjectionEntryBound N D := by
  classical
  have hentry := Finset.mem_Icc.mp
    (Fintype.mem_piFinset.mp (Fintype.mem_piFinset.mp hA i) j)
  change (A i j).natAbs ≤
    max ((D + 1) ^ N) ((D * D + 1) ^ (N + 1))
  by_cases hnonneg : 0 ≤ A i j
  · rw [← Int.ofNat_le, Int.natAbs_of_nonneg hnonneg]
    exact hentry.2
  · have hneg : A i j < 0 := lt_of_not_ge hnonneg
    rw [← Int.ofNat_le, ← Int.natAbs_neg,
      Int.natAbs_of_nonneg (by omega : 0 ≤ -(A i j))]
    omega

/-- Every matrix in the internal projection menu has the advertised
polynomial row mass. -/
theorem affineChartProjectionCoefficientMass_le_of_mem_bounded
    {N r D : ℕ}
    {A : Matrix (Fin (r + 2)) (Fin (N + 1)) ℤ}
    (hA : A ∈ boundedIntegralAffineProjectionMatrices N r D) :
    affineChartProjectionCoefficientMass A ≤
      boundedAffineProjectionRowMassBound N D := by
  classical
  apply Finset.sup_le
  intro i _hi
  calc
    (∑ j, (A i j).natAbs) ≤
        ∑ _j : Fin (N + 1), boundedAffineProjectionEntryBound N D := by
      exact Finset.sum_le_sum fun j _hj ↦
        entry_natAbs_le_of_mem_boundedIntegralAffineProjectionMatrices hA i j
    _ = boundedAffineProjectionRowMassBound N D := by
      simp [boundedAffineProjectionRowMassBound]

/-- The projected-curve small-equation alternative with the projection mass
replaced by the explicit polynomial bound of the internal menu. -/
theorem projectedCurve_smallEquation_or_bounded_exceptional_set_of_mem_bounded
    (hBezout : StandardAG.RationalProjectiveCurveAuxiliaryFirstChartBezout)
    {N e M : ℕ} (he : 0 < e)
    (I : Ideal (MvPolynomial (Fin (N + 1)) ℚ))
    (hI : I.IsPrime)
    (hIhom : I.IsHomogeneous
      (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) ℚ))
    (hIdim : HasProjectiveDimensionDegree I 1 e)
    (A : Matrix (Fin 3) (Fin (N + 1)) ℤ)
    (hA : A ∈ boundedIntegralAffineProjectionMatrices N 1 e)
    (G : MvPolynomial (Fin 3) ℚ)
    (hprojection : StandardAG.IsAffineChartFiniteBirationalLinearProjection
      (degree := e) I hI A G)
    (X : Finset (IntVector N))
    (hsource : ∀ z ∈ X, ∀ f ∈ I,
      MvPolynomial.eval
        (fun j ↦ (integralAffineChartVector z j : ℚ)) f = 0)
    (hbox : ∀ z ∈ X, ∀ j, (z j).natAbs ≤ M) :
    X.card ≤ e * e ∨
      ∃ P : MvPolynomial (Fin 3) ℤ,
        P ≠ 0 ∧ IsPrimitiveIntegralMvPolynomial P ∧
        P.IsHomogeneous e ∧
        (∀ z ∈ X,
          MvPolynomial.eval (integralAffineChartProjection A z) P = 0) ∧
        (∀ m, (P.coeff m).natAbs ≤
          (e + 1) ^ 3 * ((e + 1) ^ 3).factorial *
            max 1 (boundedAffineProjectionRowMassBound N e * max 1 M) ^
              (e * (e + 1) ^ 3)) ∧
        Irreducible (P.map (Int.castRingHom ℚ)) ∧
        RingHom.ker
          (StandardAG.projectiveMatrixCoordinateMap I
            (A.map (Int.castRingHom ℚ))).toRingHom =
              Ideal.span {P.map (Int.castRingHom ℚ)} ∧
        projectiveIntegralClosureIdeal
          (RingHom.ker
            (StandardAG.projectiveMatrixCoordinateMap I
              (A.map (Int.castRingHom ℚ))).toRingHom) = Ideal.span {P} ∧
        (projectedSourceGradientZeroPoints A P X).card ≤ e * (e - 1) := by
  rcases projectedCurve_smallEquation_or_bounded_exceptional_set
      hBezout he I hI hIhom hIdim A G hprojection X hsource hbox with
    hsmall | ⟨P, hP, hprimitive, hPhom, hPzero, hPcoeff,
      hPirred, himage, hclosure, hsingular⟩
  · exact Or.inl hsmall
  · refine Or.inr ⟨P, hP, hprimitive, hPhom, hPzero, ?_,
      hPirred, himage, hclosure, hsingular⟩
    intro m
    refine (hPcoeff m).trans ?_
    apply Nat.mul_le_mul_left
    apply Nat.pow_le_pow_left
    apply max_le_max_left
    exact Nat.mul_le_mul_right (max 1 M)
      (affineChartProjectionCoefficientMass_le_of_mem_bounded hA)

end

end TranslatedDepthSeven
