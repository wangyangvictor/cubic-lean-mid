import TranslatedDepthSeven.StrictRankAtMostSixProjectiveSplit
import TranslatedDepthSeven.JacobianExceptionalDegreeSplit

/-!
# Exact degree frontier for the strict normalized low-rank cell

This is the preceding projective-component reduction with its finite
residual sum partitioned into low-degree, high-degree, and not-yet-certified
pieces.  The statement is still unconditional and refers only to actual
minimal primes and literal eventual Hilbert polynomials.
-/

namespace TranslatedDepthSeven

noncomputable section

open MvPolynomial Published

attribute [local instance] MvPolynomial.gradedAlgebra

local instance strictRankAtMostSixDegreeSplitClassicalDecidablePred
    {A : Type*} (q : A → Prop) : DecidablePred q := Classical.decPred q

/-- The strongest exact degree-split estimate currently available for the
literal normalized rank-at-most-six Finset. -/
theorem exists_strictRankAtMostSix_card_le_fourthPower_add_degreeSplit
    (equations : Finset (MvPolynomial (Fin 13) ℤ)) (degree : ℕ)
    (hI : IsIntegralProjectiveVariety
      (N := 12) (rationalDepthSevenEquationIdeal equations) 5 degree) :
    ∃ E : Finset (MvPolynomial (Fin 13) ℚ),
      ∃ hEhomogeneous : ∀ f ∈ E, ∃ d : ℕ, f.IsHomogeneous d,
      ∃ C : DepthSevenJacobianChartIndex E,
      ∃ K : ℕ,
        Ideal.span (E : Set (MvPolynomial (Fin 13) ℚ)) =
            rationalDepthSevenEquationIdeal equations ∧
        C.determinant ∉ rationalDepthSevenEquationIdeal equations ∧
        (∀ (Q : JacobianExceptionalComponent E),
          Q ∈ topProjectiveJacobianExceptionalComponents E hEhomogeneous →
          (jacobianExceptionalComponentNormalization
                E hEhomogeneous Q).parameterCount = 5 ∧
            Q.1.IsHomogeneous
              (MvPolynomial.homogeneousSubmodule (Fin 13) ℚ) ∧
            IsSaturatedByProjectiveIrrelevantIdeal Q.1 ∧
            Q.1.IsPrime ∧
            ringKrullDim (MvPolynomial (Fin 13) ℚ ⧸ Q.1) < 6 ∧
            ∀ r d : ℕ, HasProjectiveDimensionDegree Q.1 r d → r = 4) ∧
        ∀ (p : Parameters) (x₀ : IntVector 13) (CF : ℕ),
          let componentPoints := fun Q : JacobianExceptionalComponent E ↦
            ((depthSevenNormalizedDisplacementFinset
                p x₀ equations CF).filter fun z ↦
              (fun i ↦ (integralAffineMap x₀ z p.m i : ℚ)) ∈
                affineIdealZeroLocus Q.1).card
          (depthSevenNormalizedRankAtMostSixFinset
              p x₀ equations CF).card ≤
            K * (surfaceTangentNaturalSide p) ^ 4 +
              (∑ Q ∈ lowDegreeTopProjectiveJacobianExceptionalComponents
                    E hEhomogeneous, componentPoints Q) +
              (∑ Q ∈ highDegreeTopProjectiveJacobianExceptionalComponents
                    E hEhomogeneous, componentPoints Q) +
              ∑ Q ∈ uncertifiedTopProjectiveJacobianExceptionalComponents
                    E hEhomogeneous, componentPoints Q := by
  classical
  obtain ⟨E, hEhomogeneous, C, K, hspan, hdeterminant,
      hqualification, hbound⟩ :=
    exists_strictRankAtMostSix_card_le_fourthPower_add_projectiveFourfoldComponents
      equations degree hI
  refine ⟨E, hEhomogeneous, C, K, hspan, hdeterminant,
    hqualification, ?_⟩
  intro p x₀ CF
  let componentPoints := fun Q : JacobianExceptionalComponent E ↦
    ((depthSevenNormalizedDisplacementFinset
        p x₀ equations CF).filter fun z ↦
      (fun i ↦ (integralAffineMap x₀ z p.m i : ℚ)) ∈
        affineIdealZeroLocus Q.1).card
  have hsplit :=
    sum_topProjectiveJacobianExceptionalComponents_eq_degreeSplit
      E hEhomogeneous componentPoints
  have h := hbound p x₀ CF
  rw [hsplit] at h
  dsimp only
  simpa only [Nat.add_assoc] using h

end

end TranslatedDepthSeven
