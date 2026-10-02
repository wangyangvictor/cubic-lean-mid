import TranslatedDepthSeven.StrictRankAtMostSixBridge
import TranslatedDepthSeven.JacobianExceptionalProjectiveSplit

/-!
# The exact projective-component split for the strict low-rank cell

This file applies the literal minimal-component decomposition of the
Jacobian-exceptional locus to the exact normalized displacement set.  A
finite homogeneous generating family is selected from the homogeneous prime
ideal supplied by the strict projective input.  Equality of Jacobian row
spans at common zeroes transfers the rank condition from the displayed
integral equations to that family.

The conclusion is unconditional: the low-rank cell is `O(T^4)` apart from a
finite, explicitly displayed sum over actual nonirrelevant minimal primes
having five normalization parameters.  If any such prime has a projective
dimension-and-degree certificate, its projective dimension is forced to be
four.  Thus the residual sum is exactly the projective-fourfold frontier;
no geometric or counting predicate is introduced as a hypothesis.
-/

namespace TranslatedDepthSeven

noncomputable section

open MvPolynomial Published

attribute [local instance] MvPolynomial.gradedAlgebra

local instance strictRankAtMostSixProjectiveSplitClassicalDecidablePred
    {A : Type*} (q : A → Prop) : DecidablePred q := Classical.decPred q

/-- Exact strict low-rank reduction to the finite family of actual
projective-fourfold components.  All objects in the residual sum are chosen
once from the fixed equation ideal, before `p`, `x₀`, or `CF` is introduced.
-/
theorem exists_strictRankAtMostSix_card_le_fourthPower_add_projectiveFourfoldComponents
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
          (depthSevenNormalizedRankAtMostSixFinset
              p x₀ equations CF).card ≤
            K * (surfaceTangentNaturalSide p) ^ 4 +
              ∑ Q ∈ topProjectiveJacobianExceptionalComponents
                    E hEhomogeneous,
                ((depthSevenNormalizedDisplacementFinset
                    p x₀ equations CF).filter fun z ↦
                  (fun i ↦ (integralAffineMap x₀ z p.m i : ℚ)) ∈
                    affineIdealZeroLocus Q.1).card := by
  classical
  have hdata := strictProjectiveInput_consequences equations degree hI
  obtain ⟨E, hEhomogeneous, hEspan⟩ :=
    exists_finite_homogeneous_generators
      (rationalDepthSevenEquationIdeal equations) hdata.1
  have hEspan' : Ideal.span (E : Set (MvPolynomial (Fin 13) ℚ)) =
      rationalDepthSevenEquationIdeal equations := by
    simpa [finiteEquationIdeal] using hEspan
  letI : (rationalDepthSevenEquationIdeal equations).IsPrime :=
    hdata.2.2.1
  obtain ⟨C, hC⟩ :=
    exists_depthSevenJacobianChart_determinant_notMem_of_prime_dimension_six
      E (rationalDepthSevenEquationIdeal equations) hdata.2.2.1
      hEspan' hdata.2.2.2.1
  obtain ⟨K₀, hK₀⟩ :=
    exists_rankAtMostSix_card_le_fourthPower_add_topProjectiveComponents
      E hEhomogeneous (rationalDepthSevenEquationIdeal equations)
      hEspan' C hC hdata.2.2.2.1
  refine ⟨E, hEhomogeneous, C, K₀ * 2 ^ 4,
    hEspan', hC, ?_, ?_⟩
  · intro Q hQ
    have hqualification :=
      mem_topProjectiveJacobianExceptionalComponents_qualification
        E hEhomogeneous (rationalDepthSevenEquationIdeal equations)
        hEspan' C hC hdata.2.2.2.1 hQ
    refine ⟨hqualification.1, hqualification.2.1,
      hqualification.2.2.1, hqualification.2.2.2.1,
      hqualification.2.2.2.2, ?_⟩
    intro r d hprojective
    exact
      projectiveDimension_eq_four_of_mem_topProjectiveJacobianExceptionalComponents
        E hEhomogeneous (rationalDepthSevenEquationIdeal equations)
        hEspan' C hC hdata.2.2.2.1 hQ hprojective
  · intro p x₀ CF
    let Z := depthSevenNormalizedDisplacementFinset p x₀ equations CF
    have hzeroEquations : ∀ z ∈ Z,
        (fun i ↦ (integralAffineMap x₀ z p.m i : ℚ)) ∈
          finiteAffineCommonZeroLocus
            (rationalizedEquationFinset equations) := by
      intro z hz
      exact depthSevenNormalized_mem_rationalizedCommonZeroLocus
        p x₀ equations CF hz
    have hzeroE : ∀ z ∈ Z,
        (fun i ↦ (integralAffineMap x₀ z p.m i : ℚ)) ∈
          finiteAffineCommonZeroLocus E := by
      intro z hz
      rw [← affineIdealZeroLocus_finiteEquationIdeal, hEspan]
      change (fun i ↦ (integralAffineMap x₀ z p.m i : ℚ)) ∈
        affineIdealZeroLocus
          (finiteEquationIdeal (rationalizedEquationFinset equations))
      rw [affineIdealZeroLocus_finiteEquationIdeal]
      exact hzeroEquations z hz
    have heq :
        depthSevenNormalizedRankAtMostSixFinset p x₀ equations CF =
          Z.filter fun z ↦
            (fun i ↦ (integralAffineMap x₀ z p.m i : ℚ)) ∈
              finiteAffineCommonZeroLocus
                (depthSevenJacobianExceptionalEquationFinset E) := by
      rw [depthSevenNormalizedRankAtMostSixFinset_eq_rationalFilter]
      ext z
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨hz, hzexceptional⟩
        refine ⟨hz, (mem_finiteAffineCommonZeroLocus_exceptional_iff E _).mpr
          ⟨hzeroE z hz, ?_⟩⟩
        exact (rankAtMostSix_iff_of_idealSpan_eq
          (rationalizedEquationFinset equations) E _
          (hzeroEquations z hz) (hzeroE z hz)
          (show finiteEquationIdeal (rationalizedEquationFinset equations) =
              finiteEquationIdeal E by
            simpa [finiteEquationIdeal, rationalDepthSevenEquationIdeal]
              using hEspan'.symm)).mp
            ((mem_finiteAffineCommonZeroLocus_exceptional_iff
              (rationalizedEquationFinset equations) _).mp hzexceptional).2
      · rintro ⟨hz, hzexceptional⟩
        refine ⟨hz,
          (mem_finiteAffineCommonZeroLocus_exceptional_iff
            (rationalizedEquationFinset equations) _).mpr
              ⟨hzeroEquations z hz, ?_⟩⟩
        exact (rankAtMostSix_iff_of_idealSpan_eq
          (rationalizedEquationFinset equations) E _
          (hzeroEquations z hz) (hzeroE z hz)
          (show finiteEquationIdeal (rationalizedEquationFinset equations) =
              finiteEquationIdeal E by
            simpa [finiteEquationIdeal, rationalDepthSevenEquationIdeal]
              using hEspan'.symm)).mpr
            ((mem_finiteAffineCommonZeroLocus_exceptional_iff E _).mp
              hzexceptional).2
    have hraw := hK₀ Z x₀ p.m
      (2 * surfaceTangentNaturalSide p) p.hm
      (by
        have hside := one_le_surfaceTangentNaturalSide p
        omega)
      (by
        intro z hz
        exact depthSevenNormalized_coordinate_le_two_surfaceTangentNaturalSide
          p x₀ equations CF hz)
    rw [← heq] at hraw
    calc
      (depthSevenNormalizedRankAtMostSixFinset p x₀ equations CF).card ≤
          K₀ * (2 * surfaceTangentNaturalSide p) ^ 4 +
            ∑ Q ∈ topProjectiveJacobianExceptionalComponents
                  E hEhomogeneous,
              (Z.filter fun z ↦
                (fun i ↦ (integralAffineMap x₀ z p.m i : ℚ)) ∈
                  affineIdealZeroLocus Q.1).card := hraw
      _ = (K₀ * 2 ^ 4) * (surfaceTangentNaturalSide p) ^ 4 +
            ∑ Q ∈ topProjectiveJacobianExceptionalComponents
                  E hEhomogeneous,
              (Z.filter fun z ↦
                (fun i ↦ (integralAffineMap x₀ z p.m i : ℚ)) ∈
                  affineIdealZeroLocus Q.1).card := by ring

end

end TranslatedDepthSeven
