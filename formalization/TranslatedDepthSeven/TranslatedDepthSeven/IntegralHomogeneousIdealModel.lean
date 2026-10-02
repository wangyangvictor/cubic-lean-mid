import TranslatedDepthSeven.FiniteHomogeneousIdealGenerators
import TranslatedDepthSeven.StrictRootTheorem

/-!
# Integral homogeneous equations for a rational homogeneous ideal

This file combines two elementary operations which are needed before the
projective variety can be used as a literal integral equation family:

* choose finitely many homogeneous generators of the rational ideal;
* clear the coefficients of each generator independently.

Because every clearing denominator is a nonzero rational scalar, extension
of the resulting integral ideal back to `ℚ` is exactly the original ideal.
Thus this is equality of ideals, not merely equality of point sets.
-/

namespace TranslatedDepthSeven

noncomputable section

open MvPolynomial

universe v

local instance integralModelMvPolynomialGradedAlgebra {σ : Type v} :
    GradedAlgebra (MvPolynomial.homogeneousSubmodule σ ℚ) :=
  MvPolynomial.gradedAlgebra

/-- Coefficientwise denominator clearing preserves homogeneity exactly. -/
theorem clearRationalMvPolynomial_isHomogeneous {σ : Type v}
    {f : MvPolynomial σ ℚ} {d : ℕ} (hf : f.IsHomogeneous d) :
    (clearRationalMvPolynomial f).IsHomogeneous d := by
  apply MvPolynomial.IsHomogeneous.of_map
      (f := Int.castRingHom ℚ) Int.cast_injective
  rw [map_clearRationalMvPolynomial]
  exact hf.C_mul _

/-- Clear the coefficients of a finite rational equation family. -/
def clearedIntegralEquationFinset {σ : Type v}
    (equations : Finset (MvPolynomial σ ℚ)) :
    Finset (MvPolynomial σ ℤ) := by
  classical
  exact equations.image clearRationalMvPolynomial

/-- Every cleared equation remains homogeneous of the same displayed
degree as the rational equation from which it came. -/
theorem clearedIntegralEquationFinset_each_isHomogeneous {σ : Type v}
    (equations : Finset (MvPolynomial σ ℚ))
    (hhom : ∀ f ∈ equations, ∃ d : ℕ, f.IsHomogeneous d)
    {g : MvPolynomial σ ℤ}
    (hg : g ∈ clearedIntegralEquationFinset equations) :
    ∃ d : ℕ, g.IsHomogeneous d := by
  classical
  obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp hg
  obtain ⟨d, hfd⟩ := hhom f hf
  exact ⟨d, clearRationalMvPolynomial_isHomogeneous hfd⟩

/-- After extension of coefficients back to `ℚ`, clearing each member of a
finite equation family leaves its generated ideal exactly unchanged. -/
theorem map_finiteEquationIdeal_clearedIntegralEquationFinset
    {σ : Type v} (equations : Finset (MvPolynomial σ ℚ)) :
    Ideal.map (MvPolynomial.map (Int.castRingHom ℚ))
        (Ideal.span
          (clearedIntegralEquationFinset equations :
            Set (MvPolynomial σ ℤ))) =
      finiteEquationIdeal equations := by
  classical
  let φ : MvPolynomial σ ℤ →+* MvPolynomial σ ℚ :=
    MvPolynomial.map (Int.castRingHom ℚ)
  let J : Ideal (MvPolynomial σ ℚ) :=
    Ideal.map φ
      (Ideal.span
        (clearedIntegralEquationFinset equations :
          Set (MvPolynomial σ ℤ)))
  change J = finiteEquationIdeal equations
  apply le_antisymm
  · change Ideal.map φ
        (Ideal.span
          (clearedIntegralEquationFinset equations :
            Set (MvPolynomial σ ℤ))) ≤ finiteEquationIdeal equations
    rw [finiteEquationIdeal, Ideal.map_span]
    apply Ideal.span_le.mpr
    rintro _ ⟨g, hg, rfl⟩
    rw [Finset.mem_coe, clearedIntegralEquationFinset,
      Finset.mem_image] at hg
    obtain ⟨f, hf, rfl⟩ := hg
    change MvPolynomial.map (Int.castRingHom ℚ)
      (clearRationalMvPolynomial f) ∈ finiteEquationIdeal equations
    rw [map_clearRationalMvPolynomial]
    exact (finiteEquationIdeal equations).mul_mem_left _
      (Ideal.subset_span hf)
  · rw [finiteEquationIdeal]
    apply Ideal.span_le.mpr
    intro f hf
    have hf' : f ∈ equations := by
      simpa only [Finset.mem_coe] using hf
    have hclearMem : clearRationalMvPolynomial f ∈
        Ideal.span
          (clearedIntegralEquationFinset equations :
            Set (MvPolynomial σ ℤ)) := by
      apply Ideal.subset_span
      rw [Finset.mem_coe, clearedIntegralEquationFinset,
        Finset.mem_image]
      exact ⟨f, hf', rfl⟩
    have hmapped : φ (clearRationalMvPolynomial f) ∈ J :=
      Ideal.mem_map_of_mem φ hclearMem
    change MvPolynomial.map (Int.castRingHom ℚ)
      (clearRationalMvPolynomial f) ∈ J at hmapped
    rw [map_clearRationalMvPolynomial] at hmapped
    have hD : (mvPolynomialRationalCommonDenominator f : ℚ) ≠ 0 := by
      exact_mod_cast (mvPolynomialRationalCommonDenominator_pos f).ne'
    have hscaled :
        MvPolynomial.C
            (mvPolynomialRationalCommonDenominator f : ℚ)⁻¹ *
          (MvPolynomial.C
            (mvPolynomialRationalCommonDenominator f : ℚ) * f) ∈ J :=
      J.mul_mem_left
        (MvPolynomial.C
          (mvPolynomialRationalCommonDenominator f : ℚ)⁻¹) hmapped
    have heq :
        MvPolynomial.C
            (mvPolynomialRationalCommonDenominator f : ℚ)⁻¹ *
          (MvPolynomial.C
            (mvPolynomialRationalCommonDenominator f : ℚ) * f) = f := by
      rw [← mul_assoc, ← MvPolynomial.C_mul, inv_mul_cancel₀ hD]
      simp
    rw [heq] at hscaled
    exact hscaled

/-- Every rational homogeneous ideal admits a finite integral homogeneous
equation family whose coefficient extension generates that ideal exactly. -/
theorem exists_integral_homogeneous_equations_map_ideal_eq
    {σ : Type v} [Fintype σ]
    (I : Ideal (MvPolynomial σ ℚ))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ ℚ)) :
    ∃ equations : Finset (MvPolynomial σ ℤ),
      (∀ f ∈ equations, ∃ d : ℕ, f.IsHomogeneous d) ∧
      Ideal.map (MvPolynomial.map (Int.castRingHom ℚ))
        (Ideal.span (equations : Set (MvPolynomial σ ℤ))) = I := by
  obtain ⟨rationalEquations, hhom, hspan⟩ :=
    exists_finite_homogeneous_generators I hI
  refine ⟨clearedIntegralEquationFinset rationalEquations, ?_, ?_⟩
  · intro f hf
    exact clearedIntegralEquationFinset_each_isHomogeneous
      rationalEquations hhom hf
  · rw [map_finiteEquationIdeal_clearedIntegralEquationFinset, hspan]

end

end TranslatedDepthSeven
