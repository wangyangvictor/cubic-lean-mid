import CubicTenVariables.HomogeneousConeTraceRestriction
import TranslatedDepthSeven.IntegralHomogeneousIdealModel

/-! An actual integral homogeneous equation separating a cone from a
homogeneous closed locus which does not contain it. Denominator clearing
makes the equation vanish on the literal reduced closed locus outside one
fixed integer. This supplies the equation used to restrict a trace open. -/

set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.HomogeneousClosedLocusAvoidance
open MvPolynomial PolynomialExponentialFamily
open scoped Classical
attribute [local instance] MvPolynomial.gradedAlgebra

theorem exists_equation {n : ℕ} (I J : Ideal (MvPolynomial (Fin n) ℚ))
    (hJ : J.IsHomogeneous (homogeneousSubmodule (Fin n) ℚ)) (hnot : ¬ J ≤ I) :
    ∃ (Q : ParameterPolynomial n) (e : ℕ), Q.IsHomogeneous e ∧
      map (Int.castRingHom ℚ) Q ∈ J ∧ map (Int.castRingHom ℚ) Q ∉ I := by
  obtain ⟨E,hE,heq⟩ := TranslatedDepthSeven.exists_integral_homogeneous_equations_map_ideal_eq J hJ
  have hgen (Q : ParameterPolynomial n) (hQ : Q ∈ E) :
      map (Int.castRingHom ℚ) Q ∈ J := by
    rw [← heq]
    exact Ideal.mem_map_of_mem _ (Ideal.subset_span hQ)
  by_contra h
  push_neg at h
  apply hnot
  rw [← heq, Ideal.map_span]
  apply Ideal.span_le.mpr
  rintro _ ⟨Q,hQ,rfl⟩
  obtain ⟨e,he⟩ := hE Q hQ
  exact h Q e he (hgen Q hQ)

/-- The separator vanishes on the actual reduction of the excluded
closed locus, with the prime exclusion fixed before all fields and points. -/
theorem exists_equation_good_reduction {n t : ℕ}
    (I : Ideal (MvPolynomial (Fin n) ℚ)) (H : Fin t → ParameterPolynomial n)
    (hH : (baseIdeal H).IsHomogeneous (homogeneousSubmodule (Fin n) ℚ))
    (hnot : ¬ baseIdeal H ≤ I) :
    ∃ (Q : ParameterPolynomial n) (e D : ℕ), Q.IsHomogeneous e ∧
      map (Int.castRingHom ℚ) Q ∈ baseIdeal H ∧ map (Int.castRingHom ℚ) Q ∉ I ∧
      1 ≤ D ∧ ∀ p : ℕ, ¬ p ∣ D →
        ∀ (K : Type*) [Field K] [CharP K p] (v : Fin n → K),
          (∀ a, eval v (map (Int.castRingHom K) (H a)) = 0) →
          eval v (map (Int.castRingHom K) Q) = 0 := by
  obtain ⟨Q,e,hQ,hmem,hnotQ⟩ := exists_equation I (baseIdeal H) hH hnot
  obtain ⟨D,hD,hreduce⟩ := DegreeSpanReduction.exists_uniform_reduction H Q hmem
  exact ⟨Q,e,D,hQ,hmem,hnotQ,hD,hreduce⟩

/-- Divisibility of the chosen open equation by the separator excludes
every point of the reduced closed locus, not merely its rational points. -/
theorem not_on_excluded_locus {n s t : ℕ}
    (G : Fin s → ParameterPolynomial n) (H : Fin t → ParameterPolynomial n)
    (Q h : ParameterPolynomial n) (hQh : Q ∣ h)
    (K : Type*) [Field K] [Fintype K] (v : Fin n → K)
    (hvanish : (∀ a, eval v (map (Int.castRingHom K) (H a)) = 0) →
      eval v (map (Int.castRingHom K) Q) = 0)
    (hv : v ∈ parameterPoints G h K) :
    ¬ (∀ a, eval v (map (Int.castRingHom K) (H a)) = 0) := by
  intro hH
  exact HomogeneousConeTraceRestriction.eval_ne_zero_of_dvd Q h hQh K v
    ((mem_parameterPoints G h K v).mp hv).2 (hvanish hH)

end CubicTenVariables.HomogeneousClosedLocusAvoidance
