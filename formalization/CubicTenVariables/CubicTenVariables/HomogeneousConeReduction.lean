import CubicTenVariables.PolynomialExponentialFamily
import CubicTenVariables.DegreeSpanReduction
import CubicTenVariables.IntegralConeNormalization

/-! Homogeneity of a rational equation ideal gives scalar stability of
the actual reduced equations outside one fixed integer. The generators
themselves need not be homogeneous. We clear ideal-membership certificates
for their finitely many homogeneous components before reducing coefficients.
No primality, geometric integrality, finite-field, or literature premise
is used. -/

set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.HomogeneousConeReduction

open MvPolynomial PolynomialExponentialFamily
open scoped BigOperators Classical
attribute [local instance] MvPolynomial.gradedAlgebra

/-- All homogeneous components of the original integral generators vanish
on their actual reduced zero set, uniformly outside one fixed integer. -/
theorem exists_component_reduction {n t : ℕ}
    (G : Fin t → MvPolynomial (Fin n) ℤ)
    (hhom : (baseIdeal G).IsHomogeneous (homogeneousSubmodule (Fin n) ℚ)) :
    ∃ D : ℕ, 1 ≤ D ∧ ∀ p : ℕ, ¬ p ∣ D →
      ∀ (K : Type*) [Field K] [CharP K p] (v : Fin n → K),
        (∀ i, eval v (map (Int.castRingHom K) (G i)) = 0) →
        ∀ (i : Fin t) (d : ℕ),
          eval v (map (Int.castRingHom K) (homogeneousComponent d (G i))) = 0 := by
  let H : (Σ i : Fin t, Fin ((G i).totalDegree + 1)) → MvPolynomial (Fin n) ℤ :=
    fun j => homogeneousComponent j.2.val (G j.1)
  have hH (j : Σ i : Fin t, Fin ((G i).totalDegree + 1)) :
      map (Int.castRingHom ℚ) (H j) ∈ baseIdeal G := by
    dsimp [H]
    rw [IntegralConeNormalization.map_homogeneousComponent]
    have hmem := hhom j.2.val
      (Ideal.subset_span (Set.mem_range_self j.1))
    change (MvPolynomial.decomposition.decompose'
      (map (Int.castRingHom ℚ) (G j.1)) j.2.val : MvPolynomial (Fin n) ℚ)
        ∈ baseIdeal G at hmem
    simpa only [MvPolynomial.decomposition.decompose'_apply] using hmem
  obtain ⟨D, hD, hreduce⟩ := DegreeSpanReduction.exists_uniform_family_reduction G H hH
  refine ⟨D, hD, ?_⟩
  intro p hp K _ _ v hv i d
  by_cases hd : d < (G i).totalDegree + 1
  · exact hreduce p hp K v hv ⟨i, ⟨d, hd⟩⟩
  · rw [homogeneousComponent_eq_zero d (G i) (by omega)]
    simp

/-- A single prime exclusion makes the common zero set of the actual
reduced generators stable under every scalar, including zero. -/
theorem exists_scalar_stability {n t : ℕ}
    (G : Fin t → MvPolynomial (Fin n) ℤ)
    (hhom : (baseIdeal G).IsHomogeneous (homogeneousSubmodule (Fin n) ℚ)) :
    ∃ D : ℕ, 1 ≤ D ∧ ∀ p : ℕ, ¬ p ∣ D →
      ∀ (K : Type*) [Field K] [CharP K p] (v : Fin n → K),
        (∀ i, eval v (map (Int.castRingHom K) (G i)) = 0) →
        ∀ (a : K) (i : Fin t),
          eval (a • v) (map (Int.castRingHom K) (G i)) = 0 := by
  obtain ⟨D, hD, hreduce⟩ := exists_component_reduction G hhom
  refine ⟨D, hD, ?_⟩
  intro p hp K _ _ v hv a i
  rw [← eval₂_eq_eval_map, ← sum_homogeneousComponent (G i), eval₂_sum]
  apply Finset.sum_eq_zero
  intro d _hd
  rw [CubicGradientScaling.homogeneous_eval₂_smul
    (homogeneousComponent d (G i)) (homogeneousComponent_isHomogeneous d (G i))]
  rw [eval₂_eq_eval_map, hreduce p hp K v hv i d, mul_zero]

end CubicTenVariables.HomogeneousConeReduction
