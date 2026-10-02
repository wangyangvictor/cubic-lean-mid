import TranslatedDepthSeven.NormalizationJacobianMinorInternal

/-!
# A bounded nonzero Jacobian minor for a projective prime

The normalization data are constructed internally.  The number of
equations in the minor is exactly `N-r` for a projective `r`-fold in
projective `N`-space.  No ideal-generation assertion is made.
-/

namespace TranslatedDepthSeven

noncomputable section

open MvPolynomial Published

attribute [local instance] MvPolynomial.gradedAlgebra

set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 500000

/-- An ordinary Jacobian minor of the expected size, formed from
equations of degree at most the projective degree, is nonzero in the
source coordinate domain. -/
theorem exists_projectiveDegree_bounded_jacobian_minor
    {K : Type*} [Field K] [CharZero K] {N r d : ℕ}
    (I : Ideal (MvPolynomial (Fin (N + 1)) K))
    (hIprime : I.IsPrime)
    (hIhom : I.IsHomogeneous (homogeneousSubmodule (Fin (N + 1)) K))
    (hdegree : HasProjectiveDimensionDegree I r d) :
    ∃ (F : Fin (N - r) → MvPolynomial (Fin (N + 1)) K)
      (degrees : Fin (N - r) → ℕ)
      (cols : Fin (N - r) → Fin (N + 1)),
      Function.Injective cols ∧
      (∀ j, degrees j ≤ d) ∧
      (∀ j, (F j).IsHomogeneous (degrees j)) ∧
      (∀ j, F j ∈ I) ∧
      (Matrix.of (fun i j ↦ pderiv (cols j) (F i))).det ∉ I ∧
      ((Matrix.of (fun i j ↦ pderiv (cols j) (F i))).det).totalDegree ≤
        (N - r) * (d - 1) := by
  obtain ⟨D⟩ := exists_homogeneousLinearNormalizationData (N + 1) I hIprime hIhom
  have hcount :=
    (homogeneousLinearNormalization_genericRank_le_projectiveDegree I hIprime D hdegree).1
  have hc : N + 1 - D.parameterCount = N - r := by omega
  rw [← hc]
  exact exists_bounded_normalization_jacobian_minor I hIprime hIhom hdegree D

/-- The same result records the homogeneity of the chosen determinant
and bounds its homogeneous degree, not merely its total degree. -/
theorem exists_projectiveDegree_bounded_homogeneous_jacobian_minor
    {K : Type*} [Field K] [CharZero K] {N r d : ℕ}
    (I : Ideal (MvPolynomial (Fin (N + 1)) K))
    (hIprime : I.IsPrime)
    (hIhom : I.IsHomogeneous (homogeneousSubmodule (Fin (N + 1)) K))
    (hdegree : HasProjectiveDimensionDegree I r d) :
    ∃ (F : Fin (N - r) → MvPolynomial (Fin (N + 1)) K)
      (degrees : Fin (N - r) → ℕ)
      (cols : Fin (N - r) → Fin (N + 1)),
      Function.Injective cols ∧
      (∀ j, degrees j ≤ d) ∧
      (∀ j, (F j).IsHomogeneous (degrees j)) ∧
      (∀ j, F j ∈ I) ∧
      (Matrix.of (fun i j ↦ pderiv (cols j) (F i))).det ∉ I ∧
      (Matrix.of (fun i j ↦ pderiv (cols j) (F i))).det.IsHomogeneous
        (∑ j, (degrees j - 1)) ∧
      (∑ j, (degrees j - 1)) ≤ (N - r) * (d - 1) := by
  classical
  obtain ⟨F, degrees, cols, hcols, hdegrees, hFhom, hFmem, hminor, _⟩ :=
    exists_projectiveDegree_bounded_jacobian_minor I hIprime hIhom hdegree
  refine ⟨F, degrees, cols, hcols, hdegrees, hFhom, hFmem, hminor, ?_, ?_⟩
  · exact matrix_det_isHomogeneous_of_row_isHomogeneous _ _
      (fun i j ↦ (hFhom i).pderiv)
  · calc
      (∑ j, (degrees j - 1)) ≤ ∑ _j : Fin (N - r), (d - 1) :=
        Finset.sum_le_sum (fun j _ ↦ Nat.sub_le_sub_right (hdegrees j) 1)
      _ = _ := by simp

end

end TranslatedDepthSeven
