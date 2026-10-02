import TranslatedDepthSeven.BoundedIntegralDistinguishedNormalizationInternal

/-!
# One fixed finite integral list for distinguished normalization

The list is an explicit box of integer matrices. It is defined before
the coefficient field or source ideal, and every eligible source has an
injective finite normalization map from a matrix in that same list.
-/

namespace TranslatedDepthSeven
noncomputable section
open MvPolynomial Matrix Published
open scoped BigOperators
attribute [local instance] MvPolynomial.gradedAlgebra
set_option maxHeartbeats 2500000
set_option synthInstance.maxHeartbeats 300000

def boundedIntegralDistinguishedNormalizationMatrices (n r D : ℕ) :
    Finset (Matrix (Fin (r + 1)) (Fin (n + 1)) ℤ) :=
  Fintype.piFinset fun _ : Fin (r + 1) ↦
    Fintype.piFinset fun _ : Fin (n + 1) ↦
      Finset.Icc (-((D + 1) ^ n : ℕ) : ℤ) (((D + 1) ^ n : ℕ) : ℤ)

theorem mem_boundedIntegralDistinguishedNormalizationMatrices_of_rowNorm
    {n r D : ℕ} (A : Matrix (Fin (r + 1)) (Fin (n + 1)) ℤ)
    (hA : ∀ i, ∑ j, (A i j).natAbs ≤ (D + 1) ^ n) :
    A ∈ boundedIntegralDistinguishedNormalizationMatrices n r D := by
  classical
  apply Fintype.mem_piFinset.mpr
  intro i
  apply Fintype.mem_piFinset.mpr
  intro j
  apply Finset.mem_Icc.mpr
  have hentry : (A i j).natAbs ≤ (D + 1) ^ n :=
    (Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ j)).trans (hA i)
  have hcast : |A i j| ≤ (((D + 1) ^ n : ℕ) : ℤ) := by
    simpa only [Int.natCast_natAbs] using (Int.ofNat_le.mpr hentry)
  exact abs_le.mp hcast

/-- The matrix list depends only on ambient dimension, projective dimension
and degree bound. In particular it is independent of the coefficient field,
all coefficients of the ideal, and every translated counting parameter. -/
theorem exists_mem_boundedIntegralDistinguishedNormalizationMatrices
    {K : Type*} [Field K] [CharZero K] (n : ℕ) {r d D : ℕ}
    (I : Ideal (MvPolynomial (Fin (n + 1)) K))
    (hprime : I.IsPrime)
    (hhom : I.IsHomogeneous (homogeneousSubmodule (Fin (n + 1)) K))
    (hX : X 0 ∉ I) (hdegree : HasProjectiveDimensionDegree I r d) (hdD : d ≤ D) :
    ∃ A ∈ boundedIntegralDistinguishedNormalizationMatrices n r D,
      (∀ j, A 0 j = if j = 0 then 1 else 0) ∧
      let h := (Ideal.Quotient.mkₐ K I).comp
        (aeval (indexedMatrixRowLinearPolynomial (A.map (Int.castRingHom K))))
      Function.Injective h ∧ h.Finite := by
  obtain ⟨A, hAnorm, hAfirst, hAinj, hAfin⟩ :=
    exists_boundedIntegralDistinguishedNormalization n I hprime hhom hX hdegree hdD
  exact ⟨A, mem_boundedIntegralDistinguishedNormalizationMatrices_of_rowNorm A hAnorm,
    hAfirst, hAinj, hAfin⟩

/-- The first parameter of the literal matrix normalization is exactly X0. -/
theorem homogeneousLinearNormalizationDataOfIntegralMatrix_fixes_first
    {K : Type*} [Field K] {r n : ℕ}
    (I : Ideal (MvPolynomial (Fin (n + 1)) K))
    (A : Matrix (Fin (r + 1)) (Fin (n + 1)) ℤ)
    (hfirst : ∀ j, A 0 j = if j = 0 then 1 else 0)
    (hinjective : Function.Injective ((Ideal.Quotient.mkₐ K I).comp
      (aeval (indexedMatrixRowLinearPolynomial (A.map (Int.castRingHom K))))))
    (hfinite : ((Ideal.Quotient.mkₐ K I).comp
      (aeval (indexedMatrixRowLinearPolynomial (A.map (Int.castRingHom K))))).Finite) :
    (homogeneousLinearNormalizationDataOfIntegralMatrix I A hinjective hfinite).forms
      ⟨0, by change 0 < r + 1; omega⟩ = X 0 := by
  classical
  change (∑ j, C ((A 0 j : ℤ) : K) * X j) = X 0
  simp [hfirst]

universe u

/-- The same conclusion with the quantifiers displaying that the finite
list is chosen before the field and the source ideal. -/
theorem exists_uniform_boundedIntegralDistinguishedNormalizationMenu (n r D : ℕ) :
    ∃ menu : Finset (Matrix (Fin (r + 1)) (Fin (n + 1)) ℤ),
      ∀ (K : Type u) [Field K] [CharZero K]
        (I : Ideal (MvPolynomial (Fin (n + 1)) K)),
        I.IsPrime → I.IsHomogeneous (homogeneousSubmodule (Fin (n + 1)) K) →
        X 0 ∉ I → ∀ d : ℕ, HasProjectiveDimensionDegree I r d → d ≤ D →
          ∃ A ∈ menu, (∀ j, A 0 j = if j = 0 then 1 else 0) ∧
            let h := (Ideal.Quotient.mkₐ K I).comp
              (aeval (indexedMatrixRowLinearPolynomial (A.map (Int.castRingHom K))))
            Function.Injective h ∧ h.Finite := by
  refine ⟨boundedIntegralDistinguishedNormalizationMatrices n r D, ?_⟩
  intro K hK hChar I hprime hhom hX d hdegree hdD
  exact exists_mem_boundedIntegralDistinguishedNormalizationMatrices
    n I hprime hhom hX hdegree hdD

end
end TranslatedDepthSeven
