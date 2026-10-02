import CubicTenVariables.HomogeneousFiniteCutAlgebra
import CubicTenVariables.ProperHomogeneousNormalization

/-! Literal finite linear-cut certificates for the dimension of a homogeneous
equation quotient. The bound holds over every field. Conversely, over an
infinite field, homogeneous Noether normalization supplies exactly the desired
number of cuts, with zero forms used for padding. Neither reducedness nor a
nonzero quotient is assumed. -/

set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.FiniteLinearCutCertificates
open MvPolynomial
attribute [local instance] MvPolynomial.gradedAlgebra

variable {K : Type*} [Field K] {n s : ℕ}

/-- The characteristic-free dimension bound for the actual equation ideal.
The equations need only be individually homogeneous; their degrees may be zero. -/
theorem equation_dimension_le_of_finite_linear_cuts
    {ι : Type*} (f : ι → MvPolynomial (Fin n) K) (e : ι → ℕ)
    (hf : ∀ i, (f i).IsHomogeneous (e i))
    (L : Fin s → MvPolynomial (Fin n) K)
    (hL : ∀ j, (L j).IsHomogeneous 1)
    [Module.Finite K (MvPolynomial (Fin n) K ⧸
      (Ideal.span (Set.range f) ⊔ Ideal.span (Set.range L)))] :
    ringKrullDim (MvPolynomial (Fin n) K ⧸ Ideal.span (Set.range f)) ≤
      (s : WithBot ℕ∞) := by
  apply HomogeneousFiniteCutAlgebra.quotient_dimension_le_of_finite_linear_cuts
    (Ideal.span (Set.range f)) _ L hL
  apply Ideal.homogeneous_span
  rintro _ ⟨i, rfl⟩
  exact ⟨e i, hf i⟩

/-- A small-dimensional homogeneous quotient has a finite quotient after
exactly `s` homogeneous linear cuts. The infinite-field assumption is used
only to choose homogeneous linear Noether normalization. -/
theorem exists_finite_linear_cuts [Infinite K]
    (I : Ideal (MvPolynomial (Fin n) K))
    (hI : I.IsHomogeneous (homogeneousSubmodule (Fin n) K))
    (hdim : ringKrullDim (MvPolynomial (Fin n) K ⧸ I) ≤ (s : WithBot ℕ∞)) :
    ∃ L : Fin s → MvPolynomial (Fin n) K,
      (∀ j, (L j).IsHomogeneous 1) ∧
      Module.Finite K (MvPolynomial (Fin n) K ⧸
        (I ⊔ Ideal.span (Set.range L))) := by
  classical
  by_cases htop : I = ⊤
  · subst I
    refine ⟨fun _ => 0, fun _ => isHomogeneous_zero _ _ _, ?_⟩
    have hcut : (⊤ : Ideal (MvPolynomial (Fin n) K)) ⊔
        Ideal.span (Set.range (fun _ : Fin s => (0 : MvPolynomial (Fin n) K))) = ⊤ :=
      top_sup_eq _
    rw [hcut]
    letI : Subsingleton (MvPolynomial (Fin n) K ⧸ (⊤ : Ideal _)) :=
      Ideal.Quotient.subsingleton_iff.mpr rfl
    exact Module.Finite.of_finite
  obtain ⟨D, hD⟩ :=
    ProperHomogeneousNormalization.exists_homogeneousLinearNormalizationData_parameterCount_le
      n I htop hI s hdim
  let L : Fin s → MvPolynomial (Fin n) K := fun j =>
    if hj : j.val < D.parameterCount then D.forms ⟨j.val, hj⟩ else 0
  have hL : ∀ j, (L j).IsHomogeneous 1 := by
    intro j
    dsimp only [L]
    split
    · exact D.forms_isHomogeneous _
    · exact isHomogeneous_zero _ _ _
  have hspan : Ideal.span (Set.range L) = Ideal.span (Set.range D.forms) := by
    apply le_antisymm
    · apply Ideal.span_le.mpr
      rintro _ ⟨j, rfl⟩
      dsimp only [L]
      split
      · exact Ideal.subset_span (Set.mem_range_self _)
      · exact Ideal.zero_mem _
    · apply Ideal.span_le.mpr
      rintro _ ⟨j, rfl⟩
      have hLj : L (Fin.castLE hD j) = D.forms j := by simp [L, j.isLt]
      rw [← hLj]
      exact Ideal.subset_span (Set.mem_range_self _)
  refine ⟨L, hL, ?_⟩
  rw [hspan]
  exact HomogeneousPowerCertificates.finite_cut_quotient I D

/-- The exact algebraic criterion used by universal coefficient matrices.
The ideal may be nonreduced or equal to the whole ring. -/
theorem dimension_le_iff_exists_finite_linear_cuts [Infinite K]
    (I : Ideal (MvPolynomial (Fin n) K))
    (hI : I.IsHomogeneous (homogeneousSubmodule (Fin n) K)) :
    ringKrullDim (MvPolynomial (Fin n) K ⧸ I) ≤ (s : WithBot ℕ∞) ↔
      ∃ L : Fin s → MvPolynomial (Fin n) K,
        (∀ j, (L j).IsHomogeneous 1) ∧
        Module.Finite K (MvPolynomial (Fin n) K ⧸
          (I ⊔ Ideal.span (Set.range L))) := by
  constructor
  · exact exists_finite_linear_cuts I hI
  · rintro ⟨L, hL, hfinite⟩
    letI := hfinite
    exact HomogeneousFiniteCutAlgebra.quotient_dimension_le_of_finite_linear_cuts I hI L hL

end CubicTenVariables.FiniteLinearCutCertificates
