import TranslatedDepthSeven.ConeSectionEliminationGeneric
import TranslatedDepthSeven.ProjectiveConePrimeDimension

/-!
# Consecutive-coordinate projective cone sections

This file supplies the two general graded-algebra facts used by the
isolated-vertex quotient projection: adjoining the unused cone coordinate
preserves degree and raises projective dimension by one, and adjoining that
coordinate commutes with a displayed homogeneous linear section.
-/

namespace TranslatedDepthSeven

noncomputable section

open MvPolynomial Published

attribute [local instance] MvPolynomial.gradedAlgebra

set_option maxHeartbeats 6000000
set_option synthInstance.maxHeartbeats 400000

universe u

/-- The complete projective dimension--degree certificate of a prime
homogeneous ideal passes to its projective cone. -/
theorem hasProjectiveDimensionDegree_projectiveConeFinIdeal
    (K : Type u) [Field K] [CharZero K]
    (N r d : ℕ)
    (I : Ideal (MvPolynomial (Fin (N + 1)) K))
    (hI : I.IsHomogeneous
      (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K))
    (hprime : I.IsPrime)
    (hproj : HasProjectiveDimensionDegree I r d) :
    HasProjectiveDimensionDegree
      (projectiveConeFinIdeal K N I) (r + 1) d := by
  have hOptionDim := ringKrullDim_projectiveConeIdealExtension_eq_succ
    K I hprime hproj.1
  let E := MvPolynomial.renameEquiv K
    (_root_.finSuccEquiv (N + 1)).symm
  have hRenameDim :
      ringKrullDim
          (MvPolynomial (Option (Fin (N + 1))) K ⧸
            projectiveConeIdealExtension I) =
        ringKrullDim
          (MvPolynomial (Fin ((N + 1) + 1)) K ⧸
            projectiveConeFinIdeal K N I) := by
    exact ringKrullDim_eq_of_ringEquiv
      (renameQuotientAlgEquiv K (_root_.finSuccEquiv (N + 1)).symm
        (projectiveConeIdealExtension I)).toRingEquiv
  have hConeDim :
      ringKrullDim
          (MvPolynomial (Fin ((N + 1) + 1)) K ⧸
            projectiveConeFinIdeal K N I) =
        (((r + 1) + 1 : ℕ) : WithBot ℕ∞) := by
    rw [← hRenameDim]
    exact hOptionDim
  exact hasProjectiveDimensionDegree_projectiveConeFinIdeal_of_ringKrullDim
    K N r d I hI hprime hproj hConeDim

/-- Reindexing a zero-first-column matrix by `Fin ≃ Option` recovers its
spatial rows. -/
theorem finSuccReindexedMatrix_prependZeroColumn
    {K : Type u} [Field K] {c N : ℕ}
    (B : Matrix (Fin c) (Fin N) K) :
    finSuccReindexedMatrix (matrixPrependZeroColumn B) =
      fun i j ↦ j.elim 0 (B i) := by
  ext i j
  cases j with
  | none => rfl
  | some j => rfl

/-- Polynomial extension of a row ideal is the row ideal obtained by
prepending one zero column. -/
theorem projectiveConeIdealExtension_indexedRows_eq_prependZero
    {K : Type u} [Field K] {c N : ℕ}
    (B : Matrix (Fin c) (Fin N) K) :
    projectiveConeIdealExtension (indexedMatrixRowLinearIdeal B) =
      (matrixRowLinearIdeal (matrixPrependZeroColumn B)).map
        (MvPolynomial.renameEquiv K (_root_.finSuccEquiv N)) := by
  rw [map_matrixRowLinearIdeal_renameEquiv_finSucc,
    finSuccReindexedMatrix_prependZeroColumn]
  unfold projectiveConeIdealExtension indexedMatrixRowLinearIdeal
  rw [Ideal.map_span]
  apply congrArg Ideal.span
  ext f
  constructor
  · rintro ⟨g, ⟨i, rfl⟩, rfl⟩
    refine ⟨i, ?_⟩
    unfold indexedMatrixRowLinearPolynomial
    rw [Fintype.sum_option]
    simp
  · rintro ⟨i, rfl⟩
    refine ⟨indexedMatrixRowLinearPolynomial B i, ⟨i, rfl⟩, ?_⟩
    unfold indexedMatrixRowLinearPolynomial
    rw [Fintype.sum_option]
    simp

/-- Adjoining an unused first column commutes with taking the cone over a
linear section. -/
theorem projectiveConeFinIdeal_sup_rows_eq
    {K : Type u} [Field K] {c N : ℕ}
    (J : Ideal (MvPolynomial (Fin (N + 1)) K))
    (B : Matrix (Fin c) (Fin (N + 1)) K) :
    projectiveConeFinIdeal K N
        (J ⊔ indexedMatrixRowLinearIdeal B) =
      projectiveConeFinIdeal K N J ⊔
        matrixRowLinearIdeal (matrixPrependZeroColumn B) := by
  let E := MvPolynomial.renameEquiv K (_root_.finSuccEquiv (N + 1))
  apply E.toRingEquiv.idealComapOrderIso.symm.injective
  simp only [RingEquiv.idealComapOrderIso_symm_apply]
  change
    (projectiveConeFinIdeal K N
      (J ⊔ indexedMatrixRowLinearIdeal B)).map E =
    (projectiveConeFinIdeal K N J ⊔
      matrixRowLinearIdeal (matrixPrependZeroColumn B)).map E
  rw [Ideal.map_sup]
  have hcone (I : Ideal (MvPolynomial (Fin (N + 1)) K)) :
      (projectiveConeFinIdeal K N I).map E =
        projectiveConeIdealExtension I := by
    unfold projectiveConeFinIdeal
    exact Ideal.map_of_equiv
      (MvPolynomial.renameEquiv K
        (_root_.finSuccEquiv (N + 1)).symm).toRingEquiv
  rw [hcone, hcone]
  have hsup :
      projectiveConeIdealExtension
          (J ⊔ indexedMatrixRowLinearIdeal B) =
        projectiveConeIdealExtension J ⊔
          projectiveConeIdealExtension
            (indexedMatrixRowLinearIdeal B) := by
    unfold projectiveConeIdealExtension
    rw [Ideal.map_sup]
  rw [hsup, projectiveConeIdealExtension_indexedRows_eq_prependZero]

/-- A minimal component of a base section gives a minimal component of the
corresponding source-cone section. -/
theorem projectiveConeFinIdeal_mem_minimalPrimes_sup_rows
    {K : Type u} [Field K] {c N : ℕ}
    (J : Ideal (MvPolynomial (Fin (N + 1)) K))
    (B : Matrix (Fin c) (Fin (N + 1)) K)
    (R : Ideal (MvPolynomial (Fin (N + 1)) K))
    (hR : R ∈ (J ⊔ indexedMatrixRowLinearIdeal B).minimalPrimes) :
    projectiveConeFinIdeal K N R ∈
      (projectiveConeFinIdeal K N J ⊔
        matrixRowLinearIdeal (matrixPrependZeroColumn B)).minimalPrimes := by
  have hcone : projectiveConeIdealExtension R ∈
      (projectiveConeIdealExtension
        (J ⊔ indexedMatrixRowLinearIdeal B)).minimalPrimes := by
    let e := MvPolynomial.optionEquivLeft K (Fin (N + 1))
    have hmap : (R.map Polynomial.C) ∈
        ((J ⊔ indexedMatrixRowLinearIdeal B).map Polynomial.C).minimalPrimes := by
      letI : R.IsPrime := Ideal.minimalPrimes_isPrime hR
      refine ⟨⟨Ideal.isPrime_map_C_iff_isPrime R |>.2 inferInstance,
        Ideal.map_mono hR.1.2⟩, ?_⟩
      intro Q hQ hQR
      have hcomPrime : (Q.comap Polynomial.C).IsPrime := hQ.1.comap _
      have hbase : J ⊔ indexedMatrixRowLinearIdeal B ≤ Q.comap Polynomial.C :=
        (Ideal.map_le_iff_le_comap).mp hQ.2
      have hcomR : Q.comap Polynomial.C ≤ R := by
        intro f hf
        have hCf : Polynomial.C f ∈ R.map Polynomial.C := hQR hf
        simpa using (Ideal.mem_map_C_iff.mp hCf 0)
      have hRcom : R ≤ Q.comap Polynomial.C := hR.2 ⟨hcomPrime, hbase⟩ hcomR
      exact (Ideal.map_le_iff_le_comap).mpr hRcom
    have hfwd : (projectiveConeIdealExtension R).map e ∈
        ((projectiveConeIdealExtension
          (J ⊔ indexedMatrixRowLinearIdeal B)).map e).minimalPrimes := by
      rw [map_projectiveConeIdealExtension_optionEquivLeft,
        map_projectiveConeIdealExtension_optionEquivLeft]
      exact hmap
    have hback := map_mem_minimalPrimes_of_ringEquiv_between
      e.symm.toRingEquiv hfwd
    have hundoR : ((projectiveConeIdealExtension R).map e).map e.symm =
        projectiveConeIdealExtension R := Ideal.map_of_equiv e.toRingEquiv
    have hundoBase :
        ((projectiveConeIdealExtension
          (J ⊔ indexedMatrixRowLinearIdeal B)).map e).map e.symm =
            projectiveConeIdealExtension
              (J ⊔ indexedMatrixRowLinearIdeal B) :=
      Ideal.map_of_equiv e.toRingEquiv
    change
      ((projectiveConeIdealExtension R).map e).map e.symm ∈
        (((projectiveConeIdealExtension
          (J ⊔ indexedMatrixRowLinearIdeal B)).map e).map e.symm).minimalPrimes
      at hback
    rw [hundoR, hundoBase] at hback
    exact hback
  let E := MvPolynomial.renameEquiv K
    (_root_.finSuccEquiv (N + 1)).symm
  have hrenamed := map_mem_minimalPrimes_of_ringEquiv_between
    E.toRingEquiv hcone
  rw [← projectiveConeFinIdeal_sup_rows_eq J B]
  exact hrenamed

end

end TranslatedDepthSeven
