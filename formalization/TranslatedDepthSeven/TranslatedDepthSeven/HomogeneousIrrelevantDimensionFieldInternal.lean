import TranslatedDepthSeven.IntegralProjectiveConeBaseGeometryInternal

/-! # The irrelevant homogeneous prime over any field -/

namespace TranslatedDepthSeven
noncomputable section
open MvPolynomial Published
attribute [local instance] MvPolynomial.gradedAlgebra

variable {K : Type*} [Field K]

theorem projectiveIrrelevantIdeal_eq_ker_constantCoeff_over_field (N : ℕ) :
    projectiveIrrelevantIdeal K N =
      RingHom.ker (MvPolynomial.constantCoeff (σ := Fin (N + 1)) (R := K)) := by
  rw [projectiveIrrelevantIdeal, ← mvPolynomialIrrelevantIdeal_eq_span_X]
  ext f
  change f ∈ HomogeneousIdeal.irrelevant
      (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K) ↔
    MvPolynomial.constantCoeff f = 0
  rw [HomogeneousIdeal.mem_irrelevant_iff]
  change GradedRing.projZeroRingHom
      (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K) f = 0 ↔
    MvPolynomial.constantCoeff f = 0
  rw [projZeroRingHom_homogeneousSubmodule_apply, MvPolynomial.C_eq_zero]

theorem ringKrullDim_quotient_eq_zero_of_irrelevant_le_over_field
    (N : ℕ) (J : Ideal (MvPolynomial (Fin (N + 1)) K))
    (hprime : J.IsPrime) (hirr : projectiveIrrelevantIdeal K N ≤ J) :
    ringKrullDim (MvPolynomial (Fin (N + 1)) K ⧸ J) = 0 := by
  have hmax : (projectiveIrrelevantIdeal K N).IsMaximal := by
    rw [projectiveIrrelevantIdeal_eq_ker_constantCoeff_over_field]
    apply RingHom.ker_isMaximal_of_surjective
    intro a
    exact ⟨MvPolynomial.C a, by simp⟩
  have hJ : projectiveIrrelevantIdeal K N = J :=
    hmax.eq_of_le hprime.ne_top hirr
  letI : J.IsMaximal := hJ ▸ hmax
  letI := Ideal.Quotient.field J
  exact ringKrullDim_eq_zero_of_field _

end
end TranslatedDepthSeven
