import TranslatedDepthSeven.ProjectiveHilbertDegreeCertificationInternal
import TranslatedDepthSeven.HomogeneousIrrelevantDimensionFieldInternal

/-! A homogeneous prime of specified positive affine dimension has a
positive projective degree certified by its actual Hilbert polynomial.
The Hilbert-polynomial certification is the existing internal theorem,
not a literature premise or an assumed degree label. -/

set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.HomogeneousPrimeDegree
open MvPolynomial TranslatedDepthSeven
attribute [local instance] MvPolynomial.gradedAlgebra

/-- Positive affine dimension excludes the irrelevant prime, and the
internally constructed Hilbert polynomial has the specified dimension. -/
theorem exists_degree {K : Type*} [Field K] [CharZero K] {N r : ℕ}
    (I : Ideal (MvPolynomial (Fin (N+1)) K)) (hprime : I.IsPrime)
    (hhom : I.IsHomogeneous (homogeneousSubmodule (Fin (N+1)) K))
    (hdim : ringKrullDim (MvPolynomial (Fin (N+1)) K ⧸ I) =
      ((r+1 : ℕ) : WithBot ℕ∞)) :
    ∃ d : ℕ, 1 ≤ d ∧ Published.HasProjectiveDimensionDegree I r d := by
  have hirr : ¬ Published.projectiveIrrelevantIdeal K N ≤ I := by
    intro hle
    have hzero := ringKrullDim_quotient_eq_zero_of_irrelevant_le_over_field N I hprime hle
    rw [hdim] at hzero
    have hz : r+1 = 0 := by exact_mod_cast hzero
    omega
  obtain ⟨s,d,P,hP⟩ := projectiveHilbertDegreeCertification_internal K N I hprime hhom hirr
  have hs : s = r := by
    have he := hP.1.symm.trans hdim
    have he' : s+1 = r+1 := by exact_mod_cast he
    omega
  subst s
  exact ⟨d,hP.2.1,hP.toPublished⟩

end CubicTenVariables.HomogeneousPrimeDegree
