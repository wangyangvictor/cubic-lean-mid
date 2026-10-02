import TranslatedDepthSeven.ProjectiveDegreeSpanSectionAlgebra

/-!
# Projective dimension and degree over an arbitrary coefficient extension

The extension may be transcendental. Degree-by-degree Hilbert ranks are
preserved by scalar extension. For a homogeneous prime after extension in
characteristic zero, the internally proved Hilbert certification therefore
recovers the same actual Krull dimension and projective degree.

Primality of the extended ideal is an explicit hypothesis: this file does
not prove geometric integrality or a generic hyperplane-section theorem.
-/

namespace TranslatedDepthSeven

noncomputable section

open MvPolynomial Published
attribute [local instance] MvPolynomial.gradedAlgebra

/-- Positive projective Hilbert data pass to any coefficient field, without
primality, homogeneity, algebraicity, or a characteristic restriction. -/
theorem hasProjectiveHilbertDimensionDegree_coefficientExtension
    {K L : Type*} [Field K] [Field L] [Algebra K L] {N r d : ℕ}
    (I : Ideal (MvPolynomial (Fin (N + 1)) K))
    (hdegree : HasProjectiveHilbertDimensionDegree I r d) :
    HasProjectiveHilbertDimensionDegree
      (I.map (MvPolynomial.map (algebraMap K L))) r d := by
  obtain ⟨hd, P, hPdeg, hPlc, n₀, hP⟩ := hdegree
  refine ⟨hd, P, hPdeg, hPlc, n₀, ?_⟩
  intro n hn
  rw [projectiveHilbertPiece_finrank_map_eq (K := K) (L := L) N n I]
  exact hP n hn

/-- Full projective dimension and degree pass to an arbitrary, possibly
transcendental, field extension when the homogeneous extended ideal is
prime. The source ideal need not separately be assumed prime. -/
theorem hasProjectiveDimensionDegree_coefficientExtension
    {K L : Type*} [Field K] [CharZero K] [Field L] [Algebra K L] {N r d : ℕ}
    (I : Ideal (MvPolynomial (Fin (N + 1)) K))
    (hhom : I.IsHomogeneous (homogeneousSubmodule (Fin (N + 1)) K))
    (hdegree : HasProjectiveDimensionDegree I r d)
    (hprime : (I.map (MvPolynomial.map (algebraMap K L))).IsPrime) :
    HasProjectiveDimensionDegree
      (I.map (MvPolynomial.map (algebraMap K L))) r d := by
  letI : CharZero L := charZero_of_injective_algebraMap (algebraMap K L).injective
  exact projectiveSection_fullDegree_of_hilbertDegree _ hprime
    (isHomogeneous_map_mvPolynomialMap (algebraMap K L) I hhom)
    (hasProjectiveHilbertDimensionDegree_coefficientExtension I hdegree.toHilbert)

/-- The corresponding equality of actual affine-cone Krull dimensions;
no integral-extension argument is used. -/
theorem projectiveQuotient_ringKrullDim_coefficientExtension_eq
    {K L : Type*} [Field K] [CharZero K] [Field L] [Algebra K L] {N r d : ℕ}
    (I : Ideal (MvPolynomial (Fin (N + 1)) K))
    (hhom : I.IsHomogeneous (homogeneousSubmodule (Fin (N + 1)) K))
    (hdegree : HasProjectiveDimensionDegree I r d)
    (hprime : (I.map (MvPolynomial.map (algebraMap K L))).IsPrime) :
    ringKrullDim (MvPolynomial (Fin (N + 1)) L ⧸
      I.map (MvPolynomial.map (algebraMap K L))) =
      ringKrullDim (MvPolynomial (Fin (N + 1)) K ⧸ I) :=
  (hasProjectiveDimensionDegree_coefficientExtension I hhom hdegree hprime).1.trans
    hdegree.1.symm

end

end TranslatedDepthSeven
