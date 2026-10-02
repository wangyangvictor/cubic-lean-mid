import TranslatedDepthSeven.RealCoefficientExtension
import TranslatedDepthSeven.PublishedCountingTheorems
import Mathlib.RingTheory.TensorProduct.Quotient
import Mathlib.RingTheory.IsTensorProduct

/-!
# Homogeneous Hilbert pieces under extension from `ℚ` to `ℝ`

This file identifies, degree by degree, the homogeneous quotient pieces of
an ideal over `ℚ` with those of its coefficient extension to `ℝ`.
-/

namespace TranslatedDepthSeven

noncomputable section

open scoped TensorProduct
open MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra

set_option synthInstance.maxHeartbeats 500000
set_option maxHeartbeats 1000000

noncomputable local instance realMvPolynomialCoefficientAlgebra'
    {σ : Type*} :
    Algebra (MvPolynomial σ ℚ) (MvPolynomial σ ℝ) :=
  MvPolynomial.algebraMvPolynomial

/-- Coefficient extension commutes with passage to the quotient. -/
noncomputable def realProjectiveQuotientTensorLinearEquiv
    {σ : Type*} (I : Ideal (MvPolynomial σ ℚ)) :
    (MvPolynomial σ ℝ ⧸ I.map (MvPolynomial.map (algebraMap ℚ ℝ))) ≃ₗ[ℝ]
      ℝ ⊗[ℚ] (MvPolynomial σ ℚ ⧸ I) := by
  let e₁ :=
    (Algebra.TensorProduct.quotIdealMapEquivTensorQuot
      (MvPolynomial σ ℝ) I).toLinearEquiv.restrictScalars ℝ
  let e₂ := Algebra.IsPushout.cancelBaseChange ℚ ℝ
    (MvPolynomial σ ℚ) (MvPolynomial σ ℝ)
      (MvPolynomial σ ℚ ⧸ I)
  simpa only [MvPolynomial.algebraMap_apply] using e₁.trans e₂

@[simp]
theorem realProjectiveQuotientTensorLinearEquiv_mk_map
    {σ : Type*} (I : Ideal (MvPolynomial σ ℚ))
    (p : MvPolynomial σ ℚ) :
    realProjectiveQuotientTensorLinearEquiv I
        (Ideal.Quotient.mk _ (MvPolynomial.map (algebraMap ℚ ℝ) p)) =
      (1 : ℝ) ⊗ₜ[ℚ] Ideal.Quotient.mk I p := by
  change (Algebra.IsPushout.cancelBaseChange ℚ ℝ
      (MvPolynomial σ ℚ) (MvPolynomial σ ℝ)
        (MvPolynomial σ ℚ ⧸ I))
      ((Algebra.TensorProduct.quotIdealMapEquivTensorQuot
        (MvPolynomial σ ℝ) I)
        (Ideal.Quotient.mk _ (MvPolynomial.map (algebraMap ℚ ℝ) p))) = _
  rw [Algebra.TensorProduct.quotIdealMapEquivTensorQuot_mk]
  have hmap : MvPolynomial.map (algebraMap ℚ ℝ) p =
      algebraMap (MvPolynomial σ ℚ) (MvPolynomial σ ℝ) p := rfl
  rw [hmap]
  rw [show algebraMap (MvPolynomial σ ℚ) (MvPolynomial σ ℝ) p =
      p • (1 : MvPolynomial σ ℝ) by simp [Algebra.smul_def]]
  rw [TensorProduct.smul_tmul,
    Algebra.IsPushout.cancelBaseChange_tmul]
  simp [Algebra.smul_def]

/-- A homogeneous quotient piece is spanned by the images of the monomials
of the indicated degree. -/
theorem projectiveHilbertPiece_eq_span_monomials
    (K : Type*) [Field K] (N : ℕ)
    (I : Ideal (MvPolynomial (Fin (N + 1)) K)) (k : ℕ) :
    Published.projectiveHilbertPiece K N I k =
      Submodule.span K
        ((fun d : Fin (N + 1) →₀ ℕ ↦
            Ideal.Quotient.mk I (MvPolynomial.monomial d 1)) ''
          {d | d.degree = k}) := by
  rw [Published.projectiveHilbertPiece,
    MvPolynomial.homogeneousSubmodule_eq_finsupp_supported,
    Finsupp.supported_eq_span_single, Submodule.map_span]
  congr 1
  ext x
  constructor
  · rintro ⟨p, ⟨d, hd, rfl⟩, rfl⟩
    refine ⟨d, hd, ?_⟩
    simp only [MvPolynomial.single_eq_monomial]
    change Ideal.Quotient.mk I _ = Ideal.Quotient.mkₐ K I _
    rw [Ideal.Quotient.mkₐ_eq_mk]
  · rintro ⟨d, hd, rfl⟩
    refine ⟨MvPolynomial.monomial d 1, ?_, rfl⟩
    exact ⟨d, hd, by simp only [MvPolynomial.single_eq_monomial]⟩

/-- Under the quotient base-change equivalence, the real homogeneous piece
is exactly the scalar extension of the rational homogeneous piece. -/
theorem map_real_projectiveHilbertPiece_eq_baseChange
    (N k : ℕ)
    (I : Ideal (MvPolynomial (Fin (N + 1)) ℚ)) :
    (Published.projectiveHilbertPiece ℝ N
        (I.map (MvPolynomial.map (algebraMap ℚ ℝ))) k).map
        (realProjectiveQuotientTensorLinearEquiv I).toLinearMap =
      (Published.projectiveHilbertPiece ℚ N I k).baseChange ℝ := by
  rw [projectiveHilbertPiece_eq_span_monomials,
    projectiveHilbertPiece_eq_span_monomials,
    Submodule.map_span, Submodule.baseChange_span]
  congr 1
  ext x
  simp only [Set.mem_image, Set.mem_setOf_eq]
  constructor
  · rintro ⟨q, ⟨d, hd, rfl⟩, rfl⟩
    refine ⟨Ideal.Quotient.mk I (MvPolynomial.monomial d 1), ?_, ?_⟩
    · exact ⟨d, hd, rfl⟩
    · simpa using
        (realProjectiveQuotientTensorLinearEquiv_mk_map I
          (MvPolynomial.monomial d (1 : ℚ))).symm
  · rintro ⟨q, ⟨d, hd, rfl⟩, rfl⟩
    refine ⟨Ideal.Quotient.mk _ (MvPolynomial.monomial d 1), ⟨d, hd, rfl⟩, ?_⟩
    simpa using
      (realProjectiveQuotientTensorLinearEquiv_mk_map I
        (MvPolynomial.monomial d (1 : ℚ)))

/-- Scalar extension of a finite-dimensional rational subspace has the
same dimension over `ℝ` as the original subspace has over `ℚ`. -/
theorem finrank_real_baseChange_submodule
    {M : Type*} [AddCommGroup M] [Module ℚ M]
    (p : Submodule ℚ M) :
    Module.finrank ℝ (p.baseChange ℝ) = Module.finrank ℚ p := by
  rw [Submodule.baseChange,
    LinearMap.finrank_range_of_inj, Module.finrank_baseChange]
  rw [LinearMap.baseChange_eq_ltensor]
  exact (Module.FaithfullyFlat.lTensor_injective_iff_injective
    ℚ ℝ p.subtype).2 (Submodule.subtype_injective p)

/-- Every projective Hilbert function value is unchanged by extending the
coefficient field from `ℚ` to `ℝ`. -/
theorem real_projectiveHilbertPiece_finrank_eq
    (N k : ℕ)
    (I : Ideal (MvPolynomial (Fin (N + 1)) ℚ)) :
    Module.finrank ℝ
        (Published.projectiveHilbertPiece ℝ N
          (I.map (MvPolynomial.map (algebraMap ℚ ℝ))) k) =
      Module.finrank ℚ (Published.projectiveHilbertPiece ℚ N I k) := by
  calc
    Module.finrank ℝ
        (Published.projectiveHilbertPiece ℝ N
          (I.map (MvPolynomial.map (algebraMap ℚ ℝ))) k) =
        Module.finrank ℝ
          ((Published.projectiveHilbertPiece ℝ N
            (I.map (MvPolynomial.map (algebraMap ℚ ℝ))) k).map
              (realProjectiveQuotientTensorLinearEquiv I).toLinearMap) :=
      (LinearEquiv.finrank_map_eq
        (realProjectiveQuotientTensorLinearEquiv I)
        (Published.projectiveHilbertPiece ℝ N
          (I.map (MvPolynomial.map (algebraMap ℚ ℝ))) k)).symm
    _ = Module.finrank ℝ
        ((Published.projectiveHilbertPiece ℚ N I k).baseChange ℝ) := by
      rw [map_real_projectiveHilbertPiece_eq_baseChange]
    _ = Module.finrank ℚ
        (Published.projectiveHilbertPiece ℚ N I k) :=
      finrank_real_baseChange_submodule _

/-- The positive degree and exact eventual projective Hilbert polynomial are
preserved by extending coefficients from `ℚ` to `ℝ`.  The independent Krull-
dimension conjunct of `HasProjectiveDimensionDegree` is intentionally not
asserted here. -/
theorem real_projectiveHilbertPolynomial_of_rational
    {N r d : ℕ}
    (I : Ideal (MvPolynomial (Fin (N + 1)) ℚ))
    (hI : Published.HasProjectiveDimensionDegree I r d) :
    0 < d ∧ ∃ P : Polynomial ℚ,
      P.natDegree = r ∧
      P.leadingCoeff = (d : ℚ) / r.factorial ∧
      ∃ k₀ : ℕ, ∀ k ≥ k₀,
        (Module.finrank ℝ
          (Published.projectiveHilbertPiece ℝ N
            (I.map (MvPolynomial.map (algebraMap ℚ ℝ))) k) : ℚ) =
          P.eval (k : ℚ) := by
  rcases hI with ⟨_hdim, hd, P, hdegree, hleading, k₀, heventual⟩
  refine ⟨hd, P, hdegree, hleading, k₀, ?_⟩
  intro k hk
  rw [real_projectiveHilbertPiece_finrank_eq N k I]
  exact heventual k hk

/-- Projective Hilbert dimension and degree are unchanged by extending
coefficients from `ℚ` to `ℝ`.  This formulation deliberately records only
the Hilbert-polynomial datum: it is precisely what is needed to pass from a
homogeneous projective ideal to its affine cone before applying Pila's
theorem. -/
theorem real_hasProjectiveHilbertDimensionDegree_of_rational
    {N r d : ℕ}
    (I : Ideal (MvPolynomial (Fin (N + 1)) ℚ))
    (hI : Published.HasProjectiveDimensionDegree I r d) :
    Published.HasProjectiveHilbertDimensionDegree
      (I.map (MvPolynomial.map (algebraMap ℚ ℝ))) r d := by
  exact real_projectiveHilbertPolynomial_of_rational I hI

end

end TranslatedDepthSeven
