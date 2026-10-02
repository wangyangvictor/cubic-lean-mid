import TranslatedDepthSeven.ParameterCountSurface
import TranslatedDepthSeven.PublishedCountingTheorems
import TranslatedDepthSeven.QbarCoefficientExtension
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Mathlib.RingTheory.IsTensorProduct
import Mathlib.RingTheory.TensorProduct.Quotient

/-!
# Projective Hilbert data under coefficient extension

The degree-by-degree Hilbert function of a homogeneous polynomial quotient
is unchanged by extending its coefficient field.  If the field extension is
algebraic and the extended ideal is prime, the quotient rings also have the
same Krull dimension.  Thus the complete literal predicate
`Published.HasProjectiveDimensionDegree` passes to the extended ideal.

This is a base-change theorem, not Hilbert--Serre existence: it transports an
eventual Hilbert polynomial which has already been constructed over the
smaller field.
-/

namespace TranslatedDepthSeven

noncomputable section

open scoped TensorProduct
open MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra

set_option synthInstance.maxHeartbeats 500000
set_option maxHeartbeats 1000000

universe u v w

variable {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]

noncomputable local instance projectiveHilbertCoefficientAlgebra
    {sigma : Type w} :
    Algebra (MvPolynomial sigma K) (MvPolynomial sigma L) :=
  MvPolynomial.algebraMvPolynomial

/-- Coefficient extension commutes with passage to a polynomial quotient. -/
noncomputable def projectiveQuotientTensorLinearEquiv
    {sigma : Type w} (I : Ideal (MvPolynomial sigma K)) :
    (MvPolynomial sigma L ⧸
        I.map (MvPolynomial.map (algebraMap K L))) ≃ₗ[L]
      L ⊗[K] (MvPolynomial sigma K ⧸ I) := by
  let e₁ :=
    (Algebra.TensorProduct.quotIdealMapEquivTensorQuot
      (MvPolynomial sigma L) I).toLinearEquiv.restrictScalars L
  let e₂ := Algebra.IsPushout.cancelBaseChange K L
    (MvPolynomial sigma K) (MvPolynomial sigma L)
      (MvPolynomial sigma K ⧸ I)
  simpa only [MvPolynomial.algebraMap_apply] using e₁.trans e₂

@[simp]
theorem projectiveQuotientTensorLinearEquiv_mk_map
    {sigma : Type w} (I : Ideal (MvPolynomial sigma K))
    (p : MvPolynomial sigma K) :
    projectiveQuotientTensorLinearEquiv (K := K) (L := L) I
        (Ideal.Quotient.mk _ (MvPolynomial.map (algebraMap K L) p)) =
      (1 : L) ⊗ₜ[K] Ideal.Quotient.mk I p := by
  change (Algebra.IsPushout.cancelBaseChange K L
      (MvPolynomial sigma K) (MvPolynomial sigma L)
        (MvPolynomial sigma K ⧸ I))
      ((Algebra.TensorProduct.quotIdealMapEquivTensorQuot
        (MvPolynomial sigma L) I)
        (Ideal.Quotient.mk _ (MvPolynomial.map (algebraMap K L) p))) = _
  rw [Algebra.TensorProduct.quotIdealMapEquivTensorQuot_mk]
  have hmap : MvPolynomial.map (algebraMap K L) p =
      algebraMap (MvPolynomial sigma K) (MvPolynomial sigma L) p := rfl
  rw [hmap]
  rw [show algebraMap (MvPolynomial sigma K) (MvPolynomial sigma L) p =
      p • (1 : MvPolynomial sigma L) by simp [Algebra.smul_def]]
  rw [TensorProduct.smul_tmul,
    Algebra.IsPushout.cancelBaseChange_tmul]
  simp [Algebra.smul_def]

/-- A homogeneous quotient piece is spanned by the images of the monomials
of its degree. -/
theorem projectiveHilbertPiece_eq_span_monomials_general
    (F : Type*) [Field F] (N : ℕ)
    (I : Ideal (MvPolynomial (Fin (N + 1)) F)) (k : ℕ) :
    Published.projectiveHilbertPiece F N I k =
      Submodule.span F
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
    change Ideal.Quotient.mk I _ = Ideal.Quotient.mkₐ F I _
    rw [Ideal.Quotient.mkₐ_eq_mk]
  · rintro ⟨d, hd, rfl⟩
    refine ⟨MvPolynomial.monomial d 1, ?_, rfl⟩
    exact ⟨d, hd, by simp only [MvPolynomial.single_eq_monomial]⟩

/-- The quotient base-change equivalence carries an extended homogeneous
piece onto the scalar extension of the original piece. -/
theorem map_projectiveHilbertPiece_eq_baseChange
    (N k : ℕ)
    (I : Ideal (MvPolynomial (Fin (N + 1)) K)) :
    (Published.projectiveHilbertPiece L N
        (I.map (MvPolynomial.map (algebraMap K L))) k).map
        (projectiveQuotientTensorLinearEquiv
          (K := K) (L := L) I).toLinearMap =
      (Published.projectiveHilbertPiece K N I k).baseChange L := by
  rw [projectiveHilbertPiece_eq_span_monomials_general,
    projectiveHilbertPiece_eq_span_monomials_general,
    Submodule.map_span, Submodule.baseChange_span]
  congr 1
  ext x
  simp only [Set.mem_image, Set.mem_setOf_eq]
  constructor
  · rintro ⟨q, ⟨d, hd, rfl⟩, rfl⟩
    refine ⟨Ideal.Quotient.mk I (MvPolynomial.monomial d 1), ?_, ?_⟩
    · exact ⟨d, hd, rfl⟩
    · simpa using
        (projectiveQuotientTensorLinearEquiv_mk_map
          (K := K) (L := L) I
          (MvPolynomial.monomial d (1 : K))).symm
  · rintro ⟨q, ⟨d, hd, rfl⟩, rfl⟩
    refine ⟨Ideal.Quotient.mk _ (MvPolynomial.monomial d 1),
      ⟨d, hd, rfl⟩, ?_⟩
    simpa using
      (projectiveQuotientTensorLinearEquiv_mk_map
        (K := K) (L := L) I
        (MvPolynomial.monomial d (1 : K)))

/-- Scalar extension of a finite-dimensional subspace preserves its
dimension over the corresponding field. -/
theorem finrank_baseChange_submodule_field
    {M : Type*} [AddCommGroup M] [Module K M]
    (p : Submodule K M) :
    Module.finrank L (p.baseChange L) = Module.finrank K p := by
  rw [Submodule.baseChange,
    LinearMap.finrank_range_of_inj, Module.finrank_baseChange]
  rw [LinearMap.baseChange_eq_ltensor]
  exact (Module.FaithfullyFlat.lTensor_injective_iff_injective
    K L p.subtype).2 (Submodule.subtype_injective p)

/-- Every homogeneous Hilbert-function value is invariant under coefficient
field extension. -/
theorem projectiveHilbertPiece_finrank_map_eq
    (N k : ℕ)
    (I : Ideal (MvPolynomial (Fin (N + 1)) K)) :
    Module.finrank L
        (Published.projectiveHilbertPiece L N
          (I.map (MvPolynomial.map (algebraMap K L))) k) =
      Module.finrank K (Published.projectiveHilbertPiece K N I k) := by
  calc
    Module.finrank L
        (Published.projectiveHilbertPiece L N
          (I.map (MvPolynomial.map (algebraMap K L))) k) =
        Module.finrank L
          ((Published.projectiveHilbertPiece L N
            (I.map (MvPolynomial.map (algebraMap K L))) k).map
              (projectiveQuotientTensorLinearEquiv
                (K := K) (L := L) I).toLinearMap) :=
      (LinearEquiv.finrank_map_eq
        (projectiveQuotientTensorLinearEquiv
          (K := K) (L := L) I)
        (Published.projectiveHilbertPiece L N
          (I.map (MvPolynomial.map (algebraMap K L))) k)).symm
    _ = Module.finrank L
        ((Published.projectiveHilbertPiece K N I k).baseChange L) := by
      rw [map_projectiveHilbertPiece_eq_baseChange]
    _ = Module.finrank K
        (Published.projectiveHilbertPiece K N I k) :=
      finrank_baseChange_submodule_field _

/-- A prime quotient after extension from `ℚ` to `Qbar` has the same Krull
dimension as the original quotient.  Integrality comes from algebraicity of
`Qbar/ℚ`, while injectivity is faithful-flat contraction. -/
theorem qbarProjectiveQuotient_ringKrullDim_map_eq
    {N : ℕ} (I : Ideal (MvPolynomial (Fin (N + 1)) ℚ))
    (hmapPrime :
      (I.map (MvPolynomial.map (algebraMap ℚ Qbar))).IsPrime) :
    ringKrullDim
        (MvPolynomial (Fin (N + 1)) Qbar ⧸
          I.map (MvPolynomial.map (algebraMap ℚ Qbar))) =
      ringKrullDim (MvPolynomial (Fin (N + 1)) ℚ ⧸ I) := by
  let R := MvPolynomial (Fin (N + 1)) ℚ
  let S := MvPolynomial (Fin (N + 1)) Qbar
  let f : R →+* S := MvPolynomial.map (algebraMap ℚ Qbar)
  let J : Ideal S := I.map f
  have hcomap : J.comap f = I := by
    simpa only [MvPolynomial.algebraMap_apply] using
      (Ideal.comap_map_eq_self_of_faithfullyFlat I)
  letI : Algebra.IsIntegral ℚ Qbar :=
    Algebra.isAlgebraic_iff_isIntegral.mp inferInstance
  letI : Algebra R S := MvPolynomial.algebraMvPolynomial
  letI : Algebra.IsIntegral R S := inferInstance
  let g : (R ⧸ J.comap f) →+* (S ⧸ J) :=
    Ideal.quotientMap J f le_rfl
  letI : Algebra (R ⧸ J.comap f) (S ⧸ J) := g.toAlgebra
  letI : IsDomain (S ⧸ J) :=
    (Ideal.Quotient.isDomain_iff_prime (I := J)).mpr hmapPrime
  have hfIntegral : f.IsIntegral := by
    change (algebraMap R S).IsIntegral
    exact Algebra.IsIntegral.isIntegral
  letI : Algebra.IsIntegral (R ⧸ J.comap f) (S ⧸ J) :=
    ⟨hfIntegral.quotient⟩
  letI : FaithfulSMul (R ⧸ J.comap f) (S ⧸ J) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr
      (by
        change Function.Injective g
        exact Ideal.quotientMap_injective)
  have hdim := ringKrullDim_eq_of_isIntegral_injective_parameterCount
    (R := R ⧸ J.comap f) (S := S ⧸ J)
  rw [hcomap] at hdim
  exact hdim.symm

/-- The complete projective dimension--degree certificate passes from `ℚ`
to `Qbar` whenever geometric primeness makes the extended ideal prime. -/
theorem qbarHasProjectiveDimensionDegree_of_rational
    {N r d : ℕ}
    (I : Ideal (MvPolynomial (Fin (N + 1)) ℚ))
    (hI : Published.HasProjectiveDimensionDegree I r d)
    (hmapPrime :
      (I.map (MvPolynomial.map (algebraMap ℚ Qbar))).IsPrime) :
    Published.HasProjectiveDimensionDegree
      (I.map (MvPolynomial.map (algebraMap ℚ Qbar))) r d := by
  rcases hI with ⟨hdim, hd, P, hdegree, hleading, k₀, heventual⟩
  refine ⟨?_, hd, P, hdegree, hleading, k₀, ?_⟩
  · rw [qbarProjectiveQuotient_ringKrullDim_map_eq I hmapPrime]
    exact hdim
  · intro k hk
    rw [projectiveHilbertPiece_finrank_map_eq
      (K := ℚ) (L := Qbar) N k I]
    exact heventual k hk

end

end TranslatedDepthSeven
