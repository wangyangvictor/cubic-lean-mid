import TranslatedDepthSeven.FiniteFamilyHomogenization
import TranslatedDepthSeven.FiniteNormalizationPointCount
import TranslatedDepthSeven.RationalPointResidueField

/-!
# Affine zeroes as rational points of a quotient

For an ideal `I ⊆ k[X₁,…,Xₙ]`, evaluation at a common zero of `I`
factors uniquely through `k[X₁,…,Xₙ] / I`.  Conversely, a `k`-algebra
homomorphism from the quotient to `k` is evaluation at the images of the
coordinate variables.  This file records that correspondence as a literal
equivalence and transports the finite-normalization point bound to the
existing affine-zero-locus definition.
-/

namespace TranslatedDepthSeven

noncomputable section

open MvPolynomial

universe u v

/-- Membership in the literal affine zero locus is exactly the kernel
condition which permits evaluation to descend through the quotient. -/
theorem mem_affineIdealZeroLocus_iff_le_ker_aeval
    {k : Type u} {σ : Type v} [Field k]
    (I : Ideal (MvPolynomial σ k)) (z : σ → k) :
    z ∈ affineIdealZeroLocus I ↔
      I ≤ RingHom.ker (MvPolynomial.aeval z).toRingHom := by
  constructor
  · intro hz f hf
    rw [RingHom.mem_ker]
    exact hz f hf
  · intro hI f hf
    exact RingHom.mem_ker.mp (hI hf)

/-- A common zero of `I` gives the evaluation homomorphism on the quotient
by `I`. -/
noncomputable def affineIdealPointToQuotientAlgHom
    {k : Type u} {σ : Type v} [Field k]
    (I : Ideal (MvPolynomial σ k))
    (z : {z : σ → k // z ∈ affineIdealZeroLocus I}) :
    (MvPolynomial σ k ⧸ I) →ₐ[k] k :=
  affineQuotientRationalPoint I z.1
    ((mem_affineIdealZeroLocus_iff_le_ker_aeval I z.1).mp z.2)

/-- A rational point of the quotient gives its coordinate tuple. -/
noncomputable def quotientAlgHomToAffineIdealPoint
    {k : Type u} {σ : Type v} [Field k]
    (I : Ideal (MvPolynomial σ k))
    (φ : (MvPolynomial σ k ⧸ I) →ₐ[k] k) :
    {z : σ → k // z ∈ affineIdealZeroLocus I} := by
  let z : σ → k := fun i ↦ φ (Ideal.Quotient.mk I (X i))
  refine ⟨z, (mem_affineIdealZeroLocus_iff_le_ker_aeval I z).mpr ?_⟩
  intro f hf
  rw [RingHom.mem_ker]
  have hcomp :
      φ.comp (Ideal.Quotient.mkₐ k I) = MvPolynomial.aeval z := by
    apply MvPolynomial.algHom_ext
    intro i
    simp [z]
  rw [← hcomp]
  change φ (Ideal.Quotient.mk I f) = 0
  rw [Ideal.Quotient.eq_zero_iff_mem.mpr hf]
  exact map_zero φ

@[simp]
theorem affineIdealPointToQuotientAlgHom_apply_mk
    {k : Type u} {σ : Type v} [Field k]
    (I : Ideal (MvPolynomial σ k))
    (z : {z : σ → k // z ∈ affineIdealZeroLocus I})
    (f : MvPolynomial σ k) :
    affineIdealPointToQuotientAlgHom I z (Ideal.Quotient.mk I f) =
      MvPolynomial.aeval z.1 f := by
  rfl

@[simp]
theorem quotientAlgHomToAffineIdealPoint_apply
    {k : Type u} {σ : Type v} [Field k]
    (I : Ideal (MvPolynomial σ k))
    (φ : (MvPolynomial σ k ⧸ I) →ₐ[k] k) (i : σ) :
    (quotientAlgHomToAffineIdealPoint I φ).1 i =
      φ (Ideal.Quotient.mk I (X i)) := by
  simp [quotientAlgHomToAffineIdealPoint]

/-- Common zeroes of an ideal in affine space are canonically equivalent to
`k`-algebra homomorphisms from its coordinate ring to `k`. -/
noncomputable def affineIdealZeroLocusEquivQuotientAlgHom
    {k : Type u} {σ : Type v} [Field k]
    (I : Ideal (MvPolynomial σ k)) :
    {z : σ → k // z ∈ affineIdealZeroLocus I} ≃
      ((MvPolynomial σ k ⧸ I) →ₐ[k] k) where
  toFun := affineIdealPointToQuotientAlgHom I
  invFun := quotientAlgHomToAffineIdealPoint I
  left_inv z := by
    apply Subtype.ext
    funext i
    simp
  right_inv φ := by
    apply Ideal.Quotient.algHom_ext
    apply MvPolynomial.algHom_ext
    intro i
    simp

/-- Cardinal form of the point-coordinate-ring correspondence. -/
theorem natCard_affineIdealZeroLocus_eq_quotientAlgHom
    {k : Type u} {σ : Type v} [Field k]
    (I : Ideal (MvPolynomial σ k)) :
    Nat.card {z : σ → k // z ∈ affineIdealZeroLocus I} =
      Nat.card ((MvPolynomial σ k ⧸ I) →ₐ[k] k) :=
  Nat.card_congr (affineIdealZeroLocusEquivQuotientAlgHom I)

/-- A prime affine ideal of displayed transcendence degree `d` has at most
`D (#k)^d` literal common zeroes over the finite field `k`. -/
theorem exists_natCard_affineIdealZeroLocus_le_mul_pow_of_trdeg_eq
    (k : Type u) [Field k] [Finite k] {n d : ℕ}
    (P : Ideal (MvPolynomial (Fin n) k)) [P.IsPrime]
    (htrdeg : Algebra.trdeg k (MvPolynomial (Fin n) k ⧸ P) =
      (d : Cardinal)) :
    ∃ D : ℕ,
      Nat.card {z : Fin n → k // z ∈ affineIdealZeroLocus P} ≤
        D * Nat.card k ^ d := by
  obtain ⟨D, hD⟩ :=
    exists_natCard_primeAffine_algHom_le_mul_pow_of_trdeg_eq k P htrdeg
  refine ⟨D, ?_⟩
  rw [natCard_affineIdealZeroLocus_eq_quotientAlgHom]
  exact hD

/-- The same point bound for the literal common zero set of a finite family
whose generated ideal is prime. -/
theorem exists_natCard_finiteAffineCommonZeroLocus_le_mul_pow_of_trdeg_eq
    (k : Type u) [Field k] [Finite k] {n d : ℕ}
    (equations : Finset (MvPolynomial (Fin n) k))
    [(finiteEquationIdeal equations).IsPrime]
    (htrdeg :
      Algebra.trdeg k
          (MvPolynomial (Fin n) k ⧸ finiteEquationIdeal equations) =
        (d : Cardinal)) :
    ∃ D : ℕ,
      Nat.card
          {z : Fin n → k // z ∈ finiteAffineCommonZeroLocus equations} ≤
        D * Nat.card k ^ d := by
  simpa only [affineIdealZeroLocus_finiteEquationIdeal] using
    exists_natCard_affineIdealZeroLocus_le_mul_pow_of_trdeg_eq
      k (finiteEquationIdeal equations) htrdeg

end

end TranslatedDepthSeven
