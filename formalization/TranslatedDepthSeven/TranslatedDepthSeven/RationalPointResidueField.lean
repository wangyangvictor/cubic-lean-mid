import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Eval

/-!
# Residue fields at rational affine points

A `k`-rational point of an affine `k`-algebra `A` is represented by a
`k`-algebra homomorphism `A →ₐ[k] k`.  Its kernel is maximal, and the
residue field of the local ring of `A` at that kernel is canonically `k`.

The final declarations specialize this observation to a quotient of a
multivariate polynomial ring by equations vanishing at a specified point.
-/

namespace TranslatedDepthSeven

noncomputable section

universe u v w

open MvPolynomial

/-- Every algebra map from a `k`-algebra to `k` is surjective: constants
give a section. -/
theorem rationalPoint_surjective
    {k : Type u} {A : Type v} [Field k] [CommRing A] [Algebra k A]
    (x : A →ₐ[k] k) : Function.Surjective x := by
  intro a
  exact ⟨algebraMap k A a, x.commutes a⟩

/-- The kernel of a rational point is a maximal ideal. -/
theorem rationalPoint_ker_isMaximal
    {k : Type u} {A : Type v} [Field k] [CommRing A] [Algebra k A]
    (x : A →ₐ[k] k) : (RingHom.ker x.toRingHom).IsMaximal :=
  RingHom.ker_isMaximal_of_surjective x.toRingHom (rationalPoint_surjective x)

/-- The prime-ideal instance attached to a rational point. -/
instance rationalPoint_ker_isPrime
    {k : Type u} {A : Type v} [Field k] [CommRing A] [Algebra k A]
    (x : A →ₐ[k] k) : (RingHom.ker x.toRingHom).IsPrime :=
  (rationalPoint_ker_isMaximal x).isPrime

/-- The residue field at a `k`-rational point of an affine `k`-algebra is
canonically `k`.  Here `p.ResidueField` is definitionally the residue field
of the local ring `Localization.AtPrime p`. -/
noncomputable def rationalPointResidueFieldAlgEquiv
    {k : Type u} {A : Type v} [Field k] [CommRing A] [Algebra k A]
    (x : A →ₐ[k] k) :
    (RingHom.ker x.toRingHom).ResidueField ≃ₐ[k] k := by
  let p : Ideal A := RingHom.ker x.toRingHom
  letI : p.IsMaximal := rationalPoint_ker_isMaximal x
  let hp0 : p ≤ RingHom.ker x.toRingHom := by rfl
  let hunit : p.primeCompl ≤ (IsUnit.submonoid k).comap x := by
    intro a ha
    change IsUnit (x a)
    rw [isUnit_iff_ne_zero]
    intro hzero
    exact ha hzero
  let φ : p.ResidueField →ₐ[k] k :=
    Ideal.ResidueField.liftₐ p x hp0 hunit
  refine AlgEquiv.ofBijective φ ⟨φ.injective, ?_⟩
  intro a
  obtain ⟨b, rfl⟩ := rationalPoint_surjective x a
  exact ⟨algebraMap A p.ResidueField b, by
    exact Ideal.ResidueField.liftₐ_algebraMap p x hp0 hunit b⟩

@[simp]
theorem rationalPointResidueFieldAlgEquiv_algebraMap
    {k : Type u} {A : Type v} [Field k] [CommRing A] [Algebra k A]
    (x : A →ₐ[k] k) (a : A) :
    rationalPointResidueFieldAlgEquiv x
        (algebraMap A (RingHom.ker x.toRingHom).ResidueField a) = x a := by
  let p : Ideal A := RingHom.ker x.toRingHom
  letI : p.IsMaximal := rationalPoint_ker_isMaximal x
  simp [rationalPointResidueFieldAlgEquiv]

/-- Evaluation at an affine point, descended to a quotient by equations
which vanish there. -/
noncomputable def affineQuotientRationalPoint
    {k : Type u} {σ : Type w} [Field k]
    (I : Ideal (MvPolynomial σ k)) (z : σ → k)
    (hI : I ≤ RingHom.ker (MvPolynomial.aeval z).toRingHom) :
    (MvPolynomial σ k ⧸ I) →ₐ[k] k :=
  Ideal.Quotient.liftₐ I (MvPolynomial.aeval z) hI

@[simp]
theorem affineQuotientRationalPoint_mk
    {k : Type u} {σ : Type w} [Field k]
    (I : Ideal (MvPolynomial σ k)) (z : σ → k)
    (hI : I ≤ RingHom.ker (MvPolynomial.aeval z).toRingHom)
    (f : MvPolynomial σ k) :
    affineQuotientRationalPoint I z hI (Ideal.Quotient.mk I f) =
      MvPolynomial.aeval z f := by
  rfl

/-- Literal affine-quotient specialization: the residue field of the local
ring of `k[\sigma]/I` at the point induced by `z` is `k`. -/
noncomputable def affineQuotientRationalPointResidueFieldAlgEquiv
    {k : Type u} {σ : Type w} [Field k]
    (I : Ideal (MvPolynomial σ k)) (z : σ → k)
    (hI : I ≤ RingHom.ker (MvPolynomial.aeval z).toRingHom) :
    (RingHom.ker (affineQuotientRationalPoint I z hI).toRingHom).ResidueField
      ≃ₐ[k] k :=
  rationalPointResidueFieldAlgEquiv (affineQuotientRationalPoint I z hI)

end

end TranslatedDepthSeven
