import Mathlib.RingTheory.Etale.Field
import Mathlib.FieldTheory.Perfect
import TranslatedDepthSeven.AlgebraicallyClosedCoefficientPrime

/-! A finite reduced algebra over a perfect field stays reduced after every
field extension. The proof uses the actual finite Artinian decomposition
into fields and separability, with no geometric reducedness premise. -/

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 300000
noncomputable section
namespace CubicTenVariables.FiniteReducedGeometric
open scoped TensorProduct

attribute [local instance] IsArtinianRing.fieldOfSubtypeIsMaximal in
theorem formallyEtale (k A : Type*) [Field k] [PerfectField k]
    [CommRing A] [Algebra k A] [Module.Finite k A] [IsReduced A] :
    Algebra.FormallyEtale k A := by
  classical
  letI : IsArtinianRing A := isArtinian_of_tower k inferInstance
  let e : A ≃ₐ[k] (∀ i : MaximalSpectrum A, A ⧸ i.asIdeal) :=
    { __ := IsArtinianRing.equivPi A, commutes' := fun r => rfl }
  apply (Algebra.FormallyEtale.iff_exists_algEquiv_prod k A).mpr
  refine ⟨MaximalSpectrum A, inferInstance, (fun i => A ⧸ i.asIdeal),
    inferInstance, inferInstance, e, ?_⟩
  intro i
  infer_instance

theorem tensor_isReduced (k A E : Type*) [Field k] [PerfectField k]
    [CommRing A] [Algebra k A] [Module.Finite k A] [IsReduced A]
    [Field E] [Algebra k E] : IsReduced (E ⊗[k] A) := by
  letI : Algebra.FormallyEtale k A := formallyEtale k A
  exact Algebra.FormallyUnramified.isReduced_of_field E (E ⊗[k] A)

/-- Literal coefficient extension of a finite reduced polynomial quotient. -/
theorem polynomial_quotient_isReduced
    {k E σ : Type*} [Field k] [PerfectField k] [Field E] [Algebra k E]
    (I : Ideal (MvPolynomial σ k)) [Module.Finite k (MvPolynomial σ k ⧸ I)]
    (hI : I.IsRadical) :
    IsReduced (MvPolynomial σ E ⧸ I.map (MvPolynomial.map (algebraMap k E))) := by
  letI : IsReduced (MvPolynomial σ k ⧸ I) :=
    (Ideal.isRadical_iff_quotient_reduced I).mp hI
  letI : IsReduced (E ⊗[k] (MvPolynomial σ k ⧸ I)) := tensor_isReduced k _ E
  exact isReduced_of_injective
    (TranslatedDepthSeven.polynomialQuotientTensorAlgEquiv (L := E) I).toRingHom
    (TranslatedDepthSeven.polynomialQuotientTensorAlgEquiv (L := E) I).injective

end CubicTenVariables.FiniteReducedGeometric
