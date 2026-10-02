import TranslatedDepthSeven.FiniteIntegralFibreCardinalityInternal
import TranslatedDepthSeven.HomogeneousNormalizationDegreeBoundInternal

/-!
# The degree bound for every fibre of a linear normalization

The generic-rank bound from the source Hilbert polynomial and the monic
specialization argument give a degree bound for distinct points in every
fibre, including exceptional fibres. This does not require the source to
be geometrically integral, and makes no assertion about fibre lengths.
-/

namespace TranslatedDepthSeven

noncomputable section
open MvPolynomial Published
open scoped nonZeroDivisors
attribute [local instance] MvPolynomial.gradedAlgebra
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 300000

/-- Any finite set of field-valued points in one fibre of a homogeneous
linear Noether normalization has cardinality at most the projective degree. -/
theorem finite_homogeneousNormalization_fibre_card_le_projectiveDegree
    {K : Type*} [Field K] [CharZero K] {N r d : ℕ}
    (I : Ideal (MvPolynomial (Fin (N + 1)) K))
    (hprime : I.IsPrime) (D : HomogeneousLinearNormalizationData I)
    (hdegree : HasProjectiveDimensionDegree I r d)
    (specialization : MvPolynomial (Fin D.parameterCount) K →ₐ[K] K)
    (S : Finset ((MvPolynomial (Fin (N + 1)) K ⧸ I) →ₐ[K] K))
    (hS : ∀ f ∈ S, f.comp D.hom = specialization) :
    S.card ≤ d := by
  letI : I.IsPrime := hprime
  let B := MvPolynomial (Fin D.parameterCount) K
  let A := MvPolynomial (Fin (N + 1)) K ⧸ I
  letI : Algebra B A := D.hom.toRingHom.toAlgebra
  letI : FaithfulSMul B A :=
    (faithfulSMul_iff_algebraMap_injective B A).mpr D.hom_injective
  letI : Module.Finite B A := D.hom_finite
  have hbound := finite_fibre_card_le_localized_rank
    (B := B) (A := A) specialization.toRingHom S (by
      intro f hf b
      exact congrArg (fun g : B →ₐ[K] K ↦ g b) (hS f hf))
  exact hbound.trans
    (homogeneousLinearNormalization_genericRank_le_projectiveDegree I hprime D hdegree).2

end
end TranslatedDepthSeven
