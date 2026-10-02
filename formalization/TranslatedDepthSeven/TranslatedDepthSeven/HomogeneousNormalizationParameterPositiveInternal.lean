import TranslatedDepthSeven.HomogeneousIrrelevantDimensionFieldInternal
import TranslatedDepthSeven.ParameterCountSurface
import TranslatedDepthSeven.FieldPolynomialKrullDimension
import TranslatedDepthSeven.FiniteComponentFrontier

/-! # A nonempty projective homogeneous prime has positive normalization dimension

The homogeneous prime is strictly contained in the irrelevant maximal ideal.
This two-prime chain forces positive affine dimension, hence at least one
parameter in every finite injective linear normalization. No Hilbert
polynomial or degree certificate is used.
-/

namespace TranslatedDepthSeven

noncomputable section

open MvPolynomial Published
attribute [local instance] MvPolynomial.gradedAlgebra

set_option maxHeartbeats 1000000

theorem HomogeneousLinearNormalizationData.parameterCount_pos_of_irrelevant_not_le
    {K : Type*} [Field K] [CharZero K] {N : ℕ}
    (I : Ideal (MvPolynomial (Fin (N + 1)) K))
    (hprime : I.IsPrime)
    (hhom : I.IsHomogeneous (homogeneousSubmodule (Fin (N + 1)) K))
    (hirr : ¬ projectiveIrrelevantIdeal K N ≤ I)
    (D : HomogeneousLinearNormalizationData I) : 0 < D.parameterCount := by
  let J := projectiveIrrelevantIdeal K N
  have hle : I ≤ J := by
    intro f hf
    have hz := homogeneousPrimeIdeal_le_eval_zero I hprime hhom hf
    dsimp only [J]
    rw [projectiveIrrelevantIdeal_eq_ker_constantCoeff_over_field]
    apply RingHom.mem_ker.mpr
    simpa only [RingHom.mem_ker, MvPolynomial.eval_zero] using hz
  have hlt : I < J := lt_of_le_not_ge hle hirr
  have hmax : J.IsMaximal := by
    dsimp only [J]
    rw [projectiveIrrelevantIdeal_eq_ker_constantCoeff_over_field]
    apply RingHom.ker_isMaximal_of_surjective
    intro a
    exact ⟨C a, by simp⟩
  letI : I.IsPrime := hprime
  letI : J.IsMaximal := hmax
  have hdimension := D.ringKrullDim_eq_parameterPolynomial (N + 1) I hprime
  rw [ringKrullDim_mvPolynomial_fin_eq_of_field K D.parameterCount] at hdimension
  have hfinite : ringKrullDim (MvPolynomial (Fin (N + 1)) K ⧸ I) < ⊤ := by
    rw [hdimension]
    exact WithBot.coe_lt_coe.mpr (ENat.coe_lt_top _)
  have hdrop := ringKrullDim_quotient_lt_of_prime_lt I J hlt hfinite
  have hzero := ringKrullDim_quotient_eq_zero_of_irrelevant_le_over_field
    N J hmax.isPrime le_rfl
  rw [hzero, hdimension] at hdrop
  exact_mod_cast hdrop

end
end TranslatedDepthSeven
