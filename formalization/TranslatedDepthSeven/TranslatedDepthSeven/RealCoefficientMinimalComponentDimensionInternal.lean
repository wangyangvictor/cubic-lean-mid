import TranslatedDepthSeven.PushoutTensorAlgebraEquivalenceInternal
import TranslatedDepthSeven.FiniteTorsionFreeAlgebraComponentsInternal
import TranslatedDepthSeven.MinimalComponentDimensionQuotientEquivalenceInternal
import TranslatedDepthSeven.ParameterCountSurface
import TranslatedDepthSeven.FieldPolynomialKrullDimension

/-!
# Equidimensionality of the real coefficient extension of a rational domain

Choose a finite injective polynomial normalization of the rational
coordinate domain. Its scalar extension to the real polynomial base is
finite and torsion-free. Every minimal component therefore has exactly
the base dimension. Explicit tensor algebra equivalences identify these
components with those of the original coefficient-extended ideal.

No geometric reducedness, Galois transitivity, or component-degree
statement is used in this dimension argument.
-/

namespace TranslatedDepthSeven

noncomputable section
open scoped TensorProduct
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 300000

noncomputable local instance realPolynomialCoefficientAlgebraForComponents {σ : Type*} :
    Algebra (MvPolynomial σ ℚ) (MvPolynomial σ ℝ) :=
  MvPolynomial.algebraMvPolynomial

theorem realCoefficient_minimalComponent_dimension_eq_parameterCount
    {N : ℕ} (I : Ideal (MvPolynomial (Fin N) ℚ)) (hI : I.IsPrime)
    (D : HomogeneousLinearNormalizationData I)
    (P : Ideal (MvPolynomial (Fin N) ℝ))
    (hP : P ∈ (I.map (MvPolynomial.map (algebraMap ℚ ℝ))).minimalPrimes) :
    ringKrullDim (MvPolynomial (Fin N) ℝ ⧸ P) = (D.parameterCount : WithBot ℕ∞) := by
  let A := MvPolynomial (Fin N) ℚ ⧸ I
  let B := MvPolynomial (Fin D.parameterCount) ℚ
  let S := MvPolynomial (Fin D.parameterCount) ℝ
  letI : I.IsPrime := hI
  letI : IsDomain A := Ideal.Quotient.isDomain I
  letI : Algebra B A := D.hom.toRingHom.toAlgebra
  haveI : Module.Finite B A := D.hom_finite
  haveI : NoZeroSMulDivisors B A :=
    NoZeroSMulDivisors.iff_algebraMap_injective.mpr D.hom_injective
  let J := I.map (MvPolynomial.map (algebraMap ℚ ℝ))
  let E : (MvPolynomial (Fin N) ℝ ⧸ J) ≃ₐ[ℝ] S ⊗[B] A :=
    (realCoefficientQuotientTensorAlgEquiv I).trans
      (pushoutTensorAlgebraEquiv ℚ ℝ B S A).symm
  apply ringKrullDim_minimalComponent_of_quotient_equiv (C := S ⊗[B] A)
    J E.toRingEquiv (D.parameterCount : WithBot ℕ∞) ?_ P hP
  intro Q hQ
  exact (ringKrullDim_baseChange_component_eq_of_finite_torsionFree B S A Q hQ).trans
    (ringKrullDim_mvPolynomial_fin_eq_of_field ℝ D.parameterCount)

/-- All reduced real components have the same affine dimension as the
original rational domain. -/
theorem realCoefficient_minimalComponent_dimension_eq_source
    {N : ℕ} (I : Ideal (MvPolynomial (Fin N) ℚ)) (hI : I.IsPrime)
    (D : HomogeneousLinearNormalizationData I)
    (P : Ideal (MvPolynomial (Fin N) ℝ))
    (hP : P ∈ (I.map (MvPolynomial.map (algebraMap ℚ ℝ))).minimalPrimes) :
    ringKrullDim (MvPolynomial (Fin N) ℝ ⧸ P) =
      ringKrullDim (MvPolynomial (Fin N) ℚ ⧸ I) := by
  rw [realCoefficient_minimalComponent_dimension_eq_parameterCount I hI D P hP,
    D.ringKrullDim_eq_parameterPolynomial N I hI,
    ringKrullDim_mvPolynomial_fin_eq_of_field ℚ D.parameterCount]

end
end TranslatedDepthSeven
