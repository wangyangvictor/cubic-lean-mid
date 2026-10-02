import TranslatedDepthSeven.QbarComponentKrullDimension
import HessianTheorem11.UnconditionalCutDimension

/-! The rational equation ideal and its actual geometric zero locus have
identical Krull dimension. Nilpotents in the equation quotient do not change
this dimension. The coefficient extension to the algebraic closure is
integral and faithfully flat. -/

namespace CubicTenVariables.RationalEquationDimension
open TranslatedDepthSeven
noncomputable section
local instance {σ : Type*} :
    Algebra (MvPolynomial σ ℚ) (MvPolynomial σ Qbar) :=
  MvPolynomial.algebraMvPolynomial

theorem qbar_quotient_dimension {σ : Type*}
    (I : Ideal (MvPolynomial σ ℚ)) (hI : I ≠ ⊤) :
    ringKrullDim (MvPolynomial σ Qbar ⧸
      I.map (MvPolynomial.map (algebraMap ℚ Qbar))) =
    ringKrullDim (MvPolynomial σ ℚ ⧸ I) := by
  let R := MvPolynomial σ ℚ
  let S := MvPolynomial σ Qbar
  let f : R →+* S := MvPolynomial.map (algebraMap ℚ Qbar)
  let J := I.map f
  have hcontract : J.comap f = I :=
    Ideal.comap_map_eq_self_of_faithfullyFlat I
  have hJ : J ≠ ⊤ := by
    intro he
    apply hI
    rw [← hcontract, he, Ideal.comap_top]
  letI : Nontrivial (S ⧸ J) := Ideal.Quotient.nontrivial_iff.mpr hJ
  letI : Nontrivial (R ⧸ J.comap f) :=
    Ideal.Quotient.nontrivial_iff.mpr (by rw [hcontract]; exact hI)
  have hf : f.IsIntegral := by
    change (algebraMap R S).IsIntegral
    exact Algebra.IsIntegral.isIntegral
  let g : (R ⧸ J.comap f) →+* (S ⧸ J) := Ideal.quotientMap J f le_rfl
  letI : Algebra (R ⧸ J.comap f) (S ⧸ J) := g.toAlgebra
  letI : Algebra.IsIntegral (R ⧸ J.comap f) (S ⧸ J) :=
    ⟨RingHom.IsIntegral.quotient f hf⟩
  have hdim : ringKrullDim (S ⧸ J) = ringKrullDim (R ⧸ J.comap f) :=
    ringKrullDim_eq_of_isIntegral_injective
      (show Function.Injective g from Ideal.quotientMap_injective)
  rw [hcontract] at hdim
  exact hdim


theorem rational_quotient_dimension_eq_geometric_zeroLocus
    {σ : Type*} [Finite σ]
    (I : Ideal (MvPolynomial σ ℚ)) (hI : I ≠ ⊤) :
    HessianTheorem11.affineDimension
      (MvPolynomial.zeroLocus Qbar
        (I.map (MvPolynomial.map (algebraMap ℚ Qbar)))) =
      ringKrullDim (MvPolynomial σ ℚ ⧸ I) := by
  rw [HessianTheorem11.affineDimension,
    MvPolynomial.vanishingIdeal_zeroLocus_eq_radical,
    HessianTheorem11.UnconditionalCutDimension.quotient_radical_dimension]
  exact qbar_quotient_dimension I hI

end
end CubicTenVariables.RationalEquationDimension
