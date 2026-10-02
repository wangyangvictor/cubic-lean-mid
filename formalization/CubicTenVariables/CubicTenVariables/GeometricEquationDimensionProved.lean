import TranslatedDepthSeven.QbarPrimeAlgebraicCoefficientExtension
import TranslatedDepthSeven.PrimeAffineNoetherNormalization
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import CubicTenVariables.FixedFamilyFiberPointCount

/-! An algebraic coefficient extension preserves the Krull dimension of
the literal equation quotient, including the empty-fiber case. These are
unconditional identities; no point-counting premise is used. -/

set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.GeometricEquationDimensionProved
open MvPolynomial

local instance {K L σ : Type*} [Field K] [Field L] [Algebra K L] :
    Algebra (MvPolynomial σ K) (MvPolynomial σ L) :=
  MvPolynomial.algebraMvPolynomial

theorem integralExtension_quotient_dimension
    {K L σ : Type*} [Field K] [Field L] [Algebra K L]
    [Algebra.IsIntegral K L] (I : Ideal (MvPolynomial σ K)) :
    ringKrullDim (MvPolynomial σ L ⧸ I.map (map (algebraMap K L))) =
      ringKrullDim (MvPolynomial σ K ⧸ I) := by
  by_cases hI : I = ⊤
  · subst I
    simp [Ideal.map_top, ringKrullDim_eq_bot_of_subsingleton]
  let R := MvPolynomial σ K
  let S := MvPolynomial σ L
  let f : R →+* S := map (algebraMap K L)
  let J := I.map f
  letI : Module.FaithfullyFlat R S := TranslatedDepthSeven.mvPolynomial_faithfullyFlat
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
    TranslatedDepthSeven.ringKrullDim_eq_of_isIntegral_injective
      (show Function.Injective g from Ideal.quotientMap_injective)
  rw [hcontract] at hdim
  exact hdim

theorem algebraicClosure_quotient_dimension
    {K σ : Type*} [Field K] (I : Ideal (MvPolynomial σ K)) :
    ringKrullDim (MvPolynomial σ (AlgebraicClosure K) ⧸
      I.map (map (algebraMap K (AlgebraicClosure K)))) =
      ringKrullDim (MvPolynomial σ K ⧸ I) :=
  integralExtension_quotient_dimension I

theorem geometricEquationDimension_eq_quotient
    {n t : ℕ} {K : Type*} [Field K]
    (g : Fin t → MvPolynomial (Fin n) K) :
    Literature.geometricEquationDimension g =
      ringKrullDim (MvPolynomial (Fin n) K ⧸ Ideal.span (Set.range g)) := by
  have hid : (Ideal.span (Set.range g)).map (map (algebraMap K (AlgebraicClosure K))) =
      Ideal.span (Set.range (fun i => map (algebraMap K (AlgebraicClosure K)) (g i))) := by
    rw [Ideal.map_span, ← Set.range_comp']
  unfold Literature.geometricEquationDimension
  rw [← hid]
  exact algebraicClosure_quotient_dimension _

theorem geometricFiberDimension_eq_quotient
    {m n t : ℕ} (f : Fin t → BihomogeneousIncidenceFamily.Polynomial m n)
    (K : Type*) [Field K] (v : Fin m → K) :
    IntegralGeometricFiberDepth.geometricFiberDimension f K v =
      ringKrullDim (MvPolynomial (Fin n) K ⧸ Literature.integralFamilyFiberIdeal f K v) := by
  rw [← FixedFamilyFiberPointCount.geometric_dimension_specialize]
  exact geometricEquationDimension_eq_quotient _

end CubicTenVariables.GeometricEquationDimensionProved
