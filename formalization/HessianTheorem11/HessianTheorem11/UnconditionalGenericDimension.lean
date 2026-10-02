import HessianTheorem11.UnconditionalGenericNormalization
import HessianTheorem11.UnconditionalGenericDerivation
import HessianTheorem11.UnconditionalPolynomialDimension

/-! Krull dimension equals the function-field differential dimension for
actual finite-type domains over the geometric field. -/

noncomputable section
namespace HessianTheorem11.UnconditionalGeneric
open Module

variable (A : Type*) [CommRing A] [IsDomain A]
  [Algebra GeometricField A] [Algebra.FiniteType GeometricField A]

/-- The usual dimension/differential theorem, obtained from an actual
normalization map and a separately constructed differential basis. -/
theorem krull_dimension_eq_differential_finrank :
    ringKrullDim A = (finrank (FractionRing A)
      (KaehlerDifferential GeometricField (FractionRing A)) : Dimension) := by
  letI : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing GeometricField A
  obtain ⟨d,g,hg,hint,⟨b⟩⟩ := exists_normalization_differential_basis GeometricField A
  rw [finrank_eq_card_basis b,Fintype.card_fin]
  exact UnconditionalPolynomialDimension.normalization_dimension A g hg hint

theorem functionField_differentials_finite :
    FiniteDimensional (FractionRing A) (KaehlerDifferential GeometricField (FractionRing A)) := by
  obtain ⟨d,g,hg,hint,⟨b⟩⟩ := exists_normalization_differential_basis GeometricField A
  exact Module.Finite.of_basis b

/-- Equivalently, Krull dimension counts base derivations of the domain
with values in its actual fraction field. -/
theorem krull_dimension_eq_derivation_finrank :
    ringKrullDim A = (finrank (FractionRing A)
      (Derivation GeometricField A (FractionRing A)) : Dimension) := by
  letI := functionField_differentials_finite A
  rw [derivation_finrank_eq_differential_finrank]
  exact krull_dimension_eq_differential_finrank A

end HessianTheorem11.UnconditionalGeneric
