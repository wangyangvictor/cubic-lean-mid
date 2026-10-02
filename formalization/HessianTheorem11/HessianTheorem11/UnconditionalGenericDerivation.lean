import HessianTheorem11.UnconditionalGenericDifferentials
import Mathlib.LinearAlgebra.Dual.Lemmas

/-! Derivations of a domain with values in its fraction field extend
uniquely to that field. The extension is constructed through the proved
localization theorem for Kähler differentials. -/

noncomputable section
namespace HessianTheorem11.UnconditionalGeneric
open Module
open scoped TensorProduct nonZeroDivisors

variable (K A F : Type*) [CommRing K] [CommRing A] [Field F]
  [Algebra K A] [Algebra K F] [Algebra A F] [IsScalarTower K A F]
  [IsFractionRing A F]

/-- The actual restriction map on derivations is bijective for a fraction
field, with no separability or smoothness assumption. -/
theorem fraction_derivation_restriction_bijective :
    Function.Bijective (Derivation.compAlgebraMapL K A F F) := by
  constructor
  · intro d e h
    apply Derivation.ext
    intro x
    obtain ⟨a,b,rfl⟩ := IsLocalization.exists_mk'_eq A⁰ x
    rw [IsFractionRing.mk'_eq_div,d.leibniz_div,e.leibniz_div]
    have ha : d (algebraMap A F a) = e (algebraMap A F a) :=
      Derivation.congr_fun h a
    have hb : d (algebraMap A F b) = e (algebraMap A F b) :=
      Derivation.congr_fun h b
    rw [ha,hb]
  · intro d
    letI : Algebra.FormallyEtale A F := Algebra.FormallyEtale.of_isLocalization A⁰
    let E := KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale K A F
    let l : KaehlerDifferential K F →ₗ[F] F :=
      (d.liftKaehlerDifferential.liftBaseChange F).comp E.symm.toLinearMap
    let e : Derivation K F F := l.compDer (KaehlerDifferential.D K F)
    refine ⟨e,?_⟩
    apply Derivation.ext
    intro a
    change d.liftKaehlerDifferential.liftBaseChange F
      (E.symm (KaehlerDifferential.D K F (algebraMap A F a))) = d a
    rw [KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale_symm_D_algebraMap]
    simp

/-- A linear equivalence, over the fraction field, rather than just an
existence statement for each separate derivation. -/
def fractionDerivationEquiv : Derivation K F F ≃ₗ[F] Derivation K A F :=
  LinearEquiv.ofBijective (Derivation.compAlgebraMapL K A F F)
    (fraction_derivation_restriction_bijective K A F)

/-- The dual of the actual field differential module parametrizes all
base-linear derivations of the coordinate domain into its fraction field. -/
def genericDerivationDualEquiv :
    Module.Dual F (KaehlerDifferential K F) ≃ₗ[F] Derivation K A F :=
  (KaehlerDifferential.linearMapEquivDerivation K F (M := F)).trans
    (fractionDerivationEquiv K A F)

theorem derivation_finrank_eq_differential_finrank
    [FiniteDimensional F (KaehlerDifferential K F)] :
    finrank F (Derivation K A F) = finrank F (KaehlerDifferential K F) := by
  rw [← (genericDerivationDualEquiv K A F).finrank_eq, Subspace.dual_finrank_eq]

end HessianTheorem11.UnconditionalGeneric
