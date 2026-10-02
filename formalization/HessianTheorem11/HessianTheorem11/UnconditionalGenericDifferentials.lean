import Mathlib.RingTheory.Etale.Field
import Mathlib.RingTheory.Etale.Kaehler
import Mathlib.RingTheory.Kaehler.Polynomial
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.RingTheory.Localization.FractionRing

/-! Differential bases for separable extensions of rational function fields.
This is the field-algebra step toward identifying generic Jacobian ranks.
All assertions are proved from mathlib; no geometric theorem is an input. -/

noncomputable section
namespace HessianTheorem11.UnconditionalGeneric
open scoped TensorProduct nonZeroDivisors
open Module

variable (K F L : Type*) (σ : Type*) [Field K] [Field F] [Field L]
  [Algebra K L] [Algebra (MvPolynomial σ K) F]
  [IsFractionRing (MvPolynomial σ K) F]
  [Algebra (MvPolynomial σ K) L] [Algebra F L]
  [IsScalarTower K (MvPolynomial σ K) L]
  [IsScalarTower (MvPolynomial σ K) F L]
  [Algebra.IsSeparable F L]

/-- A separating rational-function coordinate family gives an actual
basis of the differentials of the extension field. -/
def separatingDifferentialBasis : Basis σ L (KaehlerDifferential K L) := by
  letI : Algebra.FormallyEtale (MvPolynomial σ K) F :=
    Algebra.FormallyEtale.of_isLocalization ((MvPolynomial σ K)⁰)
  letI : Algebra.FormallyEtale F L := Algebra.FormallyEtale.of_isSeparable F L
  letI : Algebra.FormallyEtale (MvPolynomial σ K) L :=
    Algebra.FormallyEtale.comp (MvPolynomial σ K) F L
  exact ((KaehlerDifferential.mvPolynomialBasis K σ).baseChange L).map
    (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale K (MvPolynomial σ K) L)

@[simp] theorem separatingDifferentialBasis_apply (i : σ) :
    separatingDifferentialBasis K F L σ i =
      KaehlerDifferential.D K L (algebraMap (MvPolynomial σ K) L (MvPolynomial.X i)) := by
  letI : Algebra.FormallyEtale (MvPolynomial σ K) F :=
    Algebra.FormallyEtale.of_isLocalization ((MvPolynomial σ K)⁰)
  letI : Algebra.FormallyEtale F L := Algebra.FormallyEtale.of_isSeparable F L
  letI : Algebra.FormallyEtale (MvPolynomial σ K) L :=
    Algebra.FormallyEtale.comp (MvPolynomial σ K) F L
  simp only [separatingDifferentialBasis, Basis.map_apply, Basis.baseChange_apply,
    KaehlerDifferential.mvPolynomialBasis_apply,
    KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale_apply,
    KaehlerDifferential.mapBaseChange_tmul, one_smul, KaehlerDifferential.map_D]

include F in
/-- The differential dimension is the number of separating coordinates;
there is no smoothness or dimension premise. -/
theorem differential_finrank_of_separating_coordinates [Fintype σ] :
    finrank L (KaehlerDifferential K L) = Fintype.card σ :=
  finrank_eq_card_basis (separatingDifferentialBasis K F L σ)

end HessianTheorem11.UnconditionalGeneric
