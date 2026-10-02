import TranslatedDepthSeven.PrimeAffineNoetherNormalization
import Mathlib.FieldTheory.Separable
import Mathlib.FieldTheory.Perfect
import Mathlib.RingTheory.Algebraic.Integral
import Mathlib.Algebra.CharP.Algebra
import Mathlib.RingTheory.Etale.Field
import Mathlib.RingTheory.Etale.Kaehler
import Mathlib.RingTheory.Kaehler.Polynomial

/-!
# Differentials of the function field of a normalized affine domain

An injective finite normalization by a polynomial ring in `s` variables
identifies the dimension of the absolute Kahler differentials of the
fraction field with `s`.  The proof uses only localization, separability in
characteristic zero, and the standard polynomial differential basis.
-/

namespace TranslatedDepthSeven

noncomputable section

open KaehlerDifferential
open scoped TensorProduct

variable {R : Type*} [Field R] [CharZero R]
variable {s : ℕ}
variable {A : Type*} [CommRing A] [IsDomain A] [Algebra R A]

/-- The function field of a finite normalized affine domain has exactly one
independent differential for each normalization parameter. -/
theorem finrank_fractionRing_kaehler_eq_normalizationParameters
    (g : MvPolynomial (Fin s) R →ₐ[R] A)
    (hg : Function.Injective g) (hf : g.Finite) :
    Module.finrank (FractionRing A) Ω[FractionRing A⁄R] = s := by
  let B := MvPolynomial (Fin s) R
  let K := FractionRing B
  let L := FractionRing A
  letI : Algebra B A := g.toRingHom.toAlgebra
  letI : IsScalarTower R B A :=
    IsScalarTower.of_algebraMap_eq fun x ↦ by
      simp [RingHom.algebraMap_toAlgebra]
  letI : FaithfulSMul B A :=
    (faithfulSMul_iff_algebraMap_injective B A).mpr hg
  letI : Module.Finite B A := hf
  letI : CharZero B := charZero_of_injective_algebraMap
    (FaithfulSMul.algebraMap_injective R B)
  letI : CharZero A := charZero_of_injective_algebraMap
    (FaithfulSMul.algebraMap_injective R A)
  letI : Algebra K L := FractionRing.liftAlgebra B L
  letI : CharZero K :=
    charZero_of_injective_algebraMap (IsFractionRing.injective B K)
  haveI : Algebra.IsSeparable K L := by infer_instance
  letI : Algebra.FormallyEtale B K :=
    Algebra.FormallyEtale.of_isLocalization (nonZeroDivisors B)
  letI : Algebra.FormallyEtale K L :=
    Algebra.FormallyEtale.of_isSeparable K L
  let eBK : (K ⊗[B] (KaehlerDifferential R B)) ≃ₗ[K]
      KaehlerDifferential R K :=
    KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale R B K
  let eKL : (L ⊗[K] (KaehlerDifferential R K)) ≃ₗ[L]
      KaehlerDifferential R L :=
    KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale R K L
  calc
    Module.finrank L (KaehlerDifferential R L) =
        Module.finrank L (L ⊗[K] (KaehlerDifferential R K)) :=
      eKL.finrank_eq.symm
    _ = Module.finrank K (KaehlerDifferential R K) := Module.finrank_baseChange
    _ = Module.finrank K (K ⊗[B] (KaehlerDifferential R B)) :=
      eBK.finrank_eq.symm
    _ = Module.finrank B (KaehlerDifferential R B) := Module.finrank_baseChange
    _ = s := by
      rw [Module.finrank_eq_card_basis (mvPolynomialBasis R (Fin s)),
        Fintype.card_fin]

end

end TranslatedDepthSeven
