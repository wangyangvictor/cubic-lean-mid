import HessianTheorem11.UnconditionalGenericDifferentials
import Mathlib.RingTheory.Localization.Integral
import Mathlib.RingTheory.NoetherNormalization

/-! An actual differential basis of a finite-type domain's function field,
obtained from an injective integral Noether-normalization map. -/

noncomputable section
namespace HessianTheorem11.UnconditionalGeneric
open Module MvPolynomial

/-- Noether-normalization coordinates give a differential basis of the
actual fraction field. Characteristic zero supplies separability. -/
theorem exists_differential_basis_of_normalization
    (K A : Type*) [Field K] [CharZero K] [CommRing A] [IsDomain A] [Algebra K A]
    {d : ℕ} (g : MvPolynomial (Fin d) K →ₐ[K] A)
    (hg : Function.Injective g) (hint : g.IsIntegral) :
    Nonempty (Basis (Fin d) (FractionRing A) (KaehlerDifferential K (FractionRing A))) := by
  letI : Algebra (MvPolynomial (Fin d) K) A := g.toAlgebra
  letI : IsScalarTower K (MvPolynomial (Fin d) K) A := IsScalarTower.of_algHom g
  letI : FaithfulSMul (MvPolynomial (Fin d) K) A :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr hg
  letI : Algebra.IsIntegral (MvPolynomial (Fin d) K) A := ⟨hint⟩
  letI : Algebra (FractionRing (MvPolynomial (Fin d) K)) (FractionRing A) :=
    FractionRing.liftAlgebra (MvPolynomial (Fin d) K) (FractionRing A)
  letI : IsScalarTower (MvPolynomial (Fin d) K)
      (FractionRing (MvPolynomial (Fin d) K)) (FractionRing A) :=
    FractionRing.isScalarTower_liftAlgebra (MvPolynomial (Fin d) K) (FractionRing A)
  letI : Algebra.IsAlgebraic (FractionRing (MvPolynomial (Fin d) K)) (FractionRing A) :=
    isAlgebraic_of_isFractionRing (R := MvPolynomial (Fin d) K) (S := A)
      (FractionRing (MvPolynomial (Fin d) K)) (FractionRing A)
  exact ⟨separatingDifferentialBasis K (FractionRing (MvPolynomial (Fin d) K))
    (FractionRing A) (Fin d)⟩

/-- An actual finitely generated domain admits a finite differential basis
of its function field, with its size witnessed by a Noether-normalization
embedding. No dimension, smoothness or generic-rank input is used. -/
theorem exists_normalization_differential_basis
    (K A : Type*) [Field K] [CharZero K] [CommRing A] [IsDomain A] [Algebra K A]
    [Algebra.FiniteType K A] :
    ∃ (d : ℕ) (g : MvPolynomial (Fin d) K →ₐ[K] A),
      Function.Injective g ∧ g.IsIntegral ∧
      Nonempty (Basis (Fin d) (FractionRing A) (KaehlerDifferential K (FractionRing A))) := by
  obtain ⟨d,g,hg,hint⟩ := exists_integral_inj_algHom_of_fg K A
  exact ⟨d,g,hg,hint,exists_differential_basis_of_normalization K A g hg hint⟩

end HessianTheorem11.UnconditionalGeneric
