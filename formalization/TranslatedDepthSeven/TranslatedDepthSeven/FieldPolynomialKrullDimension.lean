import TranslatedDepthSeven.SmoothLocalDimensionBridge
import Mathlib.RingTheory.Etale.Field
import Mathlib.RingTheory.Etale.Kaehler
import Mathlib.RingTheory.Jacobson.Ring
import Mathlib.RingTheory.Kaehler.Polynomial
import Mathlib.RingTheory.KrullDimension.Field
import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
import Mathlib.RingTheory.Localization.FractionRing

/-!
# Krull dimension of a finite polynomial algebra over a field

The pinned Mathlib version does not yet contain the general formula for the
Krull dimension of a finite multivariate polynomial ring over a Noetherian
base.  The field case needed here has a short proof which avoids that missing
result.

At a maximal ideal, Zariski's lemma makes the residue field a finite
separable extension of the ground field.  Formal smoothness therefore
identifies the cotangent dimension with the number of polynomial variables.
Krull's height theorem gives the upper bound on the height of every maximal
ideal.  The usual coordinate-prime chain gives the reverse inequality.
-/

namespace TranslatedDepthSeven

noncomputable section

open scoped TensorProduct
open KaehlerDifferential IsLocalRing

universe u

/-- The differential module of the localization of a polynomial algebra at
an arbitrary prime retains the standard basis `dX_i`. -/
noncomputable def mvPolynomialAtPrimeKaehlerBasis
    (k : Type u) [Field k] (n : ℕ)
    (p : Ideal (MvPolynomial (Fin n) k)) [p.IsPrime] :
    Module.Basis (Fin n) (Localization.AtPrime p)
      Ω[Localization.AtPrime p⁄k] := by
  let R := MvPolynomial (Fin n) k
  let S := Localization.AtPrime p
  letI : Algebra.FormallyEtale R S :=
    Algebra.FormallyEtale.of_isLocalization p.primeCompl
  exact
    ((KaehlerDifferential.mvPolynomialBasis k (Fin n)).baseChange S).map
      (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale k R S)

/-- The residue field at a maximal ideal of a finite polynomial algebra is
finite over the ground field.  This is the precise Zariski-lemma input used
in the dimension proof. -/
theorem mvPolynomial_maximal_residueField_finite
    (k : Type u) [Field k] (n : ℕ)
    (m : Ideal (MvPolynomial (Fin n) k)) [m.IsMaximal] :
    Module.Finite k m.ResidueField := by
  let R := MvPolynomial (Fin n) k
  let L := m.ResidueField
  have hRL : Function.Surjective (algebraMap R L) := by
    intro x
    obtain ⟨y, hy⟩ := (Ideal.bijective_algebraMap_quotient_residueField m).2 x
    obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective y
    exact ⟨f, hy⟩
  have hkR : (algebraMap k R).FiniteType := by
    rw [RingHom.finiteType_algebraMap]
    infer_instance
  have hkL : (algebraMap k L).FiniteType := by
    simpa only [IsScalarTower.algebraMap_eq k R L] using
      hkR.comp_surjective hRL
  letI : Algebra.FiniteType k L :=
    RingHom.finiteType_algebraMap.mp hkL
  exact finite_of_finite_type_of_isJacobsonRing k L

/-- Every maximal ideal of `k[X₁,…,Xₙ]` has height at most `n`.

The proof is local but does not invoke a regular-local-ring theorem: the
already proved cotangent/height inequality is combined with the explicit
localized `dX_i` basis. -/
theorem mvPolynomial_maximal_height_le
    (k : Type u) [Field k] [CharZero k] (n : ℕ)
    (m : Ideal (MvPolynomial (Fin n) k)) [m.IsMaximal] :
    m.height ≤ (n : ℕ∞) := by
  let R := MvPolynomial (Fin n) k
  let S := Localization.AtPrime m
  let L := ResidueField S
  letI : Module.Finite k L :=
    mvPolynomial_maximal_residueField_finite k n m
  letI : Algebra.IsIntegral k L := Algebra.IsIntegral.of_finite k L
  letI : Algebra.IsSeparable k L := Algebra.IsSeparable.of_integral k L
  letI : Algebra.FormallyEtale k L :=
    Algebra.FormallyEtale.of_isSeparable k L
  letI : Algebra.FormallySmooth R S :=
    Algebra.FormallySmooth.of_isLocalization m.primeCompl
  letI : Algebra.FormallySmooth k S :=
    Algebra.FormallySmooth.comp k R S
  let bS : Module.Basis (Fin n) S Ω[S⁄k] :=
    mvPolynomialAtPrimeKaehlerBasis k n m
  let bL : Module.Basis (Fin n) L (L ⊗[S] Ω[S⁄k]) := bS.baseChange L
  have hfinrank : Module.finrank L (L ⊗[S] Ω[S⁄k]) = n := by
    rw [Module.finrank_eq_card_basis bL, Fintype.card_fin]
  have hdim : ringKrullDim S ≤ (n : WithBot ℕ∞) := by
    have h := ringKrullDim_le_finrank_residualKaehler (R := S) k
    rw [hfinrank] at h
    exact h
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height m S] at hdim
  exact WithBot.coe_le_coe.mp hdim

/-- Exact Krull dimension of a polynomial algebra in finitely many variables
over a field, proved without the unproved general Noetherian-base theorem. -/
theorem ringKrullDim_mvPolynomial_fin_eq_of_field
    (k : Type u) [Field k] [CharZero k] (n : ℕ) :
    ringKrullDim (MvPolynomial (Fin n) k) = (n : WithBot ℕ∞) := by
  apply le_antisymm
  · rw [ringKrullDim_le_iff_isMaximal_height_le]
    intro m hm
    letI : m.IsMaximal := hm
    exact_mod_cast mvPolynomial_maximal_height_le k n m
  · have h := ringKrullDim_add_natCard_le_ringKrullDim_mvPolynomial
        (R := k) (Fin n)
    simpa only [ringKrullDim_eq_zero_of_field, zero_add, Nat.card_fin] using h

end

end TranslatedDepthSeven
