import CubicTenVariables.FixedEquationNormalization
import CubicTenVariables.LocalizedIntegerExceptionalSet
import TranslatedDepthSeven.PerfectFieldPolynomialKrullDimension
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic

/-! Geometric dimension bounds for every good-characteristic specialization
of one fixed integral equation family. No containment of any separately
defined characteristic-p locus is asserted. -/

noncomputable section
namespace CubicTenVariables.FixedEquationDimensionReduction
open MvPolynomial TranslatedDepthSeven FixedEquationNormalization

/-- The original literal integral equations, over an arbitrary coefficient ring. -/
def zeroSet {N t : ℕ} (f : Fin t → MvPolynomial (Fin N) ℤ)
    (K : Type*) [CommRing K] : Set (Fin N → K) :=
  {x | ∀ i, eval₂ (Int.castRingHom K) x (f i) = 0}

theorem equationIdeal_le_vanishingIdeal {N t : ℕ}
    (f : Fin t → MvPolynomial (Fin N) ℤ) (K : Type*) [Field K] :
    equationIdeal f K ≤ vanishingIdeal K (zeroSet f K) := by
  apply Ideal.span_le.mpr
  rintro _ ⟨i,rfl⟩ x hx
  change eval x (equationsOver f K i) = 0
  simpa only [equationsOver, eval_map] using hx i

/-- Passing to the actual reduced coordinate ring cannot increase dimension. -/
theorem zeroSet_dimension_le_quotient {N t : ℕ}
    (f : Fin t → MvPolynomial (Fin N) ℤ) (K : Type*) [Field K] :
    ringKrullDim (MvPolynomial (Fin N) K ⧸ vanishingIdeal K (zeroSet f K)) ≤
      ringKrullDim (MvPolynomial (Fin N) K ⧸ equationIdeal f K) :=
  ringKrullDim_le_of_surjective
    (Ideal.Quotient.factor (equationIdeal_le_vanishingIdeal f K))
    (Ideal.Quotient.factor_surjective _)

/-- Integral coefficient extension to an algebraic closure removes any
perfectness restriction from the polynomial-dimension formula. -/
theorem polynomial_dimension (K : Type*) [Field K] (s : ℕ) :
    ringKrullDim (MvPolynomial (Fin s) K) = (s : WithBot ℕ∞) := by
  letI : Algebra (MvPolynomial (Fin s) K)
      (MvPolynomial (Fin s) (AlgebraicClosure K)) :=
    MvPolynomial.algebraMvPolynomial
  have he : ringKrullDim (MvPolynomial (Fin s) (AlgebraicClosure K)) =
      ringKrullDim (MvPolynomial (Fin s) K) :=
    ringKrullDim_eq_of_isIntegral_injective
      (show Function.Injective (algebraMap (MvPolynomial (Fin s) K)
        (MvPolynomial (Fin s) (AlgebraicClosure K))) from
        MvPolynomial.map_injective _ (algebraMap K (AlgebraicClosure K)).injective)
  rw [← he]
  exact ringKrullDim_mvPolynomial_fin_eq_of_perfectField _ _

/-- A fixed finite normalization, with its monic relations and discrepancy
denominators cleared, controls dimension in every field specialization. -/
theorem exists_localized_dimension_bound {N t r : ℕ}
    (f : Fin t → MvPolynomial (Fin N) ℤ)
    (hproper : equationIdeal f ℚ ≠ ⊤)
    (hdim : ringKrullDim (MvPolynomial (Fin N) ℚ ⧸ equationIdeal f ℚ) ≤
      (r : WithBot ℕ∞)) :
    ∃ Δ : ℤ, Δ ≠ 0 ∧ ∃ δ : Localization.Away Δ, δ ≠ 0 ∧
      ∀ (K : Type) [Field K] (ρ : Localization.Away Δ →+* K),
        IsUnit (ρ δ) →
          ringKrullDim (MvPolynomial (Fin N) K ⧸ equationIdeal f K) ≤
            (r : WithBot ℕ∞) := by
  obtain ⟨s,hs,Δ,hΔ,q,p,hmonic,hmodel,hle,_hfinite⟩ :=
    exists_finite_model f hproper hdim
  let S := Localization.Away Δ
  letI : Algebra S ℚ := (awayToFractionRing (R := ℤ) (K := ℚ) Δ hΔ).toAlgebra
  letI : IsDomain S := IsLocalization.isDomain_of_le_nonZeroDivisors S
    (powers_le_nonZeroDivisors_of_noZeroDivisors hΔ)
  letI := IsScalarTower.of_algebraMap_eq (R := ℤ) (S := S) (A := ℚ)
    (fun z => (awayToFractionRing_algebraMap (R := ℤ) (K := ℚ) Δ hΔ z).symm)
  letI : IsFractionRing S ℚ :=
    IsFractionRing.isFractionRing_of_isLocalization (Submonoid.powers Δ) S ℚ
      (powers_le_nonZeroDivisors_of_noZeroDivisors hΔ)
  obtain ⟨δ,hδ,_hclear,hquantitative,_hcount⟩ :=
    exists_nonzero_base_open_quantitative_model_eq_componentClosure
      (equationIdeal f S) (equationsOver f S) q p hmonic
      (equationIdeal f ℚ) hle
      (map_equationIdeal f (algebraMap S ℚ)) hmodel
  refine ⟨Δ,hΔ,δ,hδ,?_⟩
  intro K _ ρ hρ
  obtain ⟨_g,_hg,hdimK,_hfibers⟩ := hquantitative K ρ hρ
  rw [map_equationIdeal, polynomial_dimension] at hdimK
  exact hdimK.trans (by exact_mod_cast hs)

/-- One positive integer is chosen before every prime and every field of
that characteristic. Both the original equation quotient and the actual
common-zero coordinate ring have the required dimension bound. This
includes algebraic closures of prime fields, not merely finite fields. -/
theorem exists_good_characteristic_dimension_bound {N t r : ℕ}
    (f : Fin t → MvPolynomial (Fin N) ℤ)
    (hproper : equationIdeal f ℚ ≠ ⊤)
    (hdim : ringKrullDim (MvPolynomial (Fin N) ℚ ⧸ equationIdeal f ℚ) ≤
      (r : WithBot ℕ∞)) :
    ∃ D : ℕ, 1 ≤ D ∧ ∀ (p : ℕ), p.Prime → ¬ p ∣ D →
      ∀ (K : Type) [Field K] [CharP K p],
        ringKrullDim (MvPolynomial (Fin N) K ⧸ equationIdeal f K) ≤
          (r : WithBot ℕ∞) ∧
        ringKrullDim (MvPolynomial (Fin N) K ⧸ vanishingIdeal K (zeroSet f K)) ≤
          (r : WithBot ℕ∞) := by
  obtain ⟨Δ,hΔ,δ,hδ,hbound⟩ := exists_localized_dimension_bound f hproper hdim
  obtain ⟨D,hD,_hΔD,hunit⟩ :=
    LocalizedIntegerExceptionalSet.exists_exceptionalInteger Δ hΔ δ hδ
  refine ⟨D,hD,?_⟩
  intro p hp hpD K _ _
  letI : Fact p.Prime := ⟨hp⟩
  obtain ⟨hpΔ,hu⟩ := hunit p hp hpD
  let ρ := (ZMod.castHom (dvd_refl p) K).comp (awayIntToZMod Δ p hp hpΔ)
  have hρ : IsUnit (ρ δ) := hu.map (ZMod.castHom (dvd_refl p) K)
  have hd := hbound K ρ hρ
  exact ⟨hd,(zeroSet_dimension_le_quotient f K).trans hd⟩

end CubicTenVariables.FixedEquationDimensionReduction
