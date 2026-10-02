import TranslatedDepthSeven.PrincipalOpenReduction
import Mathlib.Algebra.Field.ZMod

/-!
# One integer exceptional set for a nonzero localized integer

A nonzero element of `ℤ[1/Δ]` has a nonzero integral numerator. The prime
divisors of that numerator and Δ contain all failures of its specialization
to be a unit. The exceptional integer is chosen before the prime.
-/

noncomputable section
namespace CubicTenVariables.LocalizedIntegerExceptionalSet
open TranslatedDepthSeven

/-- A nonzero localized integer has a nonzero numerator after multiplying
by an actual power of the inverted integer. -/
theorem exists_nonzero_numerator (Δ : ℤ) (δ : Localization.Away Δ) (hδ : δ ≠ 0) :
    ∃ (k : ℕ) (a : ℤ), a ≠ 0 ∧
      δ * (algebraMap ℤ (Localization.Away Δ) Δ)^k =
        algebraMap ℤ (Localization.Away Δ) a := by
  obtain ⟨k, a, ha⟩ := IsLocalization.Away.surj Δ δ
  refine ⟨k, a, ?_, ha⟩
  intro haz
  have hz : δ * (algebraMap ℤ (Localization.Away Δ) Δ)^k = 0 := by
    simpa only [haz, map_zero] using ha
  exact hδ ((IsLocalization.Away.algebraMap_pow_isUnit Δ k).mul_left_eq_zero.mp hz)

/-- Away from the actual numerator, specialization is a unit. The
displayed denominator identity is used only by this elementary helper. -/
theorem isUnit_specialization_of_numerator
    (Δ : ℤ) (δ : Localization.Away Δ) (k : ℕ) (a : ℤ)
    (ha : δ * (algebraMap ℤ (Localization.Away Δ) Δ)^k =
      algebraMap ℤ (Localization.Away Δ) a)
    (p : ℕ) (hp : p.Prime) (hpΔ : ¬ p ∣ Δ.natAbs) (hpa : ¬ p ∣ a.natAbs) :
    IsUnit (awayIntToZMod Δ p hp hpΔ δ) := by
  letI : Fact p.Prime := ⟨hp⟩
  apply isUnit_iff_ne_zero.mpr
  intro hzero
  have he := congrArg (awayIntToZMod Δ p hp hpΔ) ha
  simp only [map_mul, map_pow, awayIntToZMod_algebraMap, hzero, zero_mul] at he
  exact intCast_zmod_ne_zero_of_not_dvd_natAbs a p hpa he.symm

/-- A single positive natural exceptional integer, divisible by |Δ|,
makes every permitted specialization a unit. No specialized unit premise
or numerator is supplied to this endpoint. -/
theorem exists_uniform_unit_exception
    (Δ : ℤ) (hΔ : Δ ≠ 0) (δ : Localization.Away Δ) (hδ : δ ≠ 0) :
    ∃ D : ℕ, 1 ≤ D ∧ Δ.natAbs ∣ D ∧
      ∀ (p : ℕ) (hp : p.Prime), ¬ p ∣ D →
        ∀ hpΔ : ¬ p ∣ Δ.natAbs, IsUnit (awayIntToZMod Δ p hp hpΔ δ) := by
  obtain ⟨k, a, ha0, ha⟩ := exists_nonzero_numerator Δ δ hδ
  refine ⟨Δ.natAbs * a.natAbs, ?_, dvd_mul_right _ _, ?_⟩
  · exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero
      (Int.natAbs_ne_zero.mpr hΔ) (Int.natAbs_ne_zero.mpr ha0))
  · intro p hp hpD hpΔ
    apply isUnit_specialization_of_numerator Δ δ k a ha p hp hpΔ
    intro hpa
    exact hpD (dvd_mul_of_dvd_right hpa _)

/-- The denominator-avoidance proof and unit specialization are both
derived from one exceptional integer chosen before every prime. -/
theorem exists_exceptionalInteger
    (Δ : ℤ) (hΔ : Δ ≠ 0) (δ : Localization.Away Δ) (hδ : δ ≠ 0) :
    ∃ D : ℕ, 1 ≤ D ∧ Δ.natAbs ∣ D ∧
      ∀ (p : ℕ) (hp : p.Prime), ¬ p ∣ D →
        ∃ hpΔ : ¬ p ∣ Δ.natAbs, IsUnit (awayIntToZMod Δ p hp hpΔ δ) := by
  obtain ⟨D, hD, hΔD, hunit⟩ := exists_uniform_unit_exception Δ hΔ δ hδ
  refine ⟨D, hD, hΔD, ?_⟩
  intro p hp hpD
  have hpΔ : ¬ p ∣ Δ.natAbs := fun h => hpD (h.trans hΔD)
  exact ⟨hpΔ, hunit p hp hpD hpΔ⟩

end CubicTenVariables.LocalizedIntegerExceptionalSet
