import Mathlib.Data.ZMod.Coprime
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.MvPolynomial.Ideal

/-!
# Reduction of a principal-open integral model

If a prime `p` does not divide an integer `Δ`, reduction modulo `p` extends
canonically from `ℤ` to `ℤ[1/Δ]`.  Mapping an ideal first to that principal
localization and then to `ZMod p` is exactly the same as reducing the
original ideal directly modulo `p`.

The last theorem gives the coefficientwise multivariate-polynomial form
used for explicit projective and affine models.  It is an equality of
literal ideals, not a comparison of their zero loci.
-/

namespace TranslatedDepthSeven

noncomputable section

universe u

/-- The cast of `Δ` in `ZMod p` is nonzero when `p ∤ Δ.natAbs`. -/
theorem intCast_zmod_ne_zero_of_not_dvd_natAbs
    (Δ : ℤ) (p : ℕ) (hpΔ : ¬ p ∣ Δ.natAbs) :
    (Δ : ZMod p) ≠ 0 := by
  rw [ne_eq, ZMod.intCast_zmod_eq_zero_iff_dvd]
  intro hdiv
  apply hpΔ
  obtain ⟨z, hz⟩ := hdiv
  refine ⟨z.natAbs, ?_⟩
  rw [hz, Int.natAbs_mul, Int.natAbs_natCast]

/-- Reduction modulo a prime away from a denominator not divisible by that
prime. -/
noncomputable def awayIntToZMod
    (Δ : ℤ) (p : ℕ) (hp : p.Prime) (hpΔ : ¬ p ∣ Δ.natAbs) :
    Localization.Away Δ →+* ZMod p := by
  have hunit : IsUnit ((Int.castRingHom (ZMod p)) Δ) :=
    (ZMod.coe_int_isUnit_iff_isCoprime Δ p).mpr <| by
      rw [(Nat.prime_iff_prime_int.mp hp).coprime_iff_not_dvd]
      intro hdiv
      apply hpΔ
      obtain ⟨z, hz⟩ := hdiv
      refine ⟨z.natAbs, ?_⟩
      rw [hz, Int.natAbs_mul, Int.natAbs_natCast]
  exact IsLocalization.Away.lift
    (S := Localization.Away Δ) (g := Int.castRingHom (ZMod p)) Δ hunit

@[simp]
theorem awayIntToZMod_algebraMap
    (Δ : ℤ) (p : ℕ) (hp : p.Prime) (hpΔ : ¬ p ∣ Δ.natAbs)
    (z : ℤ) :
    awayIntToZMod Δ p hp hpΔ
        (algebraMap ℤ (Localization.Away Δ) z) =
      (z : ZMod p) := by
  have hunit : IsUnit ((Int.castRingHom (ZMod p)) Δ) :=
    (ZMod.coe_int_isUnit_iff_isCoprime Δ p).mpr <| by
      rw [(Nat.prime_iff_prime_int.mp hp).coprime_iff_not_dvd]
      intro hdiv
      apply hpΔ
      obtain ⟨z', hz'⟩ := hdiv
      refine ⟨z'.natAbs, ?_⟩
      rw [hz', Int.natAbs_mul, Int.natAbs_natCast]
  simpa only [awayIntToZMod] using
    (IsLocalization.Away.lift_eq
      (S := Localization.Away Δ) (g := Int.castRingHom (ZMod p))
      Δ hunit z)

/-- Extension to the principal localization and subsequent reduction is
direct reduction on ideals of `ℤ`. -/
theorem map_localized_intIdeal_to_ZMod
    (Δ : ℤ) (p : ℕ) (hp : p.Prime) (hpΔ : ¬ p ∣ Δ.natAbs)
    (I : Ideal ℤ) :
    Ideal.map (awayIntToZMod Δ p hp hpΔ)
        (Ideal.map (algebraMap ℤ (Localization.Away Δ)) I) =
      Ideal.map (Int.castRingHom (ZMod p)) I := by
  rw [Ideal.map_map]
  congr 1
  exact RingHom.ext_int _ _

/-- Polynomial form of `map_localized_intIdeal_to_ZMod`: an explicit
principal-open polynomial model has exactly the canonical direct reduction
away from the denominator. -/
theorem map_localized_mvPolynomialIdeal_to_ZMod
    {σ : Type u}
    (Δ : ℤ) (p : ℕ) (hp : p.Prime) (hpΔ : ¬ p ∣ Δ.natAbs)
    (I : Ideal (MvPolynomial σ ℤ)) :
    Ideal.map (MvPolynomial.map (awayIntToZMod Δ p hp hpΔ))
        (Ideal.map
          (MvPolynomial.map (algebraMap ℤ (Localization.Away Δ))) I) =
      Ideal.map (MvPolynomial.map (Int.castRingHom (ZMod p))) I := by
  rw [Ideal.map_map]
  congr 1
  apply MvPolynomial.ringHom_ext
  · intro z
    simp
  · intro i
    simp

end

end TranslatedDepthSeven
