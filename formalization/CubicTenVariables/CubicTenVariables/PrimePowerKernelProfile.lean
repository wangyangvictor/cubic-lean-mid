import CubicTenVariables.SmithKernelFormula
import CubicTenVariables.SmithProfileMultiplicity
import Mathlib.Data.Nat.Factorization.Basic

/-!
Canonical truncated prime valuations of actual integral diagonal entries.
Zero entries receive valuation t at level p^t. The resulting monotone
cumulative profile has the exact exponent in the literal modular kernel.
-/

noncomputable section
namespace CubicTenVariables.PrimePowerKernelProfile

open scoped BigOperators

/-- The actual prime valuation truncated at the modulus exponent, including zero. -/
def truncatedValuation (p t : ℕ) (d : ℤ) : ℕ :=
  if d = 0 then t else min (d.natAbs.factorization p) t

theorem truncatedValuation_le (p t : ℕ) (d : ℤ) :
    truncatedValuation p t d ≤ t := by
  unfold truncatedValuation
  split_ifs
  · exact le_rfl
  · exact min_le_right _ _

/-- Gcd with a prime power is the corresponding truncated valuation power. -/
theorem gcd_primePower (p t : ℕ) (hp : p.Prime) (d : ℤ) :
    Nat.gcd d.natAbs (p ^ t) = p ^ truncatedValuation p t d := by
  by_cases hd : d = 0
  · simp [hd, truncatedValuation]
  · have ha : d.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hd
    rw [truncatedValuation, if_neg hd]
    apply Nat.dvd_antisymm
    · obtain ⟨k, hkt, hk⟩ := (Nat.dvd_prime_pow hp).mp (Nat.gcd_dvd_right d.natAbs (p ^ t))
      have hka : p ^ k ∣ d.natAbs := hk ▸ Nat.gcd_dvd_left d.natAbs (p ^ t)
      have hkv := (hp.pow_dvd_iff_le_factorization ha).mp hka
      rw [hk]
      exact pow_dvd_pow p (le_min hkv hkt)
    · exact Nat.dvd_gcd
        ((hp.pow_dvd_iff_le_factorization ha).mpr (min_le_left _ _))
        (pow_dvd_pow p (min_le_right _ _))

/-- Literal cardinality for any integer diagonal, with actual truncated valuations. -/
theorem card_diagonal_primePower {n : ℕ} (p t : ℕ) (hp : p.Prime)
    (d : Fin n → ℤ) :
    Nat.card {x : Fin n → ZMod (p ^ t) //
      ((Matrix.diagonal d).map (Int.castRingHom (ZMod (p ^ t)))).mulVec x = 0} =
      p ^ (∑ i, truncatedValuation p t (d i)) := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  rw [ModularKernelCardinality.card_map_diagonal_int_kernel]
  simp only [gcd_primePower p t hp]
  exact Finset.prod_pow_eq_pow_sum Finset.univ _ p

/-- The profile belongs to the actual entries; its weighted complement is
exactly the kernel exponent, including zero entries and modulus one. -/
theorem card_diagonal_primePower_profile {n : ℕ} (p t : ℕ) (hp : p.Prime)
    (d : Fin n → ℤ) :
    Nat.card {x : Fin n → ZMod (p ^ t) //
      ((Matrix.diagonal d).map (Int.castRingHom (ZMod (p ^ t)))).mulVec x = 0} =
      p ^ (n * t - ∑ i ∈ Finset.range t,
        SmithProfileMultiplicity.profile (fun ν => truncatedValuation p t (d ν)) i) := by
  rw [card_diagonal_primePower p t hp]
  congr 1
  have h := SmithProfileMultiplicity.sum_min_eq_sub_sum_profile
    (fun ν => truncatedValuation p t (d ν)) t
  simpa only [Nat.min_eq_left (truncatedValuation_le p t _)] using h

/-- Every actual integer matrix admits one integral diagonal whose literal
truncated prime-valuation profiles give the exact kernel size at every prime
power. The diagonal is chosen before p and t; no normal form is an input. -/
theorem exists_integer_kernel_profiles {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) :
    ∃ d : Fin n → ℤ, ∀ (p : ℕ), p.Prime → ∀ t : ℕ,
      Nat.card {x : Fin n → ZMod (p ^ t) //
        (B.map (Int.castRingHom (ZMod (p ^ t)))).mulVec x = 0} =
        p ^ (n * t - ∑ i ∈ Finset.range t,
          SmithProfileMultiplicity.profile (fun ν => truncatedValuation p t (d ν)) i) := by
  obtain ⟨d, hd⟩ := SmithKernelFormula.exists_kernel_formula B
  refine ⟨d, ?_⟩
  intro p hp t
  letI : NeZero p := ⟨hp.ne_zero⟩
  rw [hd (p ^ t) (pow_pos hp.pos t)]
  rw [← ModularKernelCardinality.card_map_diagonal_int_kernel (p ^ t) d]
  exact card_diagonal_primePower_profile p t hp d

end CubicTenVariables.PrimePowerKernelProfile
