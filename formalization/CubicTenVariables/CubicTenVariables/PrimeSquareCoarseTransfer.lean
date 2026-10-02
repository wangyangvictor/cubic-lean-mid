import CubicTenVariables.CompleteSumFrequencyTail

/-! Finite exceptional-prime absorption for the actual ten-variable
prime-square complete sum. The good-prime estimate is an explicit hypothesis;
this adapter does not prove that arithmetic estimate. At a prime dividing the
fixed positive integer D, the all-modulus trivial bound p^22 is absorbed using
p ≤ D. No homogeneity or literature input is needed. -/

set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.PrimeSquareCoarseTransfer
open MvPolynomial

/-- A fixed exceptional integer is absorbed into an explicit constant,
uniformly in every prime and integer frequency. -/
theorem all_primes_bound (F : MvPolynomial (Fin 10) ℤ) (D : ℕ) (hD : 1 ≤ D)
    (C₀ : ℝ)
    (hgood : ∀ (p : ℕ) [Fact p.Prime], ¬ p ∣ D → ∀ v : Fin 10 → ℤ,
      ‖completeCubicSum F (p^2) v‖ ≤ C₀ * (p : ℝ)^17)
    (p : ℕ) [hp : Fact p.Prime] (v : Fin 10 → ℤ) :
    ‖completeCubicSum F (p^2) v‖ ≤ max C₀ ((D : ℝ)^5) * (p : ℝ)^17 := by
  by_cases hbad : p ∣ D
  · have hpD : p ≤ D := Nat.le_of_dvd (by omega) hbad
    have hpDr : (p : ℝ) ≤ D := by exact_mod_cast hpD
    have hpow : (p : ℝ)^5 ≤ (D : ℝ)^5 :=
      pow_le_pow_left₀ (by positivity) hpDr 5
    have hp1 : 1 ≤ p := hp.out.one_lt.le
    calc
      ‖completeCubicSum F (p^2) v‖ ≤ ((p^2 : ℕ) : ℝ)^11 :=
        CompleteSumFrequencyTail.trivial_bound F (p^2) (by nlinarith) v
      _ = (p : ℝ)^5 * (p : ℝ)^17 := by push_cast; ring
      _ ≤ (D : ℝ)^5 * (p : ℝ)^17 :=
        mul_le_mul_of_nonneg_right hpow (by positivity)
      _ ≤ max C₀ ((D : ℝ)^5) * (p : ℝ)^17 :=
        mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)
  · exact (hgood p hbad v).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))

/-- The constant is chosen before all primes and frequencies. The only
analytic or arithmetic premise is the displayed good-prime bound. -/
theorem exists_bound (F : MvPolynomial (Fin 10) ℤ) (D : ℕ) (hD : 1 ≤ D)
    (C₀ : ℝ) (hC₀ : 1 ≤ C₀)
    (hgood : ∀ (p : ℕ) [Fact p.Prime], ¬ p ∣ D → ∀ v : Fin 10 → ℤ,
      ‖completeCubicSum F (p^2) v‖ ≤ C₀ * (p : ℝ)^17) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (p : ℕ) [Fact p.Prime] (v : Fin 10 → ℤ),
      ‖completeCubicSum F (p^2) v‖ ≤ C * (p : ℝ)^17 := by
  exact ⟨max C₀ ((D : ℝ)^5), hC₀.trans (le_max_left _ _),
    fun p _ v => all_primes_bound F D hD C₀ hgood p v⟩

end CubicTenVariables.PrimeSquareCoarseTransfer
