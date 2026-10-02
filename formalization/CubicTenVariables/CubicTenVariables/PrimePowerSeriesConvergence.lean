import CubicTenVariables.ExponentialSums
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Normed.Ring.InfiniteSum

/-! The elementary higher-prime-power convergence step for the singular series.
The exponential-sum estimate remains an explicit hypothesis. These proofs use
neither Bernert's convergence theorem nor any root-count bound derived from it.
-/

set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.PrimePowerSeriesConvergence
open scoped BigOperators

/-- For `α > 1/2`, the sum over all primes and all exponents at least two
of `(p^k)^(-α)` converges. The constant in an application must be uniform
in both the prime and the exponent. -/
theorem summable_prime_power_rpow {α : ℝ} (hα : 1 / 2 < α) :
    Summable (fun pk : Nat.Primes × ℕ =>
      ((pk.1.val : ℝ) ^ (pk.2 + 2)) ^ (-α)) := by
  have hαpos : 0 < α := by linarith
  have hpseries : Summable (fun p : Nat.Primes => (p.val : ℝ) ^ (-2 * α)) :=
    (Real.summable_nat_rpow.mpr (by linarith)).comp_injective Subtype.val_injective
  have hgeom : Summable (fun k : ℕ => ((2 : ℝ) ^ (-α)) ^ k) :=
    summable_geometric_of_lt_one (Real.rpow_nonneg (by norm_num) _)
      (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith))
  have hmajorant := hpseries.mul_of_nonneg hgeom
    (fun p => Real.rpow_nonneg (Nat.cast_nonneg _) _)
    (fun k => pow_nonneg (Real.rpow_nonneg (by norm_num) _) _)
  apply Summable.of_nonneg_of_le (fun _ => Real.rpow_nonneg (by positivity) _)
    (fun pk => ?_) hmajorant
  obtain ⟨p,k⟩ := pk
  have hp : (2 : ℝ) ≤ p.val := by exact_mod_cast p.property.two_le
  have hp0 : (0 : ℝ) < p.val := lt_of_lt_of_le (by norm_num) hp
  have heq : ((p.val : ℝ) ^ (k+2)) ^ (-α) =
      (p.val : ℝ) ^ (-2*α) * ((p.val : ℝ) ^ (-α)) ^ k := by
    rw [← Real.rpow_natCast_mul hp0.le,
      show ((k+2 : ℕ) : ℝ) * (-α) = -2*α + (-α)*(k : ℝ) by push_cast; ring,
      Real.rpow_add hp0, Real.rpow_mul_natCast hp0.le]
  rw [heq]
  exact mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (Real.rpow_nonneg hp0.le _) 
      (Real.rpow_le_rpow_of_nonpos (by norm_num) hp (by linarith)) _)
    (Real.rpow_nonneg hp0.le _)

/-- Uniform decay above the half-power threshold suffices for the higher
prime-power part of any complex series. This asserts no bound at primes. -/
theorem summable_higher_prime_powers {A : ℕ → ℂ} {C α : ℝ}
    (hα : 1 / 2 < α)
    (hbound : ∀ (p : ℕ), p.Prime → ∀ k : ℕ, 2 ≤ k →
      ‖A (p^k)‖ ≤ C * ((p : ℝ)^k)^(-α)) :
    Summable (fun pk : Nat.Primes × ℕ => ‖A (pk.1.val ^ (pk.2+2))‖) := by
  exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun pk => hbound pk.1.val pk.1.property (pk.2+2) (by omega))
    ((summable_prime_power_rpow hα).mul_left C)

/-- Division by the exact normalization `q^n` converts the complete-sum
estimate into the decay exponent used for the singular series. -/
theorem normalized_bound {n q : ℕ} (F : MvPolynomial (Fin n) ℤ)
    (hq : 0 < q) {C β : ℝ}
    (hbound : ‖completeCubicSum F q 0‖ ≤ C * (q : ℝ)^β) :
    ‖singularSeriesTerm F q‖ ≤ C * (q : ℝ)^(β-(n : ℝ)) := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  rw [singularSeriesTerm, if_neg (Nat.ne_of_gt hq), norm_div, norm_pow]
  simp only [Complex.norm_natCast]
  calc
    ‖completeCubicSum F q 0‖ / (q : ℝ)^n ≤
        (C * (q : ℝ)^β) / (q : ℝ)^n :=
      div_le_div_of_nonneg_right hbound (pow_nonneg hq0.le _)
    _ = C * (q : ℝ)^(β-(n : ℝ)) := by
      rw [Real.rpow_sub hq0, Real.rpow_natCast]
      ring

/-- The `q^(1+5n/6+ε)` complete-sum bound suffices for all exponents
at least two when `n ≥ 10` and `ε < 1/6`. Positivity of the singular
series and convergence over prime moduli are separate obligations. -/
theorem cubic_higher_prime_powers {n : ℕ} (F : MvPolynomial (Fin n) ℤ)
    (hn : 10 ≤ n) {C ε : ℝ} (hε : ε < 1 / 6)
    (hbound : ∀ (p : ℕ), p.Prime → ∀ k : ℕ, 2 ≤ k →
      ‖completeCubicSum F (p^k) 0‖ ≤
        C * ((p^k : ℕ) : ℝ)^(1 + 5*(n : ℝ)/6 + ε)) :
    Summable (fun pk : Nat.Primes × ℕ =>
      ‖singularSeriesTerm F (pk.1.val ^ (pk.2+2))‖) := by
  have hn' : (10 : ℝ) ≤ n := by exact_mod_cast hn
  apply summable_higher_prime_powers (α := (n : ℝ)/6 - 1 - ε) (C := C)
    (by linarith)
  intro p hp k hk
  have h := normalized_bound F (pow_pos hp.pos k) (hbound p hp k hk)
  convert h using 1
  push_cast
  congr 2
  ring

end CubicTenVariables.PrimePowerSeriesConvergence
