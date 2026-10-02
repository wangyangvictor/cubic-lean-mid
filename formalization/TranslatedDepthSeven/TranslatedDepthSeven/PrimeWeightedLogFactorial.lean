import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Data.Nat.Cast.Order.Field
import Mathlib.Analysis.SpecialFunctions.Stirling

/-! The first elementary Mertens step. The exact logarithmic factorial
identity uses mathlib's finite Dirichlet-convolution summation formula;
rounding the integer quotients costs at most the actual Chebyshev function.
No asymptotic prime theorem or new literature proposition is assumed. -/

namespace TranslatedDepthSeven.PrimeWeightedLogFactorial
noncomputable section
open Finset
open scoped BigOperators

private theorem Ioc_zero_eq_Icc_one (N : ℕ) :
    Finset.Ioc 0 N = Finset.Icc 1 N := by
  ext n
  simp only [Finset.mem_Ioc, Finset.mem_Icc]
  omega

/-- The logarithm of the literal natural factorial is the finite logarithm
sum, including the empty sum at zero. -/
theorem log_factorial_eq_sum_log (N : ℕ) :
    Real.log (N.factorial : ℝ) =
      ∑ n ∈ Finset.Icc 1 N, Real.log (n : ℝ) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Nat.factorial_succ, Nat.cast_mul,
      Real.log_mul (by positivity) (by positivity), ih,
      Finset.sum_Icc_succ_top (by omega)]
    ring

/-- Exact finite identity with natural-number division; no error term and
no primality or size condition are needed. -/
theorem log_factorial_eq_sum_vonMangoldt_div (N : ℕ) :
    Real.log (N.factorial : ℝ) =
      ∑ n ∈ Finset.Icc 1 N,
        ArithmeticFunction.vonMangoldt n * ((N / n : ℕ) : ℝ) := by
  rw [log_factorial_eq_sum_log]
  have h := ArithmeticFunction.sum_Ioc_mul_zeta_eq_sum
    (R := ℝ) ArithmeticFunction.vonMangoldt N
  rw [ArithmeticFunction.vonMangoldt_mul_zeta, Ioc_zero_eq_Icc_one] at h
  simpa only [ArithmeticFunction.log_apply] using h

/-- The unnormalized floor error is nonnegative and at most psi(N). -/
theorem weighted_vonMangoldt_floor_error (N : ℕ) :
    0 ≤ (N : ℝ) * (∑ n ∈ Finset.Icc 1 N,
      ArithmeticFunction.vonMangoldt n / (n : ℝ)) - Real.log (N.factorial : ℝ) ∧
    (N : ℝ) * (∑ n ∈ Finset.Icc 1 N,
      ArithmeticFunction.vonMangoldt n / (n : ℝ)) - Real.log (N.factorial : ℝ) ≤
        Chebyshev.psi (N : ℝ) := by
  let E : ℕ → ℝ := fun n => ArithmeticFunction.vonMangoldt n *
    ((N : ℝ) / (n : ℝ) - ((N / n : ℕ) : ℝ))
  have heq : (N : ℝ) * (∑ n ∈ Finset.Icc 1 N,
      ArithmeticFunction.vonMangoldt n / (n : ℝ)) - Real.log (N.factorial : ℝ) =
        ∑ n ∈ Finset.Icc 1 N, E n := by
    rw [log_factorial_eq_sum_vonMangoldt_div, Finset.mul_sum,
      ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro n _hn
    dsimp [E]
    ring
  have hnonneg (n : ℕ) : 0 ≤ E n := by
    apply mul_nonneg ArithmeticFunction.vonMangoldt_nonneg
    exact sub_nonneg.mpr Nat.cast_div_le
  have hupper (n : ℕ) (hn : n ∈ Finset.Icc 1 N) :
      E n ≤ ArithmeticFunction.vonMangoldt n := by
    have hnpos : 0 < n := (Finset.mem_Icc.mp hn).1
    have hnR : (0 : ℝ) < n := by exact_mod_cast hnpos
    have hquot : (N : ℝ) / (n : ℝ) < ((N / n : ℕ) : ℝ) + 1 := by
      apply (div_lt_iff₀ hnR).2
      have h := Nat.lt_mul_div_succ N hnpos
      have hR : (N : ℝ) < (n : ℝ) * (((N / n : ℕ) : ℝ) + 1) := by
        exact_mod_cast h
      nlinarith
    have hdiff : (N : ℝ) / (n : ℝ) - ((N / n : ℕ) : ℝ) ≤ 1 := by linarith
    simpa only [mul_one] using
      mul_le_mul_of_nonneg_left hdiff ArithmeticFunction.vonMangoldt_nonneg
  rw [heq]
  refine ⟨Finset.sum_nonneg (fun n _hn => hnonneg n), ?_⟩
  have hpsi : Chebyshev.psi (N : ℝ) =
      ∑ n ∈ Finset.Icc 1 N, ArithmeticFunction.vonMangoldt n := by
    simp only [Chebyshev.psi, Nat.floor_natCast, Ioc_zero_eq_Icc_one]
  rw [hpsi]
  exact Finset.sum_le_sum hupper

/-- Chebyshev's already-proved elementary upper estimate gives a fixed
constant in the logarithmic-factorial comparison. -/
theorem weighted_vonMangoldt_floor_error_le_linear (N : ℕ) :
    (N : ℝ) * (∑ n ∈ Finset.Icc 1 N,
      ArithmeticFunction.vonMangoldt n / (n : ℝ)) - Real.log (N.factorial : ℝ) ≤
        (Real.log 4 + 4) * (N : ℝ) :=
  (weighted_vonMangoldt_floor_error N).2.trans
    (Chebyshev.psi_le_const_mul_self (Nat.cast_nonneg N))

/-- Division by N leaves an absolute bounded error. This is the direct
input for the elementary prime-weighted logarithmic estimate. -/
theorem abs_weighted_vonMangoldt_sub_log_factorial_div_le
    (N : ℕ) (hN : 0 < N) :
    |(∑ n ∈ Finset.Icc 1 N, ArithmeticFunction.vonMangoldt n / (n : ℝ)) -
      Real.log (N.factorial : ℝ) / (N : ℝ)| ≤ Real.log 4 + 4 := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have heq : (∑ n ∈ Finset.Icc 1 N, ArithmeticFunction.vonMangoldt n / (n : ℝ)) -
      Real.log (N.factorial : ℝ) / (N : ℝ) =
        ((N : ℝ) * (∑ n ∈ Finset.Icc 1 N,
          ArithmeticFunction.vonMangoldt n / (n : ℝ)) - Real.log (N.factorial : ℝ)) /
          (N : ℝ) := by
    field_simp
  rw [heq, abs_of_nonneg (div_nonneg (weighted_vonMangoldt_floor_error N).1 hNR.le)]
  exact (div_le_iff₀ hNR).2 (weighted_vonMangoldt_floor_error_le_linear N)

/-- Elementary factorial bounds place the normalized logarithm between
log N minus one and log N. The lower bound uses mathlib's Stirling estimate. -/
theorem log_factorial_div_bounds (N : ℕ) (hN : 0 < N) :
    Real.log (N : ℝ) - 1 ≤ Real.log (N.factorial : ℝ) / (N : ℝ) ∧
      Real.log (N.factorial : ℝ) / (N : ℝ) ≤ Real.log (N : ℝ) := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hlogN : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by exact_mod_cast hN)
  have hlogpi : 0 ≤ Real.log (2 * Real.pi) :=
    Real.log_nonneg (by linarith [Real.two_le_pi])
  constructor
  · apply (le_div_iff₀ hNR).2
    have h := Stirling.le_log_factorial_stirling hN.ne'
    nlinarith
  · apply (div_le_iff₀ hNR).2
    have hfact : (N.factorial : ℝ) ≤ (N : ℝ) ^ N := by
      exact_mod_cast Nat.factorial_le_pow N
    have h := Real.log_le_log (by positivity) hfact
    rw [Real.log_pow] at h
    nlinarith

/-- Sharp leading coefficient one for the weighted von Mangoldt sum.
Removing higher prime powers is a separate finite-sum step. -/
theorem abs_weighted_vonMangoldt_sub_log_le (N : ℕ) (hN : 0 < N) :
    |(∑ n ∈ Finset.Icc 1 N, ArithmeticFunction.vonMangoldt n / (n : ℝ)) -
      Real.log (N : ℝ)| ≤ Real.log 4 + 5 := by
  let S : ℝ := ∑ n ∈ Finset.Icc 1 N, ArithmeticFunction.vonMangoldt n / (n : ℝ)
  let A : ℝ := Real.log (N.factorial : ℝ) / (N : ℝ)
  have hSA : |S - A| ≤ Real.log 4 + 4 :=
    abs_weighted_vonMangoldt_sub_log_factorial_div_le N hN
  have hA : |A - Real.log (N : ℝ)| ≤ 1 := by
    obtain ⟨hlo, hhi⟩ := log_factorial_div_bounds N hN
    apply abs_le.mpr
    dsimp [A]
    constructor <;> linarith
  calc
    _ = |(S - A) + (A - Real.log (N : ℝ))| := by dsimp [S]; congr 1; ring
    _ ≤ |S - A| + |A - Real.log (N : ℝ)| := abs_add_le _ _
    _ ≤ _ := by linarith

end
end TranslatedDepthSeven.PrimeWeightedLogFactorial
