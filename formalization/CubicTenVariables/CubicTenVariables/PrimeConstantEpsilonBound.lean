import CubicTenVariables.PrimeFactorEpsilonBound

/-! Epsilon absorption for a fixed real constant at each distinct prime
factor. Rounding the constant up reduces this to the proved natural-weight
estimate. Constants precede all positive integers; m=1 and overlapping
prime supports in the two-factor estimate are included. -/

set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.PrimeConstantEpsilonBound
open scoped BigOperators

/-- A fixed real weight per distinct prime factor is bounded by m^epsilon,
with a constant independent of the positive integer m. -/
theorem exists_bound (C : ℝ) (hC : 1 ≤ C) (ε : ℝ) (hε : 0 < ε) :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ m : ℕ, 1 ≤ m →
      C^(m.primeFactors.card) ≤ A*(m : ℝ)^ε := by
  classical
  let K : ℕ := ⌈C⌉₊
  have hCK : C ≤ (K : ℝ) := Nat.le_ceil C
  have hK : 1 ≤ K := by exact_mod_cast hC.trans hCK
  obtain ⟨A,hA,hbound⟩ :=
    PrimeFactorEpsilonBound.exists_uniform_prime_factor_bound K hK ε hε
  refine ⟨A,hA,?_⟩
  intro m hm
  have hm0 : m ≠ 0 := by omega
  have hprod : K^(m.primeFactors.card) ≤
      ∏ p ∈ m.primeFactors, K*m.factorization p := by
    rw [← Finset.prod_const]
    apply Finset.prod_le_prod'
    intro p hp
    have hν : 1 ≤ m.factorization p :=
      (Nat.prime_of_mem_primeFactors hp).factorization_pos_of_dvd hm0
        (Nat.dvd_of_mem_primeFactors hp)
    nlinarith
  calc
    C^(m.primeFactors.card) ≤ (K : ℝ)^(m.primeFactors.card) :=
      pow_le_pow_left₀ (zero_le_one.trans hC) hCK _
    _ ≤ ((∏ p ∈ m.primeFactors, K*m.factorization p : ℕ) : ℝ) := by
      exact_mod_cast hprod
    _ ≤ A*(m : ℝ)^ε := hbound m hm

/-- No coprimality is required: a common prime may occur once in each
factor's weight. The constant is chosen before both positive integers. -/
theorem exists_two_factor_bound (C : ℝ) (hC : 1 ≤ C) (ε : ℝ) (hε : 0 < ε) :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ a b : ℕ, 1 ≤ a → 1 ≤ b →
      C^(a.primeFactors.card+b.primeFactors.card) ≤ A*((a*b : ℕ) : ℝ)^ε := by
  obtain ⟨A,hA,hbound⟩ := exists_bound C hC ε hε
  refine ⟨A^2,one_le_pow₀ hA,?_⟩
  intro a b ha hb
  calc
    C^(a.primeFactors.card+b.primeFactors.card) =
        C^(a.primeFactors.card)*C^(b.primeFactors.card) := pow_add _ _ _
    _ ≤ (A*(a : ℝ)^ε)*(A*(b : ℝ)^ε) :=
      mul_le_mul (hbound a ha) (hbound b hb)
        (pow_nonneg (zero_le_one.trans hC) _) (by positivity)
    _ = A^2*((a*b : ℕ) : ℝ)^ε := by
      rw [Nat.cast_mul,Real.mul_rpow (Nat.cast_nonneg a) (Nat.cast_nonneg b)]
      ring

end CubicTenVariables.PrimeConstantEpsilonBound
