import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic

/-! Exact finite products used to assemble the composite residue estimate. -/

namespace CubicTenVariables.CompositeResidueProducts

open scoped BigOperators

/-- A prime dividing a positive divisor belongs to the larger prime set. -/
theorem primeFactors_subset_of_dvd {m c : ℕ} (hc : c ≠ 0) (hmc : m ∣ c) :
    m.primeFactors ⊆ c.primeFactors := by
  intro p hp
  exact Nat.mem_primeFactors.mpr
    ⟨(Nat.mem_primeFactors.mp hp).1, (Nat.dvd_of_mem_primeFactors hp).trans hmc, hc⟩

/-- Extending the product of prime powers by zero exponents leaves it unchanged. -/
theorem prod_prime_power_over_multiple {m c : ℕ}
    (hm : m ≠ 0) (hc : c ≠ 0) (hmc : m ∣ c) (a : ℕ) :
    (∏ p ∈ c.primeFactors, p^(a * m.factorization p)) = m^a := by
  have he : (∏ p ∈ m.primeFactors, p^(a*m.factorization p)) =
      ∏ p ∈ c.primeFactors, p^(a*m.factorization p) := by
    apply Finset.prod_subset (primeFactors_subset_of_dvd hc hmc)
    intro p hp hpm
    have hz : m.factorization p = 0 := by
      apply Nat.factorization_eq_zero_of_not_dvd
      intro hd
      exact hpm (Nat.mem_primeFactors.mpr ⟨(Nat.mem_primeFactors.mp hp).1, hd, hm⟩)
    simp [hz]
  rw [← he]
  simp_rw [Nat.mul_comm a, pow_mul]
  rw [Finset.prod_pow]
  congr 1
  simpa only [Nat.prod_factorization_eq_prod_primeFactors] using
    Nat.factorization_prod_pow_eq_self hm

/-- Local constants occur only at primes that divide the positive quotient. -/
theorem prod_local_overhead {K m c : ℕ}
    (hm : m ≠ 0) (hc : c ≠ 0) (hmc : m ∣ c) :
    (∏ p ∈ c.primeFactors, if m.factorization p = 0 then 1 else K*m.factorization p) =
      ∏ p ∈ m.primeFactors, K*m.factorization p := by
  have he : (∏ p ∈ m.primeFactors,
      if m.factorization p = 0 then 1 else K*m.factorization p) =
      ∏ p ∈ c.primeFactors,
      if m.factorization p = 0 then 1 else K*m.factorization p := by
    apply Finset.prod_subset (primeFactors_subset_of_dvd hc hmc)
    intro p hp hpm
    have hz : m.factorization p = 0 := by
      apply Nat.factorization_eq_zero_of_not_dvd
      intro hd
      exact hpm (Nat.mem_primeFactors.mpr ⟨(Nat.mem_primeFactors.mp hp).1, hd, hm⟩)
    simp [hz]
  rw [← he]
  apply Finset.prod_congr rfl
  intro p hp
  have hpos := (Nat.mem_primeFactors.mp hp).1.factorization_pos_of_dvd hm
    (Nat.dvd_of_mem_primeFactors hp)
  simp [Nat.ne_of_gt hpos]

/-- A divisor condition restricts a product to exactly the smaller prime set. -/
theorem prod_prime_divisor_filter {M : Type*} [CommMonoid M]
    {e c : ℕ} (he : e ≠ 0) (hc : c ≠ 0) (hec : e ∣ c) (f : ℕ → M) :
    (∏ p ∈ c.primeFactors, if p ∣ e then f p else 1) =
      ∏ p ∈ e.primeFactors, f p := by
  rw [← Finset.prod_filter]
  congr 1
  ext p
  simp only [Finset.mem_filter, Nat.mem_primeFactors]
  constructor
  · rintro ⟨⟨hp, _, _⟩, hpe⟩
    exact ⟨hp, hpe, he⟩
  · rintro ⟨hp,hpe,_⟩
    exact ⟨⟨hp,hpe.trans hec,hc⟩,hpe⟩

/-- Exact assembly of the numerical factors in the local inequalities.
The quotient m, not the ambient modulus c, indexes the local constants. -/
theorem prod_le_of_local_bounds {K m c e : ℕ}
    (hm : m ≠ 0) (hc : c ≠ 0) (he : e ≠ 0) (hmc : m ∣ c) (hec : e ∣ c)
    (f G H : ℕ → ℕ)
    (hlocal : ∀ p ∈ c.primeFactors,
      f p ≤ (if m.factorization p = 0 then 1 else K*m.factorization p) *
        p^(9*m.factorization p) * (if p ∣ e then G p * H p else 1)) :
    (∏ p ∈ c.primeFactors, f p) ≤
      m^9 * (∏ p ∈ e.primeFactors, G p) * (∏ p ∈ e.primeFactors, H p) *
        (∏ p ∈ m.primeFactors, K*m.factorization p) := by
  calc
    _ ≤ ∏ p ∈ c.primeFactors,
        (if m.factorization p = 0 then 1 else K*m.factorization p) *
          p^(9*m.factorization p) * (if p ∣ e then G p * H p else 1) :=
      Finset.prod_le_prod' (fun p hp => hlocal p hp)
    _ = _ := by
      simp only [Finset.prod_mul_distrib]
      rw [prod_local_overhead hm hc hmc, prod_prime_power_over_multiple hm hc hmc,
        prod_prime_divisor_filter he hc hec]
      simp only [Finset.prod_mul_distrib]
      ring

end CubicTenVariables.CompositeResidueProducts
