import Mathlib.NumberTheory.Chebyshev
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.BigOperators.Field

/-! Quantitative deletion of the primes dividing an actual nonzero integer
certificate. The loss is bounded by log D / L for primes at least L.
These finite-sum lemmas are used with the packet modulus and fixed
bad-reduction certificate in the mixed-prime determinant argument. -/

namespace TranslatedDepthSeven.PrimeWeightedDeletion
noncomputable section
open scoped BigOperators
set_option maxHeartbeats 800000

theorem sum_log_prime_divisors_le
    (P : Finset ℕ) (D : ℕ) (hD : 0 < D)
    (hP : ∀ p ∈ P, p.Prime) :
    (∑ p ∈ P.filter (fun p => p ∣ D), Real.log (p : ℝ)) ≤
      Real.log (D : ℝ) := by
  have hdiv : (∏ p ∈ P.filter (fun p => p ∣ D), p) ∣ D := by
    apply Finset.prod_dvd_of_isRelPrime
    · intro p hp q hq hpq
      exact Nat.coprime_iff_isRelPrime.mp
        ((Nat.coprime_primes (hP p (Finset.mem_filter.mp hp).1)
          (hP q (Finset.mem_filter.mp hq).1)).mpr hpq)
    · intro p hp
      exact (Finset.mem_filter.mp hp).2
  have hpos : (0 : ℝ) < ∏ p ∈ P.filter (fun p => p ∣ D), (p : ℝ) := by
    apply Finset.prod_pos
    intro p hp
    exact_mod_cast (hP p (Finset.mem_filter.mp hp).1).pos
  have hle : (∏ p ∈ P.filter (fun p => p ∣ D), (p : ℝ)) ≤ (D : ℝ) := by
    have hcast : ((∏ p ∈ P.filter (fun p => p ∣ D), p : ℕ) : ℝ) ≤ (D : ℝ) := by
      exact_mod_cast Nat.le_of_dvd hD hdiv
    simpa only [Nat.cast_prod] using hcast
  have h := Real.log_le_log hpos hle
  rw [Real.log_prod] at h
  · exact h
  · intro p hp
    exact_mod_cast (hP p (Finset.mem_filter.mp hp).1).ne_zero

theorem sum_weighted_prime_divisors_le
    (P : Finset ℕ) (D : ℕ) (L : ℝ) (hD : 0 < D) (hL : 0 < L)
    (hP : ∀ p ∈ P, p.Prime) (hlarge : ∀ p ∈ P, L ≤ (p : ℝ)) :
    (∑ p ∈ P.filter (fun p => p ∣ D), Real.log (p : ℝ) / (p : ℝ)) ≤
      Real.log (D : ℝ) / L := by
  calc
    _ ≤ ∑ p ∈ P.filter (fun p => p ∣ D), Real.log (p : ℝ) / L := by
      apply Finset.sum_le_sum
      intro p hp
      exact div_le_div_of_nonneg_left
        (Real.log_nonneg (by exact_mod_cast (hP p (Finset.mem_filter.mp hp).1).one_le))
        hL (hlarge p (Finset.mem_filter.mp hp).1)
    _ = (∑ p ∈ P.filter (fun p => p ∣ D), Real.log (p : ℝ)) / L :=
      (Finset.sum_div _ _ _).symm
    _ ≤ _ := div_le_div_of_nonneg_right (sum_log_prime_divisors_le P D hD hP) hL.le

theorem weighted_sum_after_deleting_divisors_ge
    (P : Finset ℕ) (D : ℕ) (L : ℝ) (hD : 0 < D) (hL : 0 < L)
    (hP : ∀ p ∈ P, p.Prime) (hlarge : ∀ p ∈ P, L ≤ (p : ℝ)) :
    (∑ p ∈ P, Real.log (p : ℝ) / (p : ℝ)) - Real.log (D : ℝ) / L ≤
      ∑ p ∈ P.filter (fun p => ¬ p ∣ D), Real.log (p : ℝ) / (p : ℝ) := by
  have hsplit := Finset.sum_filter_add_sum_filter_not P (fun p => p ∣ D)
    (fun p => Real.log (p : ℝ) / (p : ℝ))
  have hloss := sum_weighted_prime_divisors_le P D L hD hL hP hlarge
  linarith

/-- Exact interval subtraction before deleting any primes. -/
theorem weighted_prime_interval_eq_sub (L N : ℕ) (hLN : L ≤ N) :
    (∑ p ∈ (Finset.Icc (L + 1) N).filter Nat.Prime,
      Real.log (p : ℝ) / (p : ℝ)) =
    (∑ p ∈ (Finset.Icc 1 N).filter Nat.Prime, Real.log (p : ℝ) / (p : ℝ)) -
    (∑ p ∈ (Finset.Icc 1 L).filter Nat.Prime, Real.log (p : ℝ) / (p : ℝ)) := by
  have hsub : (Finset.Icc 1 L).filter Nat.Prime ⊆
      (Finset.Icc 1 N).filter Nat.Prime := by
    intro p hp
    simp only [Finset.mem_filter, Finset.mem_Icc] at hp ⊢
    exact ⟨⟨hp.1.1, hp.1.2.trans hLN⟩, hp.2⟩
  have heq : (Finset.Icc (L + 1) N).filter Nat.Prime =
      (Finset.Icc 1 N).filter Nat.Prime \ (Finset.Icc 1 L).filter Nat.Prime := by
    ext p
    simp only [Finset.mem_sdiff, Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨hlo, hhi⟩, hp⟩
      exact ⟨⟨⟨by omega, hhi⟩, hp⟩, by omega⟩
    · rintro ⟨⟨⟨hlo, hhi⟩, hp⟩, hnot⟩
      exact ⟨⟨by by_contra h; exact hnot ⟨⟨hlo, by omega⟩, hp⟩, hhi⟩, hp⟩
  rw [heq]
  have h := Finset.sum_sdiff hsub (f := fun p : ℕ => Real.log (p : ℝ) / (p : ℝ))
  linarith

/-- A polynomial height bound on the excluded integer makes its deletion
cost bounded independently of H once the prime cutoff is at least log H. -/
theorem log_certificate_div_cutoff_le
    (D H A : ℕ) (L : ℝ) (hD : 0 < D) (hH : 1 < H)
    (hheight : D ≤ H ^ A) (hcutoff : Real.log (H : ℝ) ≤ L) :
    Real.log (D : ℝ) / L ≤ (A : ℝ) := by
  have hHR : (1 : ℝ) < H := by exact_mod_cast hH
  have hlogH : 0 < Real.log (H : ℝ) := Real.log_pos hHR
  have hL : 0 < L := hlogH.trans_le hcutoff
  have hcast : (D : ℝ) ≤ (H : ℝ) ^ A := by exact_mod_cast hheight
  have hlog := Real.log_le_log (by exact_mod_cast hD) hcast
  rw [Real.log_pow] at hlog
  apply (div_le_iff₀ hL).2
  exact hlog.trans (mul_le_mul_of_nonneg_left hcutoff (Nat.cast_nonneg A))

/-- Passing to the natural cutoff ceil(log H) costs at most log 2 in
the logarithm of the lower endpoint when log H is at least one. -/
theorem log_ceil_log_le (H : ℕ) (hH : 1 ≤ Real.log (H : ℝ)) :
    Real.log (⌈Real.log (H : ℝ)⌉₊ : ℝ) ≤
      Real.log (Real.log (H : ℝ)) + Real.log 2 := by
  have hpos : 0 < Real.log (H : ℝ) := by linarith
  have hceilpos : (0 : ℝ) < ⌈Real.log (H : ℝ)⌉₊ := hpos.trans_le (Nat.le_ceil _)
  have hceil := Nat.ceil_lt_add_one hpos.le
  have hle : (⌈Real.log (H : ℝ)⌉₊ : ℝ) ≤ 2 * Real.log (H : ℝ) := by linarith
  have hlog := Real.log_le_log hceilpos hle
  rw [Real.log_mul (by norm_num) hpos.ne'] at hlog
  linarith

/-- Only the two indicated prefix estimates are used here. Their actual
elementary Mertens proof is supplied separately. -/
theorem weighted_prime_interval_after_deletion_lower_bound
    (L N D : ℕ) (C : ℝ) (hL : 0 < L) (hLN : L ≤ N) (hD : 0 < D)
    (hupper : (∑ p ∈ (Finset.Icc 1 L).filter Nat.Prime,
      Real.log (p : ℝ) / (p : ℝ)) ≤ Real.log (L : ℝ) + C)
    (hlower : Real.log (N : ℝ) - C ≤
      ∑ p ∈ (Finset.Icc 1 N).filter Nat.Prime, Real.log (p : ℝ) / (p : ℝ)) :
    Real.log (N : ℝ) - Real.log (L : ℝ) - 2 * C - Real.log (D : ℝ) / L ≤
      ∑ p ∈ (Finset.Icc (L + 1) N).filter (fun p => p.Prime ∧ ¬ p ∣ D),
        Real.log (p : ℝ) / (p : ℝ) := by
  have h := weighted_sum_after_deleting_divisors_ge
    ((Finset.Icc (L + 1) N).filter Nat.Prime) D L hD (by exact_mod_cast hL)
    (fun p hp => (Finset.mem_filter.mp hp).2)
    (fun p hp => by
      have hpL := (Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1).1
      exact_mod_cast (show L ≤ p by omega))
  rw [weighted_prime_interval_eq_sub L N hLN] at h
  simp only [Finset.filter_filter] at h
  linarith

/-- The unweighted logarithmic cost of any chosen prime subset is bounded
by the existing elementary Chebyshev estimate. -/
theorem sum_prime_log_le_log_four_mul (P : Finset ℕ) (N : ℕ)
    (hP : ∀ p ∈ P, p.Prime) (hPN : ∀ p ∈ P, p ≤ N) :
    (∑ p ∈ P, Real.log (p : ℝ)) ≤ Real.log 4 * (N : ℝ) := by
  have hsub : P ⊆ (Finset.Ioc 0 N).filter Nat.Prime := by
    intro p hp
    exact Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨(hP p hp).pos, hPN p hp⟩, hP p hp⟩
  have hsum : (∑ p ∈ P, Real.log (p : ℝ)) ≤ Chebyshev.theta (N : ℝ) := by
    simp only [Chebyshev.theta, Nat.floor_natCast]
    apply Finset.sum_le_sum_of_subset_of_nonneg hsub
    intro p hp _
    exact Real.log_nonneg (by exact_mod_cast (Finset.mem_filter.mp hp).2.one_le)
  exact hsum.trans (Chebyshev.theta_le_log4_mul_x (Nat.cast_nonneg N))

end
end TranslatedDepthSeven.PrimeWeightedDeletion
