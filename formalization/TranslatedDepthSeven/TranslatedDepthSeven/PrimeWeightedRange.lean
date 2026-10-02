import TranslatedDepthSeven.PrimeWeightedDeletion
import TranslatedDepthSeven.PrimeWeightedMertens

/-! The actual prime family for mixed-residue determinant gains: primes
above ceil(log H), up to N, avoiding an actual integer certificate D.
The weighted gain has leading coefficient one and an absolute bounded
loss when D has polynomial height. -/

namespace TranslatedDepthSeven.PrimeWeightedRange
noncomputable section
open scoped BigOperators
open PrimeWeightedDeletion

def largePrimesAvoiding (H N D : ℕ) : Finset ℕ :=
  (Finset.Icc (⌈Real.log (H : ℝ)⌉₊ + 1) N).filter
    (fun p => p.Prime ∧ ¬ p ∣ D)

theorem mem_largePrimesAvoiding {H N D p : ℕ} :
    p ∈ largePrimesAvoiding H N D ↔
      ⌈Real.log (H : ℝ)⌉₊ < p ∧ p ≤ N ∧ p.Prime ∧ ¬ p ∣ D := by
  simp only [largePrimesAvoiding, Finset.mem_filter, Finset.mem_Icc,
    Nat.add_one_le_iff, and_assoc]

theorem prime_and_lower_bound_of_mem {H N D p : ℕ}
    (hp : p ∈ largePrimesAvoiding H N D) :
    p.Prime ∧ Real.log (H : ℝ) ≤ (p : ℝ) := by
  obtain ⟨hlo, _hhi, hprime, _hD⟩ := mem_largePrimesAvoiding.mp hp
  exact ⟨hprime, (Nat.le_ceil _).trans (by exact_mod_cast hlo.le)⟩

theorem not_dvd_factor_of_mem {H N D p d : ℕ}
    (hp : p ∈ largePrimesAvoiding H N D) (hd : d ∣ D) : ¬ p ∣ d :=
  fun h => (mem_largePrimesAvoiding.mp hp).2.2.2 (h.trans hd)

/-- One absolute constant works for every height, upper prime cutoff,
polynomial-height exponent, and nonzero excluded certificate. The two
estimates are exactly the weighted positive term and unweighted error
term used in the mixed-residue determinant bound. -/
theorem exists_largePrimeRange_estimates :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ H N A D : ℕ,
      1 ≤ Real.log (H : ℝ) → ⌈Real.log (H : ℝ)⌉₊ ≤ N →
      0 < D → D ≤ H ^ A →
      (Real.log (N : ℝ) - Real.log (Real.log (H : ℝ)) - C - A ≤
        ∑ p ∈ largePrimesAvoiding H N D, Real.log (p : ℝ) / (p : ℝ)) ∧
      (∑ p ∈ largePrimesAvoiding H N D, Real.log (p : ℝ)) ≤
        Real.log 4 * (N : ℝ) := by
  obtain ⟨C₀, hC₀, hMertens⟩ :=
    PrimeWeightedMertens.exists_abs_weighted_prime_log_sub_log_le
  refine ⟨2 * C₀ + Real.log 2, by positivity, ?_⟩
  intro H N A D hlogH hN hD hheight
  let L : ℕ := ⌈Real.log (H : ℝ)⌉₊
  have hlogHpos : 0 < Real.log (H : ℝ) := by linarith
  have hL : 0 < L := Nat.one_le_ceil_iff.mpr hlogHpos
  have hNpos : 0 < N := hL.trans_le hN
  have hH : 1 < H := by
    exact_mod_cast (Real.log_pos_iff (Nat.cast_nonneg H)).mp hlogHpos
  obtain ⟨hloN, _hhiN⟩ := abs_le.mp (hMertens N hNpos)
  obtain ⟨_hloL, hhiL⟩ := abs_le.mp (hMertens L hL)
  have hrange := weighted_prime_interval_after_deletion_lower_bound L N D C₀
    hL hN hD (by linarith) (by linarith)
  have hloss := log_certificate_div_cutoff_le D H A L hD hH hheight (Nat.le_ceil _)
  have hlogL := log_ceil_log_le H hlogH
  constructor
  · change Real.log (N : ℝ) - Real.log (Real.log (H : ℝ)) -
        (2 * C₀ + Real.log 2) - A ≤
      ∑ p ∈ (Finset.Icc (L + 1) N).filter (fun p => p.Prime ∧ ¬ p ∣ D),
        Real.log (p : ℝ) / (p : ℝ)
    change Real.log (L : ℝ) ≤ Real.log (Real.log (H : ℝ)) + Real.log 2 at hlogL
    linarith
  · apply sum_prime_log_le_log_four_mul
    · intro p hp
      exact (mem_largePrimesAvoiding.mp hp).2.2.1
    · intro p hp
      exact (mem_largePrimesAvoiding.mp hp).2.1

end
end TranslatedDepthSeven.PrimeWeightedRange
