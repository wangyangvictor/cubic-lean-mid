import CubicTenVariables.FrobeniusPhaseNoncancellation

/-! Elementary spectral growth for literal finite complex power sums.
Repeated values retain their positive multiplicities. No geometric or
cohomological realization is assumed or constructed. -/

open Filter Finset
open scoped Topology

namespace CubicTenVariables.ComplexPowerSumGrowth

open FrobeniusPhase

theorem geometricAverage_tendsto_zero_of_norm_le_one {z : ℂ}
    (hz : ‖z‖ ≤ 1) (hne : z ≠ 1) :
    Tendsto (geometricAverage z) atTop (𝓝 0) := by
  apply squeeze_zero_norm (a := fun N : ℕ => (2 / ‖z - 1‖) / N)
  · intro N
    rw [geometricAverage, norm_div, Complex.norm_natCast]
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg N)
    rw [geom_sum_eq hne N, norm_div]
    apply div_le_div_of_nonneg_right _ (norm_nonneg _)
    calc
      ‖z ^ N - 1‖ ≤ ‖z ^ N‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ ≤ 2 := by
        rw [norm_pow, norm_one]
        linarith [show ‖z‖ ^ N ≤ 1 from pow_le_one₀ (norm_nonneg z) hz]
  · exact tendsto_const_div_atTop_nhds_zero_nat _

theorem sum_powers_not_tendsto_zero_of_mem_one {ι : Type*}
    (s : Finset ι) (z : ι → ℂ) (hz : ∀ i ∈ s, ‖z i‖ ≤ 1)
    (hone : ∃ i ∈ s, z i = 1) :
    ¬ Tendsto (fun n : ℕ => ∑ i ∈ s, z i ^ n) atTop (𝓝 0) := by
  classical
  intro hzero
  have hterm (i : ι) (hi : i ∈ s) :
      Tendsto (geometricAverage (z i)) atTop (𝓝 (if z i = 1 then 1 else 0)) := by
    split_ifs with h
    · simpa [h] using geometricAverage_one_tendsto
    · exact geometricAverage_tendsto_zero_of_norm_le_one (hz i hi) h
  have hsum := tendsto_finset_sum s hterm
  have hces : Tendsto (fun N : ℕ => ∑ i ∈ s, geometricAverage (z i) N)
      atTop (𝓝 (0 : ℂ)) := by
    convert hzero.cesaro_smul using 1
    ext N
    simp only [geometricAverage]
    rw [← sum_div, sum_comm]
    simp only [Complex.real_smul, Complex.ofReal_inv, Complex.ofReal_natCast,
      div_eq_mul_inv, mul_comm]
  have heq := tendsto_nhds_unique hsum hces
  have hcard : ((s.filter (fun i => z i = 1)).card : ℂ) = 0 := by
    simpa using heq
  have hempty : (s.filter (fun i => z i = 1)).card = 0 := by exact_mod_cast hcard
  obtain ⟨i, hi, hzi⟩ := hone
  exact (Finset.card_pos.mpr ⟨i, mem_filter.mpr ⟨hi, hzi⟩⟩).ne' hempty

/-- An eventual exponential bound on a finite power sum bounds every base.
The family may contain repeated values; their multiplicities are positive. -/
theorem norm_le_of_eventually_power_sum_bound {ι : Type*}
    (s : Finset ι) (α : ι → ℂ) {q C : ℝ} (hq : 0 < q)
    (hbound : ∀ᶠ n : ℕ in atTop, ‖∑ i ∈ s, α i ^ n‖ ≤ C * q ^ n) :
    ∀ i ∈ s, ‖α i‖ ≤ q := by
  classical
  intro i hi
  by_contra hbad
  obtain ⟨j, hj, hmax⟩ := s.exists_max_image (fun i => ‖α i‖) ⟨i, hi⟩
  have hqj : q < ‖α j‖ := (lt_of_not_ge hbad).trans_le (hmax i hi)
  have hjpos : 0 < ‖α j‖ := hq.trans hqj
  have hjne : α j ≠ 0 := norm_pos_iff.mp hjpos
  have hratio : q / ‖α j‖ < 1 := (div_lt_one hjpos).mpr hqj
  have hnonneg : 0 ≤ q / ‖α j‖ := div_nonneg hq.le hjpos.le
  have hlim : Tendsto (fun n : ℕ => C * (q / ‖α j‖) ^ n) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_norm_lt_one
      (show ‖q / ‖α j‖‖ < 1 by rwa [Real.norm_eq_abs, abs_of_nonneg hnonneg])).const_mul C
  have hzero : Tendsto (fun n : ℕ => ∑ i ∈ s, (α i / α j) ^ n) atTop (𝓝 0) := by
    apply squeeze_zero_norm' _ hlim
    filter_upwards [hbound] with n hn
    have heq : ‖∑ i ∈ s, (α i / α j) ^ n‖ =
        ‖∑ i ∈ s, α i ^ n‖ / ‖α j‖ ^ n := by
      simp only [div_pow]
      rw [← sum_div, norm_div, norm_pow]
    rw [heq]
    calc
      ‖∑ i ∈ s, α i ^ n‖ / ‖α j‖ ^ n ≤ (C * q ^ n) / ‖α j‖ ^ n :=
        div_le_div_of_nonneg_right hn (pow_nonneg hjpos.le _)
      _ = C * (q / ‖α j‖) ^ n := by rw [div_pow]; ring
  apply sum_powers_not_tendsto_zero_of_mem_one s (fun i => α i / α j) _ _ hzero
  · intro k hk
    rw [norm_div]
    exact (div_le_one hjpos).mpr (hmax k hk)
  · exact ⟨j, hj, div_self hjne⟩

/-- A bound along all positive multiples of one extension degree already
controls every eigenvalue; raising to that degree cannot cancel multiplicity. -/
theorem norm_le_of_power_sum_multiples_bound {ι : Type*}
    (s : Finset ι) (α : ι → ℂ) {q C : ℝ} (hq : 0 < q)
    (d : ℕ) (hd : 1 ≤ d)
    (hbound : ∀ m : ℕ, 1 ≤ m →
      ‖∑ i ∈ s, α i ^ (d * m)‖ ≤ C * (q ^ d) ^ m) :
    ∀ i ∈ s, ‖α i‖ ≤ q := by
  have h := norm_le_of_eventually_power_sum_bound s (fun i => α i ^ d)
    (pow_pos hq d) (C := C) (by
      filter_upwards [eventually_ge_atTop 1] with m hm
      simpa only [← pow_mul] using hbound m hm)
  intro i hi
  apply le_of_pow_le_pow_left₀ (by omega : d ≠ 0) hq.le
  simpa only [norm_pow] using h i hi

end CubicTenVariables.ComplexPowerSumGrowth
