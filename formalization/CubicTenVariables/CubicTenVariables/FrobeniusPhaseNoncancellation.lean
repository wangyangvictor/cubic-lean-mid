import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.Order.Field.GeomSum
import Mathlib.Tactic

/-!+# Elementary noncancellation of distinct unit-circle phases

This file concerns literal complex numbers and finite sums only. It constructs no
cohomology groups and assumes no trace formula or geometric weight statement.
The intended application is the final elementary step of a Frobenius trace argument.
-/

open Filter Finset
open scoped Topology

namespace CubicTenVariables.FrobeniusPhase

/-- The average of the first `N` powers, with the harmless convention `N = 0 ↦ 0`. -/
noncomputable def geometricAverage (u : ℂ) (N : ℕ) : ℂ :=
  (∑ n ∈ range N, u ^ n) / (N : ℂ)

theorem geometricAverage_tendsto_zero {u : ℂ} (hu : ‖u‖ = 1) (hne : u ≠ 1) :
    Tendsto (geometricAverage u) atTop (𝓝 0) := by
  apply squeeze_zero_norm (a := fun N : ℕ => (2 / ‖u - 1‖) / N)
  · intro N
    rw [geometricAverage, norm_div, Complex.norm_natCast]
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg N)
    rw [geom_sum_eq hne N, norm_div]
    apply div_le_div_of_nonneg_right _ (norm_nonneg _)
    calc
      ‖u ^ N - 1‖ ≤ ‖u ^ N‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = 2 := by norm_num [norm_pow, hu]
  · exact tendsto_const_div_atTop_nhds_zero_nat _

theorem geometricAverage_one_tendsto :
    Tendsto (geometricAverage 1) atTop (𝓝 1) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_ge_atTop 1] with N hN
  simp [geometricAverage, (by exact_mod_cast (show N ≠ 0 by omega) : (N : ℂ) ≠ 0)]

/-- A literal finite complex power sum. -/
noncomputable def phaseSum {ι : Type*} (s : Finset ι) (c z : ι → ℂ) (n : ℕ) : ℂ :=
  ∑ i ∈ s, c i * z i ^ n

private theorem phase_conj_ne_one {ι : Type*} {s : Finset ι} {z : ι → ℂ}
    (hz : ∀ i ∈ s, ‖z i‖ = 1) (hinj : Set.InjOn z (↑s : Set ι))
    {i j : ι} (hi : i ∈ s) (hj : j ∈ s) (hij : i ≠ j) :
    z i * starRingEnd ℂ (z j) ≠ 1 := by
  intro heq
  apply hij
  apply hinj hi hj
  have hc : starRingEnd ℂ (z j) * z j = 1 := by
    rw [mul_comm, RCLike.mul_conj, hz j hj]
    norm_num
  calc
    z i = z i * (starRingEnd ℂ (z j) * z j) := by rw [hc, mul_one]
    _ = z j := by rw [← mul_assoc, heq, one_mul]

/-- Cesàro orthogonality: distinct unit phases leave exactly the diagonal terms. -/
theorem phaseSum_meanSquare_tendsto {ι : Type*} (s : Finset ι) (c z : ι → ℂ)
    (hz : ∀ i ∈ s, ‖z i‖ = 1) (hinj : Set.InjOn z (↑s : Set ι)) :
    Tendsto (fun N : ℕ => (N : ℝ)⁻¹ * ∑ n ∈ range N, ‖phaseSum s c z n‖ ^ 2)
      atTop (𝓝 (∑ i ∈ s, ‖c i‖ ^ 2)) := by
  classical
  have hpair (i : ι) (hi : i ∈ s) (j : ι) (hj : j ∈ s) :
      Tendsto (fun N => c i * starRingEnd ℂ (c j) *
        geometricAverage (z i * starRingEnd ℂ (z j)) N) atTop
        (𝓝 (if i = j then c i * starRingEnd ℂ (c j) else 0)) := by
    by_cases hij : i = j
    · subst j
      have hu : z i * starRingEnd ℂ (z i) = 1 := by
        rw [RCLike.mul_conj, hz i hi]
        norm_num
      simpa [hu] using geometricAverage_one_tendsto.const_mul
        (c i * starRingEnd ℂ (c i))
    · have hu : ‖z i * starRingEnd ℂ (z j)‖ = 1 := by
        simp [hz i hi, hz j hj]
      simpa [hij] using (geometricAverage_tendsto_zero hu
        (phase_conj_ne_one hz hinj hi hj hij)).const_mul (c i * starRingEnd ℂ (c j))
  have hsum := tendsto_finset_sum s (fun i hi =>
    tendsto_finset_sum s (fun j hj => hpair i hi j hj))
  have hexpand (N : ℕ) :
      ∑ i ∈ s, ∑ j ∈ s, c i * starRingEnd ℂ (c j) *
          geometricAverage (z i * starRingEnd ℂ (z j)) N =
        ((∑ n ∈ range N, ‖phaseSum s c z n‖ ^ 2 : ℝ) : ℂ) / (N : ℂ) := by
    simp only [geometricAverage, ← mul_div_assoc, ← sum_div]
    congr 1
    simp only [Complex.ofReal_sum, ← Complex.normSq_eq_norm_sq, ← Complex.mul_conj,
      phaseSum, map_sum, map_mul, map_pow, mul_pow, mul_sum, sum_mul]
    simp_rw [sum_comm (s := s) (t := range N)]
    apply sum_congr rfl
    intro n hn
    rw [sum_comm]
    apply sum_congr rfl
    intro j hj
    apply sum_congr rfl
    intro i hi
    ring
  have hcomplex : Tendsto
      (fun N : ℕ => ((∑ n ∈ range N, ‖phaseSum s c z n‖ ^ 2 : ℝ) : ℂ) / (N : ℂ))
      atTop (𝓝 ((∑ i ∈ s, ‖c i‖ ^ 2 : ℝ) : ℂ)) := by
    simpa [hexpand, ← Complex.normSq_eq_norm_sq, Complex.mul_conj] using hsum
  have hreal := Complex.continuous_re.continuousAt.tendsto.comp hcomplex
  change Tendsto (fun N : ℕ =>
    (((∑ n ∈ range N, ‖phaseSum s c z n‖ ^ 2 : ℝ) : ℂ) / (N : ℂ)).re)
    atTop (𝓝 (((∑ i ∈ s, ‖c i‖ ^ 2 : ℝ) : ℂ)).re) at hreal
  have hre (N : ℕ) :
      (((∑ n ∈ range N, ‖phaseSum s c z n‖ ^ 2 : ℝ) : ℂ) / (N : ℂ)).re =
        (N : ℝ)⁻¹ * ∑ n ∈ range N, ‖phaseSum s c z n‖ ^ 2 := by
    change (((∑ n ∈ range N, ‖phaseSum s c z n‖ ^ 2 : ℝ) : ℂ) /
      ((N : ℝ) : ℂ)).re = _
    rw [← Complex.ofReal_div, Complex.ofReal_re]
    ring
  simpa only [hre, Complex.ofReal_re] using hreal

/-- A limiting Cesàro mean cannot exceed an eventual upper bound. -/
theorem cesaro_limit_le_of_eventually_le {f : ℕ → ℝ} {L C : ℝ}
    (hlim : Tendsto (fun N : ℕ => (N : ℝ)⁻¹ * ∑ n ∈ range N, f n)
      atTop (𝓝 L)) (hbound : ∀ᶠ n in atTop, f n ≤ C) : L ≤ C := by
  have hclip : Tendsto (fun n => max (f n) C) atTop (𝓝 C) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [hbound] with n hn
    exact (max_eq_right hn).symm
  apply le_of_tendsto_of_tendsto' hlim hclip.cesaro
  intro N
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (Nat.cast_nonneg N))
  exact sum_le_sum (fun n _ => le_max_left (f n) C)

/-- A nonzero mean square forces arbitrarily late values above every smaller
nonnegative threshold. No recurrence or rationality of the phases is assumed. -/
theorem phaseSum_norm_frequently_gt {ι : Type*} (s : Finset ι) (c z : ι → ℂ)
    (hz : ∀ i ∈ s, ‖z i‖ = 1) (hinj : Set.InjOn z (↑s : Set ι))
    {a : ℝ} (ha : 0 ≤ a) (haS : a ^ 2 < ∑ i ∈ s, ‖c i‖ ^ 2) :
    ∃ᶠ n in atTop, a < ‖phaseSum s c z n‖ := by
  by_contra h
  have hb : ∀ᶠ n in atTop, ‖phaseSum s c z n‖ ^ 2 ≤ a ^ 2 := by
    filter_upwards [Filter.not_frequently.mp h] with n hn
    exact (sq_le_sq₀ (norm_nonneg _) ha).mpr (le_of_not_gt hn)
  exact (not_le_of_gt haS) (cesaro_limit_le_of_eventually_le
    (phaseSum_meanSquare_tendsto s c z hz hinj) hb)

/-- Explicit tail formulation convenient for finite-extension degrees. -/
theorem phaseSum_exists_late_norm_gt {ι : Type*} (s : Finset ι) (c z : ι → ℂ)
    (hz : ∀ i ∈ s, ‖z i‖ = 1) (hinj : Set.InjOn z (↑s : Set ι))
    {a : ℝ} (ha : 0 ≤ a) (haS : a ^ 2 < ∑ i ∈ s, ‖c i‖ ^ 2) (N : ℕ) :
    ∃ n ≥ N, a < ‖phaseSum s c z n‖ :=
  Filter.frequently_atTop.mp (phaseSum_norm_frequently_gt s c z hz hinj ha haS) N

/-- A vanishing lower-order remainder cannot destroy the positive limsup.
The separate thresholds avoid introducing square roots into the statement. -/
theorem phaseSum_add_null_norm_frequently_gt {ι : Type*}
    (s : Finset ι) (c z : ι → ℂ)
    (hz : ∀ i ∈ s, ‖z i‖ = 1) (hinj : Set.InjOn z (↑s : Set ι))
    {a b : ℝ} (hb : 0 ≤ b) (hab : a < b)
    (hbS : b ^ 2 < ∑ i ∈ s, ‖c i‖ ^ 2)
    {r : ℕ → ℂ} (hr : Tendsto r atTop (𝓝 0)) :
    ∃ᶠ n in atTop, a < ‖phaseSum s c z n + r n‖ := by
  have hnorm : Tendsto (fun n => ‖r n‖) atTop (𝓝 0) := by simpa using hr.norm
  have hsmall : ∀ᶠ n in atTop, ‖r n‖ < b - a :=
    hnorm.eventually_lt_const (sub_pos.mpr hab)
  apply ((phaseSum_norm_frequently_gt s c z hz hinj hb hbS).and_eventually hsmall).mono
  intro n hn
  have htriangle : ‖phaseSum s c z n‖ ≤ ‖phaseSum s c z n + r n‖ + ‖r n‖ := by
    simpa using norm_sub_le (phaseSum s c z n + r n) (r n)
  linarith [hn.1, hn.2]

end CubicTenVariables.FrobeniusPhase
