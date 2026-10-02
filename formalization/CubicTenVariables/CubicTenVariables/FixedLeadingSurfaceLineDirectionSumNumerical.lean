import TranslatedDepthSeven.LowRadialProjectiveCount
import Mathlib.Analysis.PSeries

/-! Discrete partial summation for a one-dimensional height count. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
namespace CubicTenVariables.FixedLeadingSurfaceLineDirectionSumNumerical
open TranslatedDepthSeven
open scoped BigOperators

/-- A finite constant depending only on a positive exponent. -/
def pSeriesConstant (ε : ℝ) : ℝ := ∑' n : ℕ, (n : ℝ) ^ (-1 - ε)

theorem pSeriesConstant_nonneg (ε : ℝ) : 0 ≤ pSeriesConstant ε :=
  tsum_nonneg (fun n => Real.rpow_nonneg (Nat.cast_nonneg n) _)

theorem curve_terminal_bound (X : ℕ) (hX : 1 ≤ X) (ε : ℝ) (hε : 0 ≤ ε) :
    (X : ℝ) ^ (1 + ε) / (X + 1) ≤ (X : ℝ) ^ (2 * ε) := by
  have hXp : (0 : ℝ) < X := by exact_mod_cast (Nat.zero_lt_of_lt hX)
  have hX1 : (1 : ℝ) ≤ X := by exact_mod_cast hX
  have he : (X : ℝ) ^ (1 + ε) = (X : ℝ) ^ ε * X := by
    rw [show (1 : ℝ) + ε = ε + 1 by ring, Real.rpow_add hXp, Real.rpow_one]
  have hle : (X : ℝ) ^ (1 + ε) / (X + 1) ≤ (X : ℝ) ^ ε := by
    rw [div_le_iff₀ (by positivity), he]
    have hp := Real.rpow_nonneg hXp.le ε
    nlinarith
  exact hle.trans (Real.rpow_le_rpow_of_exponent_le hX1 (by linarith))

theorem curve_summand_bound (k X : ℕ) (hk : 1 ≤ k) (hkX : k ≤ X)
    (ε : ℝ) (hε : 0 ≤ ε) :
    (k : ℝ) ^ (1 + ε) / ((k : ℝ) * (k + 1)) ≤
      (X : ℝ) ^ (2 * ε) * (k : ℝ) ^ (-1 - ε) := by
  have hkp : (0 : ℝ) < k := by exact_mod_cast (Nat.zero_lt_of_lt hk)
  have hsmall : (k : ℝ) ^ (1 + ε) / ((k : ℝ) * (k + 1)) ≤
      (k : ℝ) ^ (ε - 1) := by
    rw [div_le_iff₀ (by positivity)]
    have he : (k : ℝ) ^ (1 + ε) = (k : ℝ) ^ (ε - 1) * (k : ℝ)^2 := by
      rw [show (1 : ℝ) + ε = (ε - 1) + 2 by ring, Real.rpow_add hkp,
        Real.rpow_two]
    rw [he]
    have hp := Real.rpow_nonneg hkp.le (ε - 1)
    nlinarith
  have he : (k : ℝ) ^ (ε - 1) =
      (k : ℝ) ^ (2 * ε) * (k : ℝ) ^ (-1 - ε) := by
    rw [← Real.rpow_add hkp]
    congr 1
    ring
  rw [he] at hsmall
  exact hsmall.trans (mul_le_mul_of_nonneg_right
    (Real.rpow_le_rpow hkp.le (by exact_mod_cast hkX) (by positivity))
    (Real.rpow_nonneg hkp.le _))

/-- A prefix estimate with exponent 1+ε gives a reciprocal-height sum
with exponent 2ε. The second ε pays for the convergent p-series. -/
theorem reciprocalHeight_sum_le_curve_power
    {α : Type*} [DecidableEq α]
    (S : Finset α) (height : α → ℕ) (X : ℕ) (C ε : ℝ)
    (hX : 1 ≤ X) (hC : 0 ≤ C) (hε : 0 < ε)
    (hpositive : ∀ x ∈ S, 0 < height x)
    (hbounded : ∀ x ∈ S, height x ≤ X)
    (hprefix : ∀ k : ℕ, 1 ≤ k → k ≤ X →
      ((heightPrefix S height k).card : ℝ) ≤ C * (k : ℝ) ^ (1 + ε)) :
    (∑ x ∈ S, (1 : ℝ) / height x) ≤
      C * (1 + pSeriesConstant ε) * (X : ℝ) ^ (2 * ε) := by
  classical
  rw [reciprocalHeight_sum_eq_partialSummation S height X hpositive hbounded]
  have hfilterX : heightPrefix S height X = S := by
    ext x
    simp only [heightPrefix, Finset.mem_filter]
    exact ⟨fun hx => hx.1, fun hx => ⟨hx, hbounded x hx⟩⟩
  have hcard := hprefix X hX le_rfl
  rw [hfilterX] at hcard
  have hterminal : (S.card : ℝ) / (X + 1) ≤ C * (X : ℝ) ^ (2 * ε) := by
    calc
      _ ≤ (C * (X : ℝ) ^ (1 + ε)) / (X + 1) :=
        div_le_div_of_nonneg_right hcard (by positivity)
      _ = C * ((X : ℝ) ^ (1 + ε) / (X + 1)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (curve_terminal_bound X hX ε hε.le) hC
  have hsum : (∑ k ∈ Finset.Icc 1 X,
      ((heightPrefix S height k).card : ℝ) / ((k : ℝ) * (k + 1))) ≤
      C * (X : ℝ) ^ (2 * ε) * pSeriesConstant ε := by
    calc
      _ ≤ ∑ k ∈ Finset.Icc 1 X,
          C * (X : ℝ) ^ (2 * ε) * (k : ℝ) ^ (-1 - ε) := by
        apply Finset.sum_le_sum
        intro k hk
        obtain ⟨hk1, hkX⟩ := Finset.mem_Icc.mp hk
        have hkpos : (0 : ℝ) < k := by exact_mod_cast Nat.zero_lt_of_lt hk1
        calc
          _ ≤ (C * (k : ℝ) ^ (1 + ε)) / ((k : ℝ) * (k + 1)) :=
            div_le_div_of_nonneg_right (hprefix k hk1 hkX) (by positivity)
          _ = C * ((k : ℝ) ^ (1 + ε) / ((k : ℝ) * (k + 1))) := by ring
          _ ≤ C * ((X : ℝ) ^ (2 * ε) * (k : ℝ) ^ (-1 - ε)) :=
            mul_le_mul_of_nonneg_left (curve_summand_bound k X hk1 hkX ε hε.le) hC
          _ = _ := by ring
      _ = C * (X : ℝ) ^ (2 * ε) *
          ∑ k ∈ Finset.Icc 1 X, (k : ℝ) ^ (-1 - ε) := by rw [Finset.mul_sum]
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply Summable.sum_le_tsum _ (fun n _ => Real.rpow_nonneg (Nat.cast_nonneg n) _)
        exact Real.summable_nat_rpow.mpr (by linarith)
  nlinarith

end CubicTenVariables.FixedLeadingSurfaceLineDirectionSumNumerical
