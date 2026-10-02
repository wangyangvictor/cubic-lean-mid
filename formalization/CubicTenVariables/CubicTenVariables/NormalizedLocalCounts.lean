import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

/-! Explicit normalization of a local zero-count lower bound. A positive
eventual lower bound is proved here; convergence of the normalized counts
is not asserted. Any limit, if supplied separately, is consequently positive. -/

namespace CubicTenVariables.NormalizedLocalCounts

open Filter
open scoped Topology

noncomputable def normalizedCount (p m : ℕ) (N : ℕ → ℕ) (s : ℕ) : ℝ :=
  (N s : ℝ) / (p : ℝ) ^ (s * m)

theorem inverse_power_le_normalizedCount (p m K : ℕ) (hp : 0 < p)
    (N : ℕ → ℕ) (s : ℕ) (hKs : K ≤ s)
    (hN : p ^ ((s - K) * m) ≤ N s) :
    ((p : ℝ) ^ (K * m))⁻¹ ≤ normalizedCount p m N s := by
  have hpR : 0 < (p : ℝ) := by exact_mod_cast hp
  have he : s * m = (s - K) * m + K * m := by
    rw [← Nat.add_mul, Nat.sub_add_cancel hKs]
  have hratio : ((p : ℝ) ^ (K * m))⁻¹ =
      (p : ℝ) ^ ((s - K) * m) / (p : ℝ) ^ (s * m) := by
    rw [he, pow_add, div_mul_eq_div_div, div_self (pow_ne_zero _ hpR.ne'), one_div]
  rw [hratio]
  exact div_le_div_of_nonneg_right (by exact_mod_cast hN) (pow_nonneg hpR.le _)

theorem positive_eventual_normalized_lower_bound (p m K : ℕ) (hp : 0 < p)
    (N : ℕ → ℕ) (hN : ∀ s, K ≤ s → p ^ ((s - K) * m) ≤ N s) :
    0 < ((p : ℝ) ^ (K * m))⁻¹ ∧
      ∀ᶠ s : ℕ in atTop, ((p : ℝ) ^ (K * m))⁻¹ ≤ normalizedCount p m N s := by
  have hpR : 0 < (p : ℝ) := by exact_mod_cast hp
  refine ⟨inv_pos.mpr (pow_pos hpR _), eventually_atTop.mpr ⟨K, ?_⟩⟩
  intro s hs
  exact inverse_power_le_normalizedCount p m K hp N s hs (hN s hs)

/-- Positivity of any separately proved limit; no limit-existence premise
is hidden in the preceding eventual lower-bound theorem. -/
theorem normalized_limit_pos (p m K : ℕ) (hp : 0 < p)
    (N : ℕ → ℕ) (hN : ∀ s, K ≤ s → p ^ ((s - K) * m) ≤ N s)
    (L : ℝ) (hL : Tendsto (normalizedCount p m N) atTop (𝓝 L)) : 0 < L := by
  obtain ⟨hpos, hlower⟩ := positive_eventual_normalized_lower_bound p m K hp N hN
  exact hpos.trans_le (ge_of_tendsto hL hlower)

end CubicTenVariables.NormalizedLocalCounts
