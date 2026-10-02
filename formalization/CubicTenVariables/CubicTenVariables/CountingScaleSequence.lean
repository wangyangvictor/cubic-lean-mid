import CubicTenVariables.CountingScaleChoice
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecificLimits.Basic

/-! A concrete natural delta-method scale for every large integral physical
scale P=k. The ceiling sequence satisfies the counting window and the
vanishing normalized square needed for convergence of the main term. -/

set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.CountingScaleSequence
open Filter
open scoped Topology

def scale (η : ℝ) (k : ℕ) : ℕ := ⌈(k:ℝ)^((3:ℝ)/2-η)⌉₊

theorem lower_bound (η : ℝ) (k : ℕ) :
    (k:ℝ)^((3:ℝ)/2-η) ≤ (scale η k:ℝ) := Nat.le_ceil _

theorem tendsto_scale (η : ℝ) (hη : η ≤ 1/2) :
    Tendsto (scale η) atTop atTop := by
  exact tendsto_nat_ceil_atTop.comp
    ((tendsto_rpow_atTop (by linarith : 0 < (3:ℝ)/2-η)).comp
      tendsto_natCast_atTop_atTop)

/-- The literal ceiling lies in the whole smaller window for all sufficiently
large k; no subsequence or existential choice of Q is used. -/
theorem eventually_window (η : ℝ) (hη : 0 < η) (hηhalf : η ≤ 1/2) :
    ∀ᶠ k : ℕ in atTop, 1 ≤ scale η k ∧
      (k:ℝ)^((3:ℝ)/2-η) ≤ (scale η k:ℝ) ∧
      (scale η k:ℝ) ≤ (k:ℝ)^((3:ℝ)/2-η/2) := by
  obtain ⟨P₀, hP₀, hb⟩ := CountingScaleChoice.exists_threshold η hη
  have ht : Tendsto (fun k : ℕ => (k:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  filter_upwards [ht.eventually (eventually_ge_atTop P₀)] with k hk
  exact CountingScaleChoice.ceiling_bounds (k:ℝ) η (by linarith) hηhalf (hb k hk)

theorem eventually_normalized_square_le (η : ℝ) (hη : 0 < η) (hηhalf : η ≤ 1/2) :
    ∀ᶠ k : ℕ in atTop, (scale η k:ℝ)^2/(k:ℝ)^3 ≤ (k:ℝ)^(-η) := by
  filter_upwards [eventually_window η hη hηhalf, eventually_ge_atTop 1] with k hk hk1
  exact CountingScaleChoice.normalized_square_le (k:ℝ) (scale η k:ℝ) η
    (by exact_mod_cast (by omega : 0 < k)) (by positivity) hk.2.2

/-- The kernel's near-one neighborhood eventually contains every fixed
rescaled coordinate because this concrete normalized square tends to zero. -/
theorem normalized_square_tendsto_zero (η : ℝ) (hη : 0 < η) (hηhalf : η ≤ 1/2) :
    Tendsto (fun k : ℕ => (scale η k:ℝ)^2/(k:ℝ)^3) atTop (𝓝 0) := by
  refine squeeze_zero' (Eventually.of_forall fun k => by positivity)
    (eventually_normalized_square_le η hη hηhalf) ?_
  exact (tendsto_rpow_neg_atTop hη).comp tendsto_natCast_atTop_atTop

/-- All requirements for the counting and integral limits hold on P=k with
the same explicit natural sequence Q. -/
theorem properties (η : ℝ) (hη : 0 < η) (hηhalf : η ≤ 1/2) :
    Tendsto (scale η) atTop atTop ∧
    Tendsto (fun k : ℕ => (scale η k:ℝ)^2/(k:ℝ)^3) atTop (𝓝 0) ∧
    (∀ᶠ k : ℕ in atTop, 1 ≤ scale η k ∧
      (k:ℝ)^((3:ℝ)/2-η) ≤ (scale η k:ℝ) ∧
      (scale η k:ℝ) ≤ (k:ℝ)^((3:ℝ)/2-η/2)) :=
  ⟨tendsto_scale η hηhalf, normalized_square_tendsto_zero η hη hηhalf,
    eventually_window η hη hηhalf⟩

end CubicTenVariables.CountingScaleSequence
