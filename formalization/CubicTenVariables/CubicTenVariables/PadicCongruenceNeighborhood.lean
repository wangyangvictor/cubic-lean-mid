import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.SpecificLimits.Basic

/-! Every p-adic open neighborhood contains a literal congruence coset.
The radius is an actual power of the prime, and the quantified perturbations
are actual p-adic integer vectors. -/

noncomputable section
namespace CubicTenVariables.PadicCongruenceNeighborhood
open Filter
open scoped Topology

theorem exists_power_coset_subset (p : ℕ) [Fact p.Prime] {n : ℕ}
    (x : Fin n → ℚ_[p]) (U : Set (Fin n → ℚ_[p])) (hU : IsOpen U) (hx : x ∈ U) :
    ∃ M : ℕ, 1 ≤ M ∧
      ∀ z : Fin n → ℤ_[p], x + (p : ℚ_[p]) ^ M • (fun i => (z i : ℚ_[p])) ∈ U := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hU x hx
  have ht : Tendsto (fun M : ℕ => ‖(p : ℚ_[p])‖ ^ M) atTop (𝓝 (0 : ℝ)) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) Padic.norm_p_lt_one
  have he : ∀ᶠ M : ℕ in atTop, ‖(p : ℚ_[p])‖ ^ M < ε :=
    ht.eventually (gt_mem_nhds hε)
  obtain ⟨N, hN⟩ := eventually_atTop.mp he
  refine ⟨max N 1, le_max_right _ _, ?_⟩
  intro z
  apply hball
  rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left]
  have hz : ‖fun i => (z i : ℚ_[p])‖ ≤ 1 := by
    apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr
    intro i
    exact (z i).2
  calc
    ‖(p : ℚ_[p]) ^ max N 1 • (fun i => (z i : ℚ_[p]))‖ =
        ‖(p : ℚ_[p])‖ ^ max N 1 * ‖fun i => (z i : ℚ_[p])‖ := by
      rw [norm_smul, norm_pow]
    _ ≤ ‖(p : ℚ_[p])‖ ^ max N 1 := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hz
        (pow_nonneg (norm_nonneg _) _)
    _ < ε := hN _ (le_max_left _ _)

end CubicTenVariables.PadicCongruenceNeighborhood
