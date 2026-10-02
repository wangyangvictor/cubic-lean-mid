import TranslatedDepthSeven.ReservoirGraph
import TranslatedDepthSeven.ReservoirSubpower

/-!
# Subpower size of the literal reservoir graph

This file combines the finite vertex/edge count with the explicit analytic
subpower estimate.  The conclusion concerns the actual fixed-cardinality
subsets and actual one-exchange pairs, not a numerical surrogate.
-/

namespace TranslatedDepthSeven

noncomputable section

theorem reservoirGraph_size_cast_le_two_mul_rpow
    {u : Finset ℕ} {k : ℕ} {M₀ ε H : ℝ}
    (hcard : u.card = reservoirDepth M₀ H)
    (hM₀ : 0 ≤ M₀) (hε : 0 < ε)
    (hH : reservoirSubpowerThreshold M₀ 4 ε ≤ H) :
    (((u.powersetCard k).card +
        (reservoirDirectedEdges u k).card : ℕ) : ℝ) ≤
      2 * H ^ ε := by
  have hfinite := card_vertices_add_directedEdges_le_two_mul_four_pow u k
  have hcast :
      (((u.powersetCard k).card +
          (reservoirDirectedEdges u k).card : ℕ) : ℝ) ≤
        2 * (4 : ℝ) ^ u.card := by
    exact_mod_cast hfinite
  have hsub : (4 : ℝ) ^ u.card ≤ H ^ ε := by
    rw [hcard]
    exact four_pow_reservoirDepth_le_rpow hM₀ hε hH
  exact hcast.trans (mul_le_mul_of_nonneg_left hsub (by norm_num))

end

end TranslatedDepthSeven
