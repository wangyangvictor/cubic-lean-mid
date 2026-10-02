import CubicTenVariables.FixedLeadingSurfaceSurvivorNumerics

/-!
# Uniform residual constants for the normalized ordinary box

Here the progression scale is one, its center is zero, and the source and
displacement radius are both `H`. The root and terminal degrees remain their
literal natural ceilings. All constants below precede the height and hence
also every varying polynomial and finite point set. The logarithm is bounded
by the already verified real-power estimate in the two-cap residual theorem.
-/

namespace CubicTenVariables.FixedLeadingSurfaceNormalizedBoxNumerics
noncomputable section
open TranslatedDepthSeven FixedLeadingSurfaceSurvivorNumerics

/-- The literal centered residual at radius `H`, with scale one, is at most
an explicit constant times `H^(1+ε)`. There is no residual logarithmic premise. -/
theorem centered_residual_le_power
    (C : ℝ) (d b H : ℕ) (η α ε : ℝ)
    (hC : 0 ≤ C) (hH : 1 ≤ H) (hη : 0 < η)
    (hα : 0 ≤ α) (_hε : 0 ≤ ε)
    (hexponent : (1 / 2 : ℝ) + α + 6 * η ≤ 1 + ε) :
    quantitativePrefixEffectiveCurveResidualTwoCapCentered C d
      (b + quantitativePrefixUniformBlockDegree H H η α)
      (b + ⌈4 * (H : ℝ) ^ η⌉₊) (H : ℝ) 1 ≤
      (C * ((d : ℝ) * ((b : ℝ) + 5)) ^ 5 *
        (η⁻¹ + (d : ℝ) * ((b : ℝ) + 5)) * 4 ^ (1 + ε)) *
        (H : ℝ) ^ (1 + ε) := by
  have hHr : (1 : ℝ) ≤ H := by exact_mod_cast hH
  have hheight : (H : ℝ) ≤ ((2 * H + 1 : ℕ) : ℝ) + 1 := by norm_num; linarith
  have hbox : 2 * (H : ℝ) / ((1 : ℕ) : ℝ) + 2 ≤
      ((2 * H + 1 : ℕ) : ℝ) + 1 := by norm_num; linarith
  have hbase := centered_residual_le_commonHeight C d b H H (2 * H + 1) 1
    (H : ℝ) η α ε hC hη hα (by positivity) hheight hheight hbox hexponent
  have hscale : (((2 * H + 1 : ℕ) : ℝ) + 1) ^ (1 + ε) ≤
      4 ^ (1 + ε) * (H : ℝ) ^ (1 + ε) := by
    rw [← Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 4) (by positivity)]
    apply Real.rpow_le_rpow (by positivity) _ (by linarith)
    norm_num
    linarith
  exact hbase.trans (by
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hscale
      (show 0 ≤ C * ((d : ℝ) * ((b : ℝ) + 5)) ^ 5 *
        (η⁻¹ + (d : ℝ) * ((b : ℝ) + 5)) by positivity))

/-- The occurrence ledger of the actual terminal cuts also has a uniform
ordinary-box constant. This is only the occurrence mass, not a line count. -/
theorem line_occurrenceMass_le_power
    (d b H : ℕ) (η α ε : ℝ)
    (hH : 1 ≤ H) (hη : 0 ≤ η) (hα : 0 ≤ α) (hε : 0 ≤ ε)
    (hexponent : α + 2 * η ≤ 1 + ε) :
    (quantitativePrefixEffectiveLineOccurrenceMassTwoCap d
      (b + quantitativePrefixUniformBlockDegree H H η α)
      (b + ⌈4 * (H : ℝ) ^ η⌉₊) : ℝ) ≤
      (((d : ℝ) * ((b : ℝ) + 5)) ^ 2 * 2 ^ (1 + ε)) *
        (H : ℝ) ^ (1 + ε) := by
  have hHr : (1 : ℝ) ≤ H := by exact_mod_cast hH
  have hbase := quantitativePrefixEffectiveLineOccurrenceMassTwoCap_le_commonHeight
    d b H H H η α hη hα (by linarith) (by linarith)
  have hscale : ((H : ℝ) + 1) ^ (α + 2 * η) ≤
      2 ^ (1 + ε) * (H : ℝ) ^ (1 + ε) := by
    calc
      _ ≤ ((H : ℝ) + 1) ^ (1 + ε) :=
        Real.rpow_le_rpow_of_exponent_le (by linarith) hexponent
      _ ≤ (2 * (H : ℝ)) ^ (1 + ε) :=
        Real.rpow_le_rpow (by positivity) (by linarith) (by linarith)
      _ = _ := Real.mul_rpow (by norm_num) (by positivity)
  exact hbase.trans (by
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hscale
      (show 0 ≤ ((d : ℝ) * ((b : ℝ) + 5)) ^ 2 by positivity))

/-- A single positive constant bounds the nonlinear residual plus the
line-occurrence mass for every radius. It is fixed before any equation. -/
theorem exists_uniform_box_residual_constant
    (C : ℝ) (d b : ℕ) (η α ε : ℝ)
    (hC : 0 ≤ C) (hη : 0 < η) (hα : 0 ≤ α) (hε : 0 ≤ ε)
    (hexponent : (1 / 2 : ℝ) + α + 6 * η ≤ 1 + ε) :
    ∃ A : ℝ, 0 < A ∧ ∀ H : ℕ, 1 ≤ H →
      quantitativePrefixEffectiveCurveResidualTwoCapCentered C d
        (b + quantitativePrefixUniformBlockDegree H H η α)
        (b + ⌈4 * (H : ℝ) ^ η⌉₊) (H : ℝ) 1 +
      (quantitativePrefixEffectiveLineOccurrenceMassTwoCap d
        (b + quantitativePrefixUniformBlockDegree H H η α)
        (b + ⌈4 * (H : ℝ) ^ η⌉₊) : ℝ) ≤ A * (H : ℝ) ^ (1 + ε) := by
  let Ac : ℝ := C * ((d : ℝ) * ((b : ℝ) + 5)) ^ 5 *
    (η⁻¹ + (d : ℝ) * ((b : ℝ) + 5)) * 4 ^ (1 + ε)
  let Al : ℝ := ((d : ℝ) * ((b : ℝ) + 5)) ^ 2 * 2 ^ (1 + ε)
  have hAc : 0 ≤ Ac := by dsimp [Ac]; positivity
  have hAl : 0 ≤ Al := by dsimp [Al]; positivity
  refine ⟨1 + Ac + Al, by linarith, ?_⟩
  intro H hH
  have hc := centered_residual_le_power C d b H η α ε hC hH hη hα hε hexponent
  have hl := line_occurrenceMass_le_power d b H η α ε hH hη.le hα hε
    (by linarith)
  change _ ≤ Ac * (H : ℝ) ^ (1 + ε) at hc
  change _ ≤ Al * (H : ℝ) ^ (1 + ε) at hl
  have hp : 0 ≤ (H : ℝ) ^ (1 + ε) := by positivity
  nlinarith

/-- The degree-four threshold suffices to choose every exponent and one
uniform box-residual constant simultaneously. -/
theorem exists_parameters_and_uniform_box_constant
    {d : ℕ} (hd : 4 ≤ d) (C ε : ℝ) (hC : 0 ≤ C) (hε : 0 < ε) :
    ∃ K α η δ A : ℝ,
      1 < K ∧ 0 < α ∧ α < 1 ∧ 0 < η ∧ 0 < δ ∧ 0 < A ∧
      Real.sqrt K / Real.sqrt (d : ℝ) < α ∧
      2 * η + 3 * δ + 2 * α ≤ 1 + ε ∧
      (1 / 2 : ℝ) + α + 6 * η ≤ 1 + ε ∧
      ∀ H : ℕ, 1 ≤ H →
      quantitativePrefixEffectiveCurveResidualTwoCapCentered C d
        (d - 1 + quantitativePrefixUniformBlockDegree H H η α)
        (d - 1 + ⌈4 * (H : ℝ) ^ η⌉₊) (H : ℝ) 1 +
      (quantitativePrefixEffectiveLineOccurrenceMassTwoCap d
        (d - 1 + quantitativePrefixUniformBlockDegree H H η α)
        (d - 1 + ⌈4 * (H : ℝ) ^ η⌉₊) : ℝ) ≤ A * (H : ℝ) ^ (1 + ε) := by
  obtain ⟨K, α, η, δ, hK, hα, hα1, hη, hδ, hrange, hedge, hcurve⟩ :=
    exists_exponent_parameters hd ε hε
  obtain ⟨A, hA, hbound⟩ := exists_uniform_box_residual_constant
    C d (d - 1) η α ε hC hη hα.le hε.le hcurve
  exact ⟨K, α, η, δ, A, hK, hα, hα1, hη, hδ, hA, hrange,
    hedge, hcurve, hbound⟩

/-- A single threshold and positive constant absorb the complete sharp
edge majorant for all bounded-degree equations and every admissible pool.
The threshold uses the fixed degree bound `d`, not the varying chart degree. -/
theorem exists_uniform_box_edge_constant
    (d b : ℕ) (M Cq Cr η α δ ε : ℝ)
    (hM : 0 ≤ M) (hCq : 0 ≤ Cq) (hCr : 0 ≤ Cr)
    (hη : 0 ≤ η) (hδ : 0 < δ)
    (hexponent : 2 * η + 3 * δ + 2 * α ≤ 1 + ε) :
    ∃ A : ℝ, ∃ H₀ : ℕ, 0 < A ∧ 1 ≤ H₀ ∧
      ∀ H : ℕ, H₀ ≤ H → ∀ (P : Finset ℕ) (depth Δ Q R : ℕ),
      Δ ≤ d → P.card ≤ reservoirDepth M H → depth ≤ reservoirDepth M H →
      (Q : ℝ) ≤ Cq * (H : ℝ) ^ δ * (H : ℝ) ^ α →
      (R : ℝ) ≤ Cr * (H : ℝ) ^ δ →
      ((PrimeSubsetPrefix.directedEdges P depth).card : ℝ) *
        quantitativePrefixModulusSensitiveEdgeMajorant
          Δ depth d b H H Q R η α ≤ A * (H : ℝ) ^ (1 + ε) := by
  let A : ℝ := ((d : ℝ) * ((b : ℝ) + 2)) ^ 2 *
    (Cq ^ 2 + Cq * Cr + Cq + Cr)
  let H₀ : ℕ := ⌈reservoirSubpowerThreshold M
    (4 * ((max 1 d : ℕ) : ℝ)) δ⌉₊ + 1
  have hA : 0 ≤ A := by dsimp [A]; positivity
  refine ⟨1 + A, H₀, by linarith, by dsimp [H₀]; omega, ?_⟩
  intro H hH P depth Δ Q R hΔ hcard hdepth hQ hR
  have hHone : 1 ≤ H := by dsimp [H₀] at hH; omega
  have hHr : (1 : ℝ) ≤ H := by exact_mod_cast hHone
  have hthreshold : reservoirSubpowerThreshold M
      (4 * ((max 1 d : ℕ) : ℝ)) δ ≤ (H : ℝ) := by
    apply (Nat.le_ceil _).trans
    exact_mod_cast (show ⌈reservoirSubpowerThreshold M
      (4 * ((max 1 d : ℕ) : ℝ)) δ⌉₊ ≤ H by dsimp [H₀] at hH; omega)
  have hmass := directedEdge_degree_mass_le_subpower_of_degree_le
    P depth Δ d M H δ hΔ hM hδ hcard hdepth hthreshold
  have hbound := edge_majorant_le_target P depth Δ d b H H Q R
    η α δ Cq Cr 1 ε hHr hHone hη hδ.le hCq hCr (by norm_num)
    (by simp) hmass hQ hR hexponent
  have hbound' : ((PrimeSubsetPrefix.directedEdges P depth).card : ℝ) *
      quantitativePrefixModulusSensitiveEdgeMajorant
        Δ depth d b H H Q R η α ≤ A * (H : ℝ) ^ (1 + ε) := by
    simpa only [Real.one_rpow, mul_one, A] using hbound
  exact hbound'.trans (mul_le_mul_of_nonneg_right (by linarith) (by positivity))

end
end CubicTenVariables.FixedLeadingSurfaceNormalizedBoxNumerics
