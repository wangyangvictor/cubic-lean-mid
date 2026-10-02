import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic

/-!
# Uniform high-degree exponents and logarithmic losses

The degree is permitted to grow with the height.  A single exponent `β`
strictly below `ε/2` controls `8/(δ+3)` for every integer
`δ > ceil(16/ε)`.  Any fixed polynomial in `log V` can then be absorbed
in this fixed positive exponent gap.  All thresholds depend on fixed
constants and never on the varying degree.
-/

namespace TranslatedDepthSeven

open Filter
open scoped Topology

noncomputable section

/-- Uniform slack in the exponent for all degrees above Salberger's
cutoff. -/
theorem exists_uniform_highCurve_primeExponent
    {ε : ℝ} (hε : 0 < ε) :
    ∃ β : ℝ, 0 < β ∧ β < ε / 2 ∧
      ∀ δ : ℕ, ⌈16 / ε⌉₊ < δ → 8 / ((δ : ℝ) + 3) ≤ β := by
  let c : ℕ := ⌈16 / ε⌉₊
  let γ : ℝ := 8 / ((c : ℝ) + 4)
  have hden : 0 < (c : ℝ) + 4 := by positivity
  have hγ : 0 < γ := by dsimp only [γ]; positivity
  have hc : 16 / ε ≤ (c : ℝ) := Nat.le_ceil _
  have hc' : 16 ≤ (c : ℝ) * ε := (div_le_iff₀ hε).mp hc
  have hγlt : γ < ε / 2 := by
    dsimp only [γ]
    apply (div_lt_iff₀ hden).mpr
    nlinarith
  refine ⟨(γ + ε / 2) / 2, by positivity, by linarith, ?_⟩
  intro δ hδ
  have hδ' : (c : ℝ) + 1 ≤ (δ : ℝ) := by
    exact_mod_cast Nat.succ_le_of_lt hδ
  have hbound : 8 / ((δ : ℝ) + 3) ≤ γ := by
    exact div_le_div_of_nonneg_left (by norm_num) hden (by linarith)
  exact hbound.trans (by linarith)

/-- A fixed polynomial logarithmic loss is absorbed by a fixed positive
gap in the exponent.  The coefficient need not be positive. -/
theorem eventually_polylog_mul_rpow_le_rpow
    (C β γ : ℝ) (k : ℕ) (hC : 0 ≤ C) (hgap : β < γ) :
    ∀ᶠ V : ℝ in atTop,
      C * (1 + Real.log V) ^ k * V ^ β ≤ V ^ γ := by
  let A : ℝ := (C + 1) * 2 ^ k
  have hA : 0 < A := by dsimp only [A]; positivity
  have hsmall := (isLittleO_log_rpow_rpow_atTop (k : ℝ)
    (sub_pos.mpr hgap)).bound (show 0 < A⁻¹ by positivity)
  filter_upwards [hsmall, eventually_gt_atTop (1 : ℝ),
    Real.tendsto_log_atTop.eventually_ge_atTop 1] with V hsmall hV hlog
  have hVpos : 0 < V := zero_lt_one.trans hV
  have hlognonneg : 0 ≤ Real.log V := by linarith
  have hsmall' : (Real.log V) ^ k ≤ A⁻¹ * V ^ (γ - β) := by
    simpa only [Real.rpow_natCast, Real.norm_eq_abs,
      abs_of_nonneg (pow_nonneg hlognonneg k),
      abs_of_pos (Real.rpow_pos_of_pos hVpos (γ - β))] using hsmall
  have hsum : (1 + Real.log V) ^ k ≤ 2 ^ k * (Real.log V) ^ k := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by positivity) (by linarith) k
  have hpoly : C * (1 + Real.log V) ^ k ≤ V ^ (γ - β) := by
    calc
      C * (1 + Real.log V) ^ k ≤ C * (2 ^ k * (Real.log V) ^ k) :=
        mul_le_mul_of_nonneg_left hsum hC
      _ ≤ A * (Real.log V) ^ k := by
        dsimp only [A]
        nlinarith [show 0 ≤ 2 ^ k * (Real.log V) ^ k by positivity]
      _ ≤ A * (A⁻¹ * V ^ (γ - β)) :=
        mul_le_mul_of_nonneg_left hsmall' hA.le
      _ = V ^ (γ - β) := by field_simp
  calc
    C * (1 + Real.log V) ^ k * V ^ β ≤ V ^ (γ - β) * V ^ β :=
      mul_le_mul_of_nonneg_right hpoly (Real.rpow_nonneg hVpos.le _)
    _ = V ^ γ := by rw [← Real.rpow_add hVpos]; congr 1; ring

end

end TranslatedDepthSeven
