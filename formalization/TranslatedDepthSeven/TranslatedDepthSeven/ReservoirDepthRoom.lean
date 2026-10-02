import TranslatedDepthSeven.ReservoirSubpower

/-!
# Room in the logarithmic prime reservoir

The depth attached to a coefficient `b` is

`ceil (b * log H / log (log H))`.

Ceilings are not additive.  Nevertheless, a strict inequality between
coefficients absorbs the bounded ceiling error for all sufficiently large
`H`.  The main result below is the form needed after deleting one bad-prime
set with coefficient `b₁` and two bad-prime sets with coefficient `b₂`.
-/

namespace TranslatedDepthSeven

open Filter

noncomputable section

/-- The scale `log H / log (log H)` tends to infinity. -/
theorem tendsto_log_div_loglog_atTop :
    Tendsto (fun H : ℝ ↦ Real.log H / Real.log (Real.log H)) atTop atTop := by
  have hloglog :
      Tendsto (fun H : ℝ ↦ Real.log (Real.log H)) atTop atTop :=
    Real.tendsto_log_atTop.comp Real.tendsto_log_atTop
  have hmain := (Real.tendsto_exp_div_pow_atTop 1).comp hloglog
  apply hmain.congr'
  filter_upwards [Real.tendsto_log_atTop.eventually_gt_atTop 0] with H hlogH
  simp [Function.comp_apply, Real.exp_log hlogH]

private theorem reservoirDepth_three_le_of_gap
    {b₁ b₂ b₃ M₀ H : ℝ}
    (hb₁ : 0 ≤ b₁) (hb₂ : 0 ≤ b₂) (hb₃ : 0 ≤ b₃)
    (hscale : 0 ≤ Real.log H / Real.log (Real.log H))
    (hgap : 3 ≤ (M₀ - (b₁ + b₂ + b₃)) *
      (Real.log H / Real.log (Real.log H))) :
    reservoirDepth b₁ H + reservoirDepth b₂ H + reservoirDepth b₃ H ≤
      reservoirDepth M₀ H := by
  let R : ℝ := Real.log H / Real.log (Real.log H)
  have h₁ : (reservoirDepth b₁ H : ℝ) < b₁ * R + 1 := by
    rw [reservoirDepth,
      show b₁ * Real.log H / Real.log (Real.log H) = b₁ * R by
        simp only [R]
        ring]
    exact Nat.ceil_lt_add_one (mul_nonneg hb₁ hscale)
  have h₂ : (reservoirDepth b₂ H : ℝ) < b₂ * R + 1 := by
    rw [reservoirDepth,
      show b₂ * Real.log H / Real.log (Real.log H) = b₂ * R by
        simp only [R]
        ring]
    exact Nat.ceil_lt_add_one (mul_nonneg hb₂ hscale)
  have h₃ : (reservoirDepth b₃ H : ℝ) < b₃ * R + 1 := by
    rw [reservoirDepth,
      show b₃ * Real.log H / Real.log (Real.log H) = b₃ * R by
        simp only [R]
        ring]
    exact Nat.ceil_lt_add_one (mul_nonneg hb₃ hscale)
  have hleft :
      ((reservoirDepth b₁ H + reservoirDepth b₂ H +
          reservoirDepth b₃ H : ℕ) : ℝ) <
        (b₁ + b₂ + b₃) * R + 3 := by
    push_cast
    linarith
  have hmiddle : (b₁ + b₂ + b₃) * R + 3 ≤ M₀ * R := by
    dsimp [R] at hgap ⊢
    linarith
  have hright : M₀ * R ≤ (reservoirDepth M₀ H : ℝ) := by
    rw [reservoirDepth,
      show M₀ * Real.log H / Real.log (Real.log H) = M₀ * R by
        simp only [R]
        ring]
    exact Nat.le_ceil (M₀ * R)
  have hcast :
      ((reservoirDepth b₁ H + reservoirDepth b₂ H +
          reservoirDepth b₃ H : ℕ) : ℝ) <
        (reservoirDepth M₀ H : ℝ) :=
    hleft.trans_le (hmiddle.trans hright)
  have hnat :
      reservoirDepth b₁ H + reservoirDepth b₂ H + reservoirDepth b₃ H <
        reservoirDepth M₀ H := by
    exact_mod_cast hcast
  exact Nat.le_of_lt hnat

/-- A strict coefficient inequality leaves room for three reservoir depths.
The bounded loss of three from the ceiling functions is absorbed by
`log H / log (log H) → ∞`. -/
theorem eventually_reservoirDepth_three_le
    {b₁ b₂ b₃ M₀ : ℝ}
    (hb₁ : 0 ≤ b₁) (hb₂ : 0 ≤ b₂) (hb₃ : 0 ≤ b₃)
    (hroom : b₁ + b₂ + b₃ < M₀) :
    ∀ᶠ H : ℝ in atTop,
      reservoirDepth b₁ H + reservoirDepth b₂ H + reservoirDepth b₃ H ≤
        reservoirDepth M₀ H := by
  let δ : ℝ := M₀ - (b₁ + b₂ + b₃)
  have hδ : 0 < δ := sub_pos.mpr hroom
  filter_upwards [tendsto_log_div_loglog_atTop.eventually_ge_atTop (3 / δ)]
      with H hH
  have hthreshold : 0 ≤ (3 : ℝ) / δ := div_nonneg (by norm_num) hδ.le
  have hscale : 0 ≤ Real.log H / Real.log (Real.log H) := hthreshold.trans hH
  have hgap : 3 ≤ δ * (Real.log H / Real.log (Real.log H)) := by
    have := (div_le_iff₀ hδ).mp hH
    simpa [mul_comm] using this
  exact reservoirDepth_three_le_of_gap hb₁ hb₂ hb₃ hscale (by
    simpa [δ] using hgap)

/-- Two strict coefficient demands fit into a larger reservoir depth for all
sufficiently large `H`. -/
theorem eventually_reservoirDepth_add_le
    {b₁ b₂ M₀ : ℝ}
    (hb₁ : 0 ≤ b₁) (hb₂ : 0 ≤ b₂)
    (hroom : b₁ + b₂ < M₀) :
    ∀ᶠ H : ℝ in atTop,
      reservoirDepth b₁ H + reservoirDepth b₂ H ≤ reservoirDepth M₀ H := by
  filter_upwards [eventually_reservoirDepth_three_le hb₁ hb₂
    (show (0 : ℝ) ≤ 0 by norm_num) (by simpa using hroom)] with H hH
  simpa [reservoirDepth] using hH

/-- The form used for one certificate family of coefficient `b₁` and two
certificate families of coefficient `b₂`.  Notice that the asserted
nonnegativity of `M₀` is automatic from the other hypotheses, so it need
not be imposed separately. -/
theorem eventually_reservoirDepth_add_two_mul_le
    {b₁ b₂ M₀ : ℝ}
    (hb₁ : 0 ≤ b₁) (hb₂ : 0 ≤ b₂)
    (hroom : b₁ + 2 * b₂ < M₀) :
    ∀ᶠ H : ℝ in atTop,
      reservoirDepth b₁ H + 2 * reservoirDepth b₂ H ≤
        reservoirDepth M₀ H := by
  have hcoeff : b₁ + b₂ + b₂ < M₀ := by linarith
  filter_upwards [eventually_reservoirDepth_three_le hb₁ hb₂ hb₂ hcoeff]
      with H hH
  omega

end

end TranslatedDepthSeven
