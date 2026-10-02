import CubicTenVariables.SmoothDeltaNormalization

/-! Uniform nonzero lattice tails for a Schwartz function with bounded shift.
This is the Poisson error needed for the modulated fixed cutoff in the
near-one delta-kernel estimate. No kernel bound is an input. -/

set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.BoundedShiftSchwartzLattice
open MeasureTheory
open scoped BigOperators SchwartzMap

/-- A bounded shift leaves a uniform gap for all nonzero lattice points
when the spacing is at least two. -/
theorem gap {a t : ℝ} (ha : 2 ≤ a) (ht : |t| ≤ 1) {k : ℤ} (hk : k ≠ 0) :
    |(k : ℝ)| *a/2 ≤ |(k : ℝ)*a+t| := by
  have hk1 : 1 ≤ |(k : ℝ)| := by
    exact_mod_cast (show (1 : ℤ) ≤ |k| from Int.one_le_abs hk)
  have htri : |(k : ℝ)| *a ≤ |(k : ℝ)*a+t|+|t| := by
    have h := abs_add_le ((k : ℝ)*a+t) (-t)
    simpa only [add_neg_cancel_right,abs_mul,abs_neg,abs_of_nonneg (by linarith : 0 ≤ a)] using h
  nlinarith [mul_le_mul_of_nonneg_right hk1 (by linarith : 0 ≤ a)]

/-- Every requested power saving holds uniformly for the spacing and the
shift; the complex series is absolutely summable before its norm is bounded. -/
theorem exists_bound (f : 𝓢(ℝ,ℂ)) (N : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ a : ℝ, 2 ≤ a → ∀ t : ℝ, |t| ≤ 1 →
      Summable (fun k : ℤ => if k=0 then (0 : ℂ) else f ((k : ℝ)*a+t)) ∧
      ‖∑' k : ℤ, if k=0 then (0 : ℂ) else f ((k : ℝ)*a+t)‖ ≤ C/a^N := by
  obtain ⟨B,hB,hbound⟩ := f.decay (N+2) 0
  let w : ℤ → ℝ := fun k => ((k : ℝ)^2)⁻¹
  have hw : Summable w := by
    simpa [w,one_div] using (Real.summable_one_div_int_pow.mpr (by omega : 1 < 2))
  have hw0 (k : ℤ) : 0 ≤ w k := inv_nonneg.mpr (sq_nonneg _)
  let D := B*(2 : ℝ)^(N+2)
  let W := ∑' k : ℤ, w k
  refine ⟨max 1 (D*W),le_max_left _ _,?_⟩
  intro a ha t ht
  have ha0 : 0 < a := by linarith
  have ha1 : 1 ≤ a := by linarith
  have hterm (k : ℤ) :
      ‖if k=0 then (0 : ℂ) else f ((k : ℝ)*a+t)‖ ≤ (D/a^N)*w k := by
    by_cases hk : k=0
    · simp [hk,w]
    have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast hk
    have hk1 : 1 ≤ |(k : ℝ)| := by
      exact_mod_cast (show (1 : ℤ) ≤ |k| from Int.one_le_abs hk)
    have hb := hbound ((k : ℝ)*a+t)
    simp only [norm_iteratedFDeriv_zero,Real.norm_eq_abs] at hb
    have hgap := gap ha ht hk
    have hp : (|(k : ℝ)| *a)^(N+2) ≤
        (2 : ℝ)^(N+2) * |(k : ℝ)*a+t|^(N+2) := by
      rw [← mul_pow]
      exact pow_le_pow_left₀ (by positivity) (by linarith) (N+2)
    have hc : |(k : ℝ)|^2*a^N ≤ (|(k : ℝ)| *a)^(N+2) := by
      rw [mul_pow]
      exact mul_le_mul (pow_le_pow_right₀ hk1 (by omega))
        (pow_le_pow_right₀ ha1 (by omega)) (by positivity) (by positivity)
    have hm : (|(k : ℝ)|^2*a^N)*‖f ((k : ℝ)*a+t)‖ ≤ D := by
      calc
        _ ≤ ((2 : ℝ)^(N+2)*|(k : ℝ)*a+t|^(N+2))*‖f ((k : ℝ)*a+t)‖ :=
          mul_le_mul_of_nonneg_right (hc.trans hp) (norm_nonneg _)
        _ = (2 : ℝ)^(N+2)*(|(k : ℝ)*a+t|^(N+2)*‖f ((k : ℝ)*a+t)‖) := by ring
        _ ≤ (2 : ℝ)^(N+2)*B := mul_le_mul_of_nonneg_left hb (by positivity)
        _ = D := by dsimp [D]; ring
    simp only [if_neg hk,w]
    rw [← sq_abs]
    have he : (D/a^N)*(|(k : ℝ)|^2)⁻¹ = D/(|(k : ℝ)|^2*a^N) := by ring
    rw [he]
    exact (le_div_iff₀ (mul_pos (pow_pos (abs_pos.mpr hk0) 2) (pow_pos ha0 N))).mpr
      (by simpa only [mul_comm] using hm)
  have hs := hw.mul_left (D/a^N)
  refine ⟨hs.of_norm_bounded hterm,?_⟩
  have hb := tsum_of_norm_bounded hs.hasSum hterm
  rw [tsum_mul_left] at hb
  calc
    _ ≤ (D/a^N)*W := hb
    _ = (D*W)/a^N := by ring
    _ ≤ max 1 (D*W)/a^N := div_le_div_of_nonneg_right (le_max_right _ _) (by positivity)

end CubicTenVariables.BoundedShiftSchwartzLattice
