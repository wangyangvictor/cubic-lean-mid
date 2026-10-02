import HessianTheorem11.UnconditionalWeightMixedSpeed

/-! Strict convexity identifies equal-length integral maximizers for a
fixed pair of weak (existence of a limit) and strict (target-ideal order)
character supports. -/
noncomputable section
namespace HessianTheorem11.UnconditionalWeightMixed
open UnconditionalWeightOptimization
variable {n : ℕ}

theorem finiteMinimum_pos {T : Finset (Fin n → ℤ)} (hT : T.Nonempty)
    (z : Fin n → ℤ) (hz : ∀ a ∈ T, 0 < integralCharacter a z) :
    0 < finiteMinimum T z := by
  obtain ⟨a,ha,h⟩ := finiteMinimum_attained hT z
  rw [h]
  exact hz a ha

theorem normalized_integer_feasible {S T : Finset (Fin n → ℤ)}
    (z : Fin n → ℤ) (hsum : ∑ j, z j = 0)
    (hS : ∀ a ∈ S, 0 ≤ integralCharacter a z) (hp : 0 < finiteMinimum T z) :
    (finiteMinimum T z : ℝ)⁻¹ • realWeight z ∈ feasible S T := by
  have hpr : (0 : ℝ) < finiteMinimum T z := by exact_mod_cast hp
  refine ⟨by simp [hsum],?_,?_⟩
  · intro a ha
    rw [map_smul,character_realWeight]
    exact mul_nonneg (inv_nonneg.mpr hpr.le) (by exact_mod_cast hS a ha)
  · intro a ha
    rw [map_smul,character_realWeight]
    change 1 ≤ (finiteMinimum T z : ℝ)⁻¹ * (integralCharacter a z : ℝ)
    calc
      1 = (finiteMinimum T z : ℝ)⁻¹ * (finiteMinimum T z : ℝ) :=
        (inv_mul_cancel₀ hpr.ne').symm
      _ ≤ _ := mul_le_mul_of_nonneg_left (by exact_mod_cast finiteMinimum_le z ha)
        (inv_nonneg.mpr hpr.le)

theorem realWeight_ne_zero_of_minimum_pos {T : Finset (Fin n → ℤ)}
    (hT : T.Nonempty) (z : Fin n → ℤ) (hp : 0 < finiteMinimum T z) :
    realWeight z ≠ 0 := by
  intro hz
  obtain ⟨a,ha⟩ := hT
  have hh : (integralCharacter a z : ℝ) = 0 := by
    rw [← character_realWeight,hz,map_zero]
  have hh' : integralCharacter a z = 0 := by exact_mod_cast hh
  have hle := finiteMinimum_le z ha
  omega

theorem minimumNorm_of_integer_maximizer {S T : Finset (Fin n → ℤ)}
    (hT : T.Nonempty) (z : Fin n → ℤ) (hsum : ∑ j, z j = 0)
    (hS : ∀ a ∈ S, 0 ≤ integralCharacter a z)
    (hpos : ∀ a ∈ T, 0 < integralCharacter a z)
    (hmax : ∀ u : Fin n → ℤ, (∑ j, u j) = 0 →
      (∀ a ∈ S, 0 ≤ integralCharacter a u) → finiteSpeed T u ≤ finiteSpeed T z) :
    MinimumNorm S T ((finiteMinimum T z : ℝ)⁻¹ • realWeight z) := by
  have hp := finiteMinimum_pos hT z hpos
  have hpr : (0 : ℝ) < finiteMinimum T z := by exact_mod_cast hp
  have hf := normalized_integer_feasible z hsum hS hp
  obtain ⟨w,N,u,hw,hN,hu,husum,huS,_,_⟩ := exists_integral_optimal_ray S T hT ⟨_,hf⟩
  have hspeed : finiteSpeed T z = 1 / ‖w‖ := by
    apply le_antisymm (finiteSpeed_le_minimumNorm hT hw z hsum hS)
    rw [← finiteSpeed_of_minimumNorm_multiple hT hw N hN u hu]
    exact hmax u husum huS
  have hnz : 0 < ‖realWeight z‖ := norm_pos_iff.mpr
    (realWeight_ne_zero_of_minimum_pos hT z hp)
  have hnw : 0 < ‖w‖ := norm_pos_iff.mpr (feasible_ne_zero hT hw.1)
  have hmul : (finiteMinimum T z : ℝ) * ‖w‖ = ‖realWeight z‖ := by
    have h := (div_eq_div_iff hnz.ne' hnw.ne').mp hspeed
    simpa only [one_mul] using h
  have hnorm : ‖(finiteMinimum T z : ℝ)⁻¹ • realWeight z‖ = ‖w‖ := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hpr),← hmul,
      ← mul_assoc,inv_mul_cancel₀ hpr.ne',one_mul]
  exact ⟨hf,fun v hv => by rw [hnorm]; exact hw.2 v hv⟩

/-- Equal-norm maximizing integer weights coincide, including their
integer scale. Only admissible competitors are needed. -/
theorem same_norm_integer_maximizers_equal {S T : Finset (Fin n → ℤ)}
    (hT : T.Nonempty) (z u : Fin n → ℤ)
    (hzsum : ∑ j, z j = 0) (husum : ∑ j, u j = 0)
    (hzS : ∀ a ∈ S, 0 ≤ integralCharacter a z)
    (huS : ∀ a ∈ S, 0 ≤ integralCharacter a u)
    (hzpos : ∀ a ∈ T, 0 < integralCharacter a z)
    (hupos : ∀ a ∈ T, 0 < integralCharacter a u)
    (hzmax : ∀ v : Fin n → ℤ, (∑ j, v j) = 0 →
      (∀ a ∈ S, 0 ≤ integralCharacter a v) → finiteSpeed T v ≤ finiteSpeed T z)
    (humax : ∀ v : Fin n → ℤ, (∑ j, v j) = 0 →
      (∀ a ∈ S, 0 ≤ integralCharacter a v) → finiteSpeed T v ≤ finiteSpeed T u)
    (hnorm : ‖realWeight z‖ = ‖realWeight u‖) : z = u := by
  have hp := finiteMinimum_pos hT z hzpos
  have hpr : (0 : ℝ) < finiteMinimum T z := by exact_mod_cast hp
  have hspeed := le_antisymm (humax z hzsum hzS) (hzmax u husum huS)
  have hnz : ‖realWeight z‖ ≠ 0 := (norm_pos_iff.mpr
    (realWeight_ne_zero_of_minimum_pos hT z hp)).ne'
  have hmin : finiteMinimum T z = finiteMinimum T u := by
    unfold finiteSpeed at hspeed
    rw [← hnorm] at hspeed
    have hh := (div_left_inj' hnz).mp hspeed
    exact_mod_cast hh
  have he := minimumNorm_unique
    (minimumNorm_of_integer_maximizer hT z hzsum hzS hzpos hzmax)
    (minimumNorm_of_integer_maximizer hT u husum huS hupos humax)
  rw [← hmin] at he
  have hre : realWeight z = realWeight u :=
    (smul_right_injective _ (inv_ne_zero hpr.ne')) he
  funext i
  have hi : (z i : ℝ) = (u i : ℝ) := congrArg (fun v : WeightSpace n => v i) hre
  exact_mod_cast hi

end HessianTheorem11.UnconditionalWeightMixed
