import HessianTheorem11.UnconditionalWeightSpeed

/-! Equal-norm integer maximizers of a fixed monomial support coincide.
This is strict convexity of the already constructed feasible region. -/
noncomputable section
namespace HessianTheorem11.UnconditionalWeightOptimization
variable {n : ℕ}

theorem finiteMinimum_pos {S : Finset (Fin n →₀ ℕ)} (hS : S.Nonempty)
    (z : Fin n → ℤ) (hz : ∀ e ∈ S, 0 < monomialWeight z e) :
    0 < finiteMinimum S z := by
  obtain ⟨e,he,h⟩ := finiteMinimum_attained hS z
  rw [h]
  exact hz e he

theorem normalized_integer_feasible {S : Finset (Fin n →₀ ℕ)}
    (z : Fin n → ℤ) (hsum : ∑ j, z j = 0) (hp : 0 < finiteMinimum S z) :
    (finiteMinimum S z : ℝ)⁻¹ • realWeight z ∈ feasible S := by
  refine ⟨by simp [hsum],?_⟩
  intro e he
  rw [map_smul,realMonomialWeight_realWeight]
  change 1 ≤ (finiteMinimum S z : ℝ)⁻¹ * (monomialWeight z e : ℝ)
  have hpr : (0 : ℝ) < finiteMinimum S z := by exact_mod_cast hp
  calc
    1 = (finiteMinimum S z : ℝ)⁻¹ * (finiteMinimum S z : ℝ) :=
      (inv_mul_cancel₀ hpr.ne').symm
    _ ≤ _ := mul_le_mul_of_nonneg_left (by exact_mod_cast finiteMinimum_le z he)
      (inv_nonneg.mpr hpr.le)

theorem realWeight_ne_zero_of_minimum_pos {S : Finset (Fin n →₀ ℕ)}
    (hS : S.Nonempty) (z : Fin n → ℤ) (hp : 0 < finiteMinimum S z) :
    realWeight z ≠ 0 := by
  intro hz
  obtain ⟨e,he⟩ := hS
  have hh : (monomialWeight z e : ℝ) = 0 := by
    rw [← realMonomialWeight_realWeight,hz,map_zero]
  have hh' : monomialWeight z e = 0 := by exact_mod_cast hh
  have hle := finiteMinimum_le z he
  omega

theorem minimumNorm_of_integer_maximizer {S : Finset (Fin n →₀ ℕ)}
    (hS : S.Nonempty) (z : Fin n → ℤ) (hsum : ∑ j, z j = 0)
    (hpos : ∀ e ∈ S, 0 < monomialWeight z e)
    (hmax : ∀ u : Fin n → ℤ, (∑ j, u j) = 0 → finiteSpeed S u ≤ finiteSpeed S z) :
    MinimumNorm S ((finiteMinimum S z : ℝ)⁻¹ • realWeight z) := by
  have hp := finiteMinimum_pos hS z hpos
  have hpr : (0 : ℝ) < finiteMinimum S z := by exact_mod_cast hp
  have hf := normalized_integer_feasible z hsum hp
  obtain ⟨w,N,u,hw,hN,hu,husum,_,_⟩ := exists_integral_optimal_ray S hS ⟨_,hf⟩
  have hspeed : finiteSpeed S z = 1 / ‖w‖ := by
    apply le_antisymm (finiteSpeed_le_minimumNorm hS hw z hsum)
    rw [← finiteSpeed_of_minimumNorm_multiple hS hw N hN u hu]
    exact hmax u husum
  have hnz : 0 < ‖realWeight z‖ := norm_pos_iff.mpr
    (realWeight_ne_zero_of_minimum_pos hS z hp)
  have hnw : 0 < ‖w‖ := norm_pos_iff.mpr (feasible_ne_zero hS hw.1)
  have hmul : (finiteMinimum S z : ℝ) * ‖w‖ = ‖realWeight z‖ := by
    have h := (div_eq_div_iff hnz.ne' hnw.ne').mp hspeed
    simpa only [one_mul] using h
  have hnorm : ‖(finiteMinimum S z : ℝ)⁻¹ • realWeight z‖ = ‖w‖ := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hpr),← hmul,
      ← mul_assoc,inv_mul_cancel₀ hpr.ne',one_mul]
  exact ⟨hf,fun v hv => by rw [hnorm]; exact hw.2 v hv⟩

/-- No primitive convention is needed when the two integer vectors have
the same norm. This is the situation for Galois conjugate frames. -/
theorem same_norm_integer_maximizers_equal {S : Finset (Fin n →₀ ℕ)}
    (hS : S.Nonempty) (z u : Fin n → ℤ)
    (hzsum : ∑ j, z j = 0) (husum : ∑ j, u j = 0)
    (hzpos : ∀ e ∈ S, 0 < monomialWeight z e)
    (hupos : ∀ e ∈ S, 0 < monomialWeight u e)
    (hzmax : ∀ v : Fin n → ℤ, (∑ j, v j) = 0 → finiteSpeed S v ≤ finiteSpeed S z)
    (humax : ∀ v : Fin n → ℤ, (∑ j, v j) = 0 → finiteSpeed S v ≤ finiteSpeed S u)
    (hnorm : ‖realWeight z‖ = ‖realWeight u‖) : z = u := by
  have hp := finiteMinimum_pos hS z hzpos
  have hpr : (0 : ℝ) < finiteMinimum S z := by exact_mod_cast hp
  have hspeed := le_antisymm (humax z hzsum) (hzmax u husum)
  have hnz : ‖realWeight z‖ ≠ 0 := (norm_pos_iff.mpr
    (realWeight_ne_zero_of_minimum_pos hS z hp)).ne'
  have hmin : finiteMinimum S z = finiteMinimum S u := by
    unfold finiteSpeed at hspeed
    rw [← hnorm] at hspeed
    have hh := (div_left_inj' hnz).mp hspeed
    exact_mod_cast hh
  have he := minimumNorm_unique S
    (minimumNorm_of_integer_maximizer hS z hzsum hzpos hzmax)
    (minimumNorm_of_integer_maximizer hS u husum hupos humax)
  rw [← hmin] at he
  have hre : realWeight z = realWeight u := by
    exact (smul_right_injective _ (inv_ne_zero hpr.ne')) he
  funext i
  have hi : (z i : ℝ) = (u i : ℝ) := congrArg (fun v : WeightSpace n => v i) hre
  exact_mod_cast hi

end HessianTheorem11.UnconditionalWeightOptimization
