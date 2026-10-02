import HessianTheorem11.UnconditionalWeightMixed
import HessianTheorem11.UnconditionalWeightSpeed

/-! An integral maximizer of normalized relative character speed exists
for each feasible pair of finite weak and strict character supports. -/
noncomputable section
namespace HessianTheorem11.UnconditionalWeightMixed
open UnconditionalWeightOptimization
variable {n : ℕ}

def integralCharacter (a z : Fin n → ℤ) : ℤ := ∑ i, a i * z i

def finiteMinimum (T : Finset (Fin n → ℤ)) (z : Fin n → ℤ) : ℤ :=
  if h : T.Nonempty then T.inf' h (fun a => integralCharacter a z) else 0

def finiteSpeed (T : Finset (Fin n → ℤ)) (z : Fin n → ℤ) : ℝ :=
  (finiteMinimum T z : ℝ) / ‖realWeight z‖

theorem finiteMinimum_le {T : Finset (Fin n → ℤ)} (z : Fin n → ℤ)
    {a : Fin n → ℤ} (ha : a ∈ T) : finiteMinimum T z ≤ integralCharacter a z := by
  classical
  have hT : T.Nonempty := ⟨a,ha⟩
  simpa only [finiteMinimum,dif_pos hT] using Finset.inf'_le (fun a => integralCharacter a z) ha

theorem finiteMinimum_attained {T : Finset (Fin n → ℤ)} (hT : T.Nonempty)
    (z : Fin n → ℤ) : ∃ a ∈ T, finiteMinimum T z = integralCharacter a z := by
  classical
  simpa only [finiteMinimum,dif_pos hT] using Finset.exists_mem_eq_inf' hT (fun a => integralCharacter a z)

@[simp] theorem character_realWeight (a z : Fin n → ℤ) :
    character a (realWeight z) = (integralCharacter a z : ℝ) := by
  simp [character,UnconditionalWeightPolyhedron.row,realWeight,integralCharacter]

theorem finiteSpeed_le_minimumNorm {S T : Finset (Fin n → ℤ)} (hT : T.Nonempty)
    {w : WeightSpace n} (hw : MinimumNorm S T w) (z : Fin n → ℤ)
    (hsum : ∑ j, z j = 0) (hS : ∀ a ∈ S, 0 ≤ integralCharacter a z) :
    finiteSpeed T z ≤ 1 / ‖w‖ := by
  by_cases hp : 0 < finiteMinimum T z
  · apply normalized_bound hT hw (realWeight z) (by simp [hsum])
      (fun a ha => by rw [character_realWeight]; exact_mod_cast hS a ha)
      (finiteMinimum T z : ℝ) (by exact_mod_cast hp)
    intro a ha
    rw [character_realWeight]
    exact_mod_cast finiteMinimum_le z ha
  · have hz : finiteSpeed T z ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg (by exact_mod_cast le_of_not_gt hp) (norm_nonneg _)
    exact hz.trans (one_div_nonneg.mpr (norm_nonneg _))

theorem finiteSpeed_of_minimumNorm_multiple {S T : Finset (Fin n → ℤ)}
    (hT : T.Nonempty) {w : WeightSpace n} (hw : MinimumNorm S T w)
    (N : ℤ) (hN : 0 < N) (z : Fin n → ℤ) (hz : realWeight z = (N : ℝ) • w) :
    finiteSpeed T z = 1 / ‖w‖ := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hweight (a : Fin n → ℤ) :
      (integralCharacter a z : ℝ) = (N : ℝ) * character a w := by
    rw [← character_realWeight,hz,map_smul]
    rfl
  have hmin : finiteMinimum T z = N := by
    apply le_antisymm
    · obtain ⟨a,ha,heq⟩ := minimumNorm_active hT hw
      have hh : integralCharacter a z = N := by
        have h := hweight a
        rw [heq,mul_one] at h
        exact_mod_cast h
      exact (finiteMinimum_le z ha).trans hh.le
    · obtain ⟨a,ha,heq⟩ := finiteMinimum_attained hT z
      rw [heq]
      have h := mul_le_mul_of_nonneg_left (hw.1.2.2 a ha) hNr.le
      rw [mul_one,← hweight] at h
      exact_mod_cast h
  have hn : ‖w‖ ≠ 0 := (norm_pos_iff.mpr (feasible_ne_zero hT hw.1)).ne'
  rw [finiteSpeed,hmin,hz,norm_smul,Real.norm_eq_abs,abs_of_pos hNr]
  field_simp

/-- All side constraints and the maximum are actual integer inequalities.
The maximum ranges over every admissible integral sum-zero weight. -/
theorem exists_fixed_support_maximizer (S T : Finset (Fin n → ℤ))
    (hT : T.Nonempty) (hne : (feasible S T).Nonempty) :
    ∃ z : Fin n → ℤ, (∑ j, z j) = 0 ∧
      (∀ a ∈ S, 0 ≤ integralCharacter a z) ∧
      (∀ a ∈ T, 0 < integralCharacter a z) ∧ 0 < finiteSpeed T z ∧
      ∀ u : Fin n → ℤ, (∑ j, u j) = 0 →
        (∀ a ∈ S, 0 ≤ integralCharacter a u) → finiteSpeed T u ≤ finiteSpeed T z := by
  obtain ⟨w,N,z,hw,hN,hz,hsum,hS,hpos,hne⟩ := exists_integral_optimal_ray S T hT hne
  have he := finiteSpeed_of_minimumNorm_multiple hT hw N hN z hz
  refine ⟨z,hsum,hS,hpos,?_,?_⟩
  · rw [he]
    exact one_div_pos.mpr (norm_pos_iff.mpr (feasible_ne_zero hT hw.1))
  · intro u hu hS
    rw [he]
    exact finiteSpeed_le_minimumNorm hT hw u hu hS

end HessianTheorem11.UnconditionalWeightMixed
