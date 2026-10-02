import CubicTenVariables.ModulatedDeltaCutoff
import CubicTenVariables.BoundedShiftSchwartzLattice

/-! Poisson summation for the actual modulated cutoff, uniformly over its
bounded modulation parameter. This is the near-one delta kernel's Riemann
error, with the mesh and modulation outside the choice of constant. -/

set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.ModulatedDeltaRiemann
open MeasureTheory ModulatedDeltaCutoff SmoothDeltaNormalization
open scoped BigOperators FourierTransform SchwartzMap

/-- The fixed cutoff's modulations have arbitrarily rapid Riemann-sum
convergence, uniformly for `|t|≤1` and every mesh `0<b≤1/2`. -/
theorem exists_bound (N : ℕ) : ∃ C : ℝ, 1 ≤ C ∧
    ∀ b : ℝ, 0 < b → b ≤ 1/2 → ∀ t : ℝ, |t| ≤ 1 →
      ‖(b : ℂ)*(∑' k : ℤ, modulated t (b*(k : ℝ))) -
        ∫ y : ℝ, modulated t y‖ ≤ C*b^N := by
  obtain ⟨C,hC,hbound⟩ := BoundedShiftSchwartzLattice.exists_bound (𝓕 (schwartz 0)) N
  refine ⟨C,hC,?_⟩
  intro b hb hbhalf t ht
  have hb2 : 2 ≤ b⁻¹ := by
    rw [inv_eq_one_div,le_div_iff₀ hb]
    linarith
  obtain ⟨hs,he⟩ := hbound b⁻¹ hb2 t ht
  let F : ℤ → ℂ := fun k => (𝓕 (schwartz t)) ((k : ℝ)/b)
  have hF : F = fun k : ℤ => (𝓕 (schwartz 0)) ((k : ℝ)*b⁻¹+t) := by
    funext k
    dsimp only [F]
    rw [fourier_shift]
    rfl
  have htail : Summable (fun k : ℤ => if k=0 then (0 : ℂ) else F k) := by
    simpa only [hF] using hs
  have hsf : Summable F := by
    have hz := (hasSum_ite_eq (0 : ℤ) (F 0)).summable
    convert hz.add htail using 1
    funext k
    by_cases hk : k=0 <;> simp [hk]
  have hsplit := hsf.tsum_eq_add_tsum_ite 0
  have hp := scaled_poisson (schwartz t) b hb
  have hidentity :
      (b : ℂ)*(∑' k : ℤ, modulated t (b*(k : ℝ))) -
        ∫ y : ℝ, modulated t y =
      ∑' k : ℤ, if k=0 then (0 : ℂ) else (𝓕 (schwartz 0)) ((k : ℝ)*b⁻¹+t) := by
    change (b : ℂ)*(∑' k : ℤ, schwartz t (b*(k : ℝ))) -
      ∫ y : ℝ, schwartz t y = _
    rw [hp,mul_inv_cancel_left₀ (by exact_mod_cast hb.ne')]
    have hsplit' : (∑' k : ℤ, (𝓕 (schwartz t)) ((k : ℝ)/b)) =
        (∫ y : ℝ, schwartz t y) +
          ∑' k : ℤ, if k=0 then (0 : ℂ) else (𝓕 (schwartz t)) ((k : ℝ)/b) := by
      simpa only [F,Int.cast_zero,zero_div,fourier_at_zero] using hsplit
    rw [hsplit',add_sub_cancel_left]
    change (∑' k : ℤ, if k=0 then (0 : ℂ) else F k) = _
    rw [hF]
  rw [hidentity]
  simpa only [inv_pow,div_inv_eq_mul] using he

end CubicTenVariables.ModulatedDeltaRiemann
