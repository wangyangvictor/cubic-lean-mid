import CubicTenVariables.ShiftedCompleteSumWindow
import CubicTenVariables.LocalizedSums

/-! Actual localized shifted complete-sum windows and the finite averaging reduction.
The clean shifted-average assertion is an explicit arithmetic proposition;
this file does not assume or prove it as a literature result. -/
set_option autoImplicit false
set_option maxHeartbeats 1500000
noncomputable section
namespace CubicTenVariables.LocalizedShiftedWindow
open MvPolynomial MeasureTheory LocalSupremumWindow DyadicFrequencyError
open ShiftedCompleteSumWindow (shiftedWindow mem_shiftedWindow)
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

def shiftedSum (F : MvPolynomial (Fin n) ℤ) (W : ℕ) (Ω : Set (Fin n → ZMod W)) (R : ℝ) (L : ℕ) (v : Fin n → ℤ) : ℝ :=
  ∑ q ∈ moduli R, ∑ a ∈ shiftedWindow L v, ‖localizedCompleteCubicSum F q W Ω a‖

/-- The localized ten-variable shifted-average target, restricted to the
integer widths used downstream. It is an explicit arithmetic antecedent
for the error reduction, not an assumed literature result. -/
def CleanShiftedAverage (F : MvPolynomial (Fin 10) ℤ) (W : ℕ) (Ω : Set (Fin 10 → ZMod W)) (b : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 1 ≤ C ∧ ∀ B R : ℝ, 1 ≤ B → 1 ≤ R →
    ∀ L : ℕ, 1 ≤ L → ∀ v : Fin 10 → ℤ,
    ‖(fun i => (v i : ℝ))‖ ≤ B →
    shiftedSum F W Ω R L v ≤ C*(B*(L : ℝ)*R)^ε*((L : ℝ)+R^((1:ℝ)/3))^10*R^b

@[simp] theorem shiftedSum_univ_one (F : MvPolynomial (Fin n) ℤ)
    (R : ℝ) (L : ℕ) (v : Fin n → ℤ) :
    shiftedSum F 1 Set.univ R L v = ShiftedCompleteSumWindow.shiftedSum F R L v := by
  simp only [shiftedSum, localizedCompleteCubicSum_univ_one,
    ShiftedCompleteSumWindow.shiftedSum]

@[simp] theorem cleanShiftedAverage_univ_one (F : MvPolynomial (Fin 10) ℤ) (b : ℝ) :
    CleanShiftedAverage F 1 Set.univ b ↔ ShiftedCompleteSumWindow.CleanShiftedAverage F b := by
  simp only [CleanShiftedAverage, ShiftedCompleteSumWindow.CleanShiftedAverage, shiftedSum_univ_one]

theorem truncated_window_sum_le (F : MvPolynomial (Fin n) ℤ) (W : ℕ) (Ω : Set (Fin n → ZMod W))
    (R B : ℝ) (L : ℕ) (v : Fin n → ℤ) :
    (∑ a ∈ LocalSupremumWindow.window (frequencies n B) v (L : ℝ),
      ∑ q ∈ moduli R, ‖localizedCompleteCubicSum F q W Ω a‖) ≤ shiftedSum F W Ω R L v := by
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro q _
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro a ha
    obtain ⟨haS,hav⟩ := (mem_window _ _ _ _).mp ha
    exact (mem_shiftedWindow L v a).mpr ⟨((mem_frequencies B a).mp haS).1,hav⟩
  · exact fun _ _ _ => norm_nonneg _

/-- The exact finite Holder averaging applied to the actual complete sums
and physical gradient-window volumes. The right side is the literal lattice
sum of local maxima, so the completed C7.4 theorem applies directly. -/
theorem weighted_volume_sum_le (G : MvPolynomial (Fin 10) ℤ) (W : ℕ) (Ω : Set (Fin 10 → ZMod W))
    (F : MvPolynomial (Fin 10) ℝ) (K : Set (Fin 10 → ℝ))
    (P R α B δ H : ℝ) (L : ℕ)
    (hshift : ∀ v ∈ centers (frequencies 10 B) L, shiftedSum G W Ω R L v ≤ H) :
    ((2*L+1 : ℕ) : ℝ)^10 *
      (∑ q ∈ moduli R, ∑ a ∈ frequencies 10 B, ‖localizedCompleteCubicSum G q W Ω a‖*
        (volume (GradientWindowScaling.window F K P α (fun i => (a i : ℝ)) δ)).toReal) ≤
      H*AveragedGradientVolume.volumeSum F K P α B δ (L : ℝ) := by
  let S := frequencies 10 B
  let g := fun a : Fin 10 → ℤ =>
    (volume (GradientWindowScaling.window F K P α (fun i => (a i : ℝ)) δ)).toReal
  let f := fun a : Fin 10 → ℤ => ∑ q ∈ moduli R, ‖localizedCompleteCubicSum G q W Ω a‖
  have hf : ∀ a ∈ S, 0 ≤ f a := fun a _ => Finset.sum_nonneg fun q _ => norm_nonneg _
  have hsum : (∑ q ∈ moduli R, ∑ a ∈ S, ‖localizedCompleteCubicSum G q W Ω a‖*g a) =
      ∑ a ∈ S, f a*g a := by rw [Finset.sum_comm]; simp only [f,Finset.sum_mul]
  have hmax : (∑ v ∈ centers S L, maximum S g v (L : ℝ))=
      AveragedGradientVolume.volumeSum F K P α B δ (L : ℝ) := by
    symm
    exact tsum_eq_sum fun v hv => maximum_zero_of_not_mem_centers S g L v hv
  calc
    _ = ((2*L+1 : ℕ) : ℝ)^10 * (∑ a ∈ S, f a*g a) := by rw [hsum]
    _ ≤ ∑ v ∈ centers S L, maximum S g v (L : ℝ)*
        ∑ a ∈ LocalSupremumWindow.window S v (L : ℝ), f a := window_average_holder S f g hf L
    _ ≤ ∑ v ∈ centers S L, maximum S g v (L : ℝ)*H := by
      apply Finset.sum_le_sum
      intro v hv
      exact mul_le_mul_of_nonneg_left
        ((truncated_window_sum_le G W Ω R B L v).trans (hshift v hv))
        (maximum_nonneg S g (fun _ _ => ENNReal.toReal_nonneg) v (L : ℝ))
    _ = H*AveragedGradientVolume.volumeSum F K P α B δ (L : ℝ) := by
      rw [← Finset.sum_mul,hmax,mul_comm]

end CubicTenVariables.LocalizedShiftedWindow
