import CubicTenVariables.LocalizedClippedFrequency
import CubicTenVariables.LocalizedNonzeroFrequencySaving
import CubicTenVariables.ClippedPhaseRange

/-! The genuine clipped dyadic contribution inherits the existing localized
power saving. All phase widths are covered: inadmissible widths give empty
clipped arcs. The chosen kernel precedes the constants and all scales.
This is a block estimate; summing the blocks and treating q=1 remain separate. -/
set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.LocalizedClippedSaving
open MvPolynomial DeltaMethod RealRegularGradientChart DyadicFrequencyError
open LocalizedShiftedWindow LocalizedClippedFrequency
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem block_eq_zero_of_not_le (G : MvPolynomial (Fin 10) ℤ)
    (w : (Fin 10 → ℝ) → ℝ) (P Q W : ℕ) (Ω : Set (Fin 10 → ZMod W))
    (R φ η : ℝ) (p : ℕ → ℕ → ℝ → ℂ)
    (hP : 0 < P) (hR : 1 ≤ R) (hη : η ≤ 1)
    (hQ : (Q:ℝ)=(P:ℝ)^((3:ℝ)/2))
    (hφ : ¬ φ ≤ (R*(P:ℝ)^((3:ℝ)/2))^(-1+η)) :
    block G w P Q W Ω R φ η p=0 := by
  apply Finset.sum_eq_zero
  intro q hq
  by_cases hqQ : q ≤ Q
  · simp only [if_pos hqQ]
    rw [ClippedPhaseRange.intersection_eq_empty_of_not_le (P:ℝ) R φ η Q q
      (by exact_mod_cast hP) hR hη hQ hq hφ]
    simp
  · simp only [if_neg hqQ]

/-- Uniform power saving for every actual clipped block. The arithmetic
shifted-average hypothesis remains explicit and is not proved here. -/
theorem exists_power_saving 
    (G : MvPolynomial (Fin 10) ℤ) (hG : G.IsHomogeneous 3)
    (D : Data (map (Int.castRingHom ℝ) G)) (W : ℕ) (hW : 0 < W)
    (Ω : Set (Fin 10 → ZMod W)) (b : ℝ) (hb : b < 20/3)
    (hshift : CleanShiftedAverage G W Ω b)
    (p : ℕ → ℕ → ℝ → ℂ) (hp : KernelEstimates 1 p) :
    ∃ δ η₀ C P₀ : ℝ, 0 < δ ∧ 0 < η₀ ∧ η₀ ≤ 1 ∧ 1 ≤ C ∧ 4 ≤ P₀ ∧
      ∀ P Q : ℕ, P₀ ≤ (P:ℝ) → 1 ≤ Q → (Q:ℝ)=(P:ℝ)^((3:ℝ)/2) →
      ∀ R φ η : ℝ, 1 ≤ R → R ≤ (P:ℝ)^((3:ℝ)/2) → 0 < φ →
        0 ≤ η → η ≤ η₀ →
        ‖block G D.weight.weight P Q W Ω R φ η p‖ ≤ C*(P:ℝ)^(7-δ) := by
  obtain ⟨δ,η₀,C,P₀,hδ,hη₀,hC,hP₀,hbound⟩ :=
    LocalizedNonzeroFrequencySaving.exists_power_saving G hG D W hW Ω b hb hshift
  obtain ⟨K,hK,hkernel⟩ := hp.bounded
  refine ⟨δ,min η₀ 1,K*C,P₀,hδ,lt_min hη₀ zero_lt_one,min_le_right _ _,
    one_le_mul_of_one_le_of_one_le hK hC,hP₀,?_⟩
  intro P Q hP hQ hQP R φ η hR hRP hφ hη hηmax
  have hPpos : 0 < P := by
    have : (0:ℝ) < P := by linarith
    exact_mod_cast this
  have hη1 : η ≤ 1 := hηmax.trans (min_le_right _ _)
  by_cases hphase : φ ≤ (R*(P:ℝ)^((3:ℝ)/2))^(-1+η)
  · obtain ⟨hsum,he⟩ := hbound (P:ℝ) R φ η hP hR hRP hφ hη
      (hηmax.trans (min_le_left _ _)) hphase
    have hqpos (q : ℕ) (hq : q ∈ moduli R) : 1 ≤ q := by
      have hqR := (mem_moduli R q).mp hq
      exact_mod_cast (le_of_lt (lt_of_le_of_lt hR hqR.1))
    have hc := block_bound G D.weight.weight D.weight.smooth.continuous D.weight.compact
      P Q W hPpos Ω R φ η p K (zero_le_one.trans hK)
      (fun q hq hqQ => (hp.smooth Q hQ q (hqpos q hq) hqQ).continuous.measurable)
      (fun q hq hqQ θ _ => hkernel Q hQ q (hqpos q hq) hqQ θ) hsum
    exact hc.trans (by simpa only [mul_assoc] using
      mul_le_mul_of_nonneg_left he (zero_le_one.trans hK))
  · rw [block_eq_zero_of_not_le G D.weight.weight P Q W Ω R φ η p
      hPpos hR hη1 hQP hphase,norm_zero]
    exact mul_nonneg (by positivity) (Real.rpow_nonneg (Nat.cast_nonneg P) _)

end CubicTenVariables.LocalizedClippedSaving
