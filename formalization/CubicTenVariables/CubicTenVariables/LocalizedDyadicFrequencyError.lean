import CubicTenVariables.LocalizedFrequencyComparison

/-! The literal summand and finite cutoff for the localized counting error.
Both the normalization and the oscillatory frequency retain lcm(q,W). -/
set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.LocalizedDyadicFrequencyError
open MvPolynomial DyadicFrequencyError LocalSupremumWindow
open scoped BigOperators

def term (G : MvPolynomial (Fin 10) ℤ) (W : ℕ)
    (Ω : Set (Fin 10 → ZMod W)) (w : (Fin 10 → ℝ) → ℝ)
    (P φ : ℝ) (q : ℕ) (v : Fin 10 → ℤ) : ℝ := by
  classical
  exact if v=0 then 0 else ‖localizedCompleteCubicSum G q W Ω v‖*
    frequencyMass G w P φ (Nat.lcm q W) v

def truncatedError (G : MvPolynomial (Fin 10) ℤ) (W : ℕ)
    (Ω : Set (Fin 10 → ZMod W)) (w : (Fin 10 → ℝ) → ℝ)
    (P R φ B : ℝ) : ℝ :=
  ∑ q ∈ moduli R, ((Nat.lcm q W:ℝ)^10)⁻¹ *
    ∑ v ∈ frequencies 10 B, ‖localizedCompleteCubicSum G q W Ω v‖*
      frequencyMass G w P φ (Nat.lcm q W) v

theorem error_eq_sum (G : MvPolynomial (Fin 10) ℤ) (W : ℕ)
    (Ω : Set (Fin 10 → ZMod W)) (w : (Fin 10 → ℝ) → ℝ) (P R φ : ℝ) :
    LocalizedFrequencyComparison.error G W Ω w P R φ =
      ∑ q ∈ moduli R, ((Nat.lcm q W:ℝ)^10)⁻¹ * ∑' v, term G W Ω w P φ q v := rfl

theorem term_nonneg (G : MvPolynomial (Fin 10) ℤ) (W : ℕ)
    (Ω : Set (Fin 10 → ZMod W)) (w : (Fin 10 → ℝ) → ℝ)
    (P φ : ℝ) (q : ℕ) (v : Fin 10 → ℤ) : 0 ≤ term G W Ω w P φ q v := by
  classical
  unfold term
  split_ifs
  · exact le_rfl
  · exact mul_nonneg (norm_nonneg _) (frequencyMass_nonneg G w P φ _ v)

end CubicTenVariables.LocalizedDyadicFrequencyError
