import CubicTenVariables.LocalizedZeroCRT

/-! Multiplicativity of the actual ordinary singular-series coefficients.
Zero frequency needs no homogeneity assumption on the integer polynomial.
The zero and unit modulus conventions are retained. -/

set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.OrdinarySeriesMultiplicativity
open MvPolynomial

theorem mul {n : ℕ} (F : MvPolynomial (Fin n) ℤ)
    (a b : ℕ) (hab : a.Coprime b) :
    singularSeriesTerm F (a*b) = singularSeriesTerm F a * singularSeriesTerm F b := by
  by_cases ha : a = 0
  · simp [ha]
  by_cases hb : b = 0
  · simp [hb]
  letI : NeZero a := ⟨ha⟩
  letI : NeZero b := ⟨hb⟩
  simpa only [localizedSingularSeriesTerm_univ_one] using
    LocalizedZeroCRT.localized_seriesTerm_mul_outside F a b 1
      (by simpa only [Nat.mul_one] using hab) Set.univ

theorem norm_mul {n : ℕ} (F : MvPolynomial (Fin n) ℤ)
    (a b : ℕ) (hab : a.Coprime b) :
    ‖singularSeriesTerm F (a*b)‖ = ‖singularSeriesTerm F a‖ * ‖singularSeriesTerm F b‖ := by
  rw [mul F a b hab, _root_.norm_mul]

end CubicTenVariables.OrdinarySeriesMultiplicativity
