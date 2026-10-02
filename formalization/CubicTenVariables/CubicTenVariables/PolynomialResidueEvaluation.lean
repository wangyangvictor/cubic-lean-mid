import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.Algebra.MvPolynomial.Eval

/-! Literal evaluation of integral polynomials commutes with reduction modulo
prime powers. In particular the residue value is independent of the chosen
integral lift. -/

namespace CubicTenVariables.PolynomialResidueEvaluation

open MvPolynomial

variable {p : ℕ} [Fact p.Prime] {ι : Type*}

theorem toZModPow_eval₂_int (F : MvPolynomial ι ℤ) (s : ℕ) (z : ι → ℤ_[p]) :
    PadicInt.toZModPow s (eval₂ (Int.castRingHom ℤ_[p]) z F) =
      eval₂ (Int.castRingHom (ZMod (p ^ s))) (fun i => PadicInt.toZModPow s (z i)) F := by
  rw [eval₂_comp_left]
  congr 1
  ext a
  simp

theorem toZModPow_eval₂_int_of_lift (F : MvPolynomial ι ℤ) (s : ℕ)
    (z : ι → ℤ_[p]) (v : ι → ZMod (p ^ s))
    (hv : ∀ i, PadicInt.toZModPow s (z i) = v i) :
    PadicInt.toZModPow s (eval₂ (Int.castRingHom ℤ_[p]) z F) =
      eval₂ (Int.castRingHom (ZMod (p ^ s))) v F := by
  rw [toZModPow_eval₂_int, funext hv]

theorem toZModPow_eval₂_int_eq_of_congr (F : MvPolynomial ι ℤ) (s : ℕ)
    (z w : ι → ℤ_[p])
    (hzw : ∀ i, PadicInt.toZModPow s (z i) = PadicInt.toZModPow s (w i)) :
    PadicInt.toZModPow s (eval₂ (Int.castRingHom ℤ_[p]) z F) =
      PadicInt.toZModPow s (eval₂ (Int.castRingHom ℤ_[p]) w F) := by
  rw [toZModPow_eval₂_int, toZModPow_eval₂_int, funext hzw]

end CubicTenVariables.PolynomialResidueEvaluation
