import CubicTenVariables.TerminalLowBound
import CubicTenVariables.TerminalHighBound
import CubicTenVariables.SmithProfileHighMultiplicity
import CubicTenVariables.HessianSmithProfile

/-!
The complete terminal Smith bound for the actual attained finite maximum.
One integral Hessian diagonal is constructed before all primes, modulus
exponents and terminal coefficients. The source's exact real exponent and
piecewise rational penalty are retained. The low branch includes p=2;
the high branch requires p!=2 through the proved quadratic support argument.
Only p^a|A is required; the source's exact valuation assumption is stronger.
-/

noncomputable section
namespace CubicTenVariables.TerminalSmithBound
open MvPolynomial HessianTheorem11 TerminalCubicSum PrimePowerKernelProfile
open SmithProfileNumerics SmithProfileMultiplicity
open scoped BigOperators

/-- The full manuscript profile inequality, first with a displayed actual
integral diagonalization to preserve the same diagonal in both branches. -/
theorem terminalMax_le_profile_of_diagonalization {n : ℕ}
    (F : MvPolynomial (Fin n) ℤ) (hF : F.IsHomogeneous 3)
    (y : Fin n → ℤ) (U V : (Matrix (Fin n) (Fin n) ℤ)ˣ) (d : Fin n → ℤ)
    (hD : (U : Matrix (Fin n) (Fin n) ℤ) * hessian F y * V = Matrix.diagonal d)
    (p : ℕ) [NeZero p] (hp : p.Prime) (a t : ℕ)
    (hcase : t ≤ a ∨ p ≠ 2) (A : ℤ) (hA : ((p^a : ℕ) : ℤ) ∣ A) :
    terminalMax (p^t) (map (Int.castRingHom (ZMod (p^t))) F)
      (A : ZMod (p^t)) (fun i => (y i : ZMod (p^t))) ≤
      Real.rpow (p : ℝ) (((n*t : ℕ) : ℝ) - ∑ i ∈ Finset.range a,
        (penaltyWeight a t i : ℝ) *
          (profile (fun ν => truncatedValuation p a (d ν)) i : ℝ)) := by
  by_cases hta : t ≤ a
  · exact TerminalLowBound.terminalMax_primePower_le_profile F hF y U V d hD
      p hp a t hta A hA
  · have hat : a < t := by omega
    have hp2 : p ≠ 2 := hcase.resolve_left hta
    have hb := TerminalHighBound.terminalMax_primePower_le_profile F hF y U V d hD
      p hp hp2 a t hat.le A hA
    rwa [SmithProfileHighMultiplicity.high_factor_eq_rpow (p : ℝ)
      (by exact_mod_cast hp.pos) (fun ν => truncatedValuation p a (d ν))
      (fun ν => truncatedValuation_le p a (d ν)) hat] at hb

/-- One actual integral diagonal is constructed before all primes, levels,
and terminal coefficients. No Smith decomposition is an input. -/
theorem exists_diagonalization_and_terminal_bound {n : ℕ}
    (F : MvPolynomial (Fin n) ℤ) (hF : F.IsHomogeneous 3) (y : Fin n → ℤ) :
    ∃ (U V : (Matrix (Fin n) (Fin n) ℤ)ˣ) (d : Fin n → ℤ),
      (U : Matrix (Fin n) (Fin n) ℤ) * hessian F y * V = Matrix.diagonal d ∧
      ∀ (p : ℕ) (hp : p.Prime) (a t : ℕ) (A : ℤ),
        ((p^a : ℕ) : ℤ) ∣ A → (t ≤ a ∨ p ≠ 2) →
        letI : NeZero p := ⟨hp.ne_zero⟩
        terminalMax (p^t) (map (Int.castRingHom (ZMod (p^t))) F)
          (A : ZMod (p^t)) (fun i => (y i : ZMod (p^t))) ≤
          Real.rpow (p : ℝ) (((n*t : ℕ) : ℝ) - ∑ i ∈ Finset.range a,
            (penaltyWeight a t i : ℝ) *
              (profile (fun ν => truncatedValuation p a (d ν)) i : ℝ)) := by
  obtain ⟨U,V,d,hD⟩ := MatrixSmithExistence.exists_integer_diagonalization (hessian F y)
  refine ⟨U,V,d,hD,?_⟩
  intro p hp a t A hA hcase
  letI : NeZero p := ⟨hp.ne_zero⟩
  exact terminalMax_le_profile_of_diagonalization F hF y U V d hD p hp a t hcase A hA

/-- The literal terminal bound now uses precisely the finite monotone
ten-variable profile consumed by the already proved numerical optimization. -/
theorem terminalMax_ten_le_profile_penalty
    (F : MvPolynomial (Fin 10) ℤ) (hF : F.IsHomogeneous 3)
    (y : Fin 10 → ℤ) (U V : (Matrix (Fin 10) (Fin 10) ℤ)ˣ) (d : Fin 10 → ℤ)
    (hD : (U : Matrix (Fin 10) (Fin 10) ℤ) * hessian F y * V = Matrix.diagonal d)
    (p : ℕ) [NeZero p] (hp : p.Prime) (a t : ℕ)
    (hcase : t ≤ a ∨ p ≠ 2) (A : ℤ) (hA : ((p^a : ℕ) : ℤ) ∣ A) :
    terminalMax (p^t) (map (Int.castRingHom (ZMod (p^t))) F)
      (A : ZMod (p^t)) (fun i => (y i : ZMod (p^t))) ≤
      Real.rpow (p : ℝ) (((10*t : ℕ) : ℝ) -
        (penalty (HessianSmithProfile.ofDiagonal p a d) t : ℝ)) := by
  rw [HessianSmithProfile.penalty_ofDiagonal_real]
  exact terminalMax_le_profile_of_diagonalization F hF y U V d hD p hp a t hcase A hA

end CubicTenVariables.TerminalSmithBound
