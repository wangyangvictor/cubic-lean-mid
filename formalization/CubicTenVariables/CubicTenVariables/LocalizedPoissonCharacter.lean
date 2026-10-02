import CubicTenVariables.PeriodicCoefficientPoisson
import CubicTenVariables.LocalizedPeriodicPhase

/-! Exact identification of the finite character arising from scalar-lattice
Poisson with the actual localized complete cubic sum. These algebraic
identities require no Poisson or literature input and include modulus one. -/
set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.LocalizedPoissonCharacter
open MvPolynomial
open scoped BigOperators
variable {n : ℕ}

/-- Translation by an integer representative gives the positive residue
character, with exactly the scalar-lattice denominator. -/
theorem phase_eq_residue (ℓ : ℕ) (x : Fin n → Fin ℓ) (v : Fin n → ℤ) :
    ScalarLatticePoisson.phase (ℓ : ℝ)
      (PeriodicCoefficientPoisson.realRepresentative x) v =
      residueExponential ℓ (∑ i, v i * (x i).val) := by
  unfold ScalarLatticePoisson.phase PeriodicCoefficientPoisson.realRepresentative
    residueExponential
  congr 1
  push_cast
  ring

/-- The complete sum produced by the literal periodic coefficient retains
both moduli and every local residue restriction. -/
theorem character_eq_localizedCompleteCubicSum
    (G : MvPolynomial (Fin n) ℤ) (q W : ℕ)
    (Ω : Set (Fin n → ZMod W)) (v : Fin n → ℤ) :
    FiniteCoefficientPoisson.character (Nat.lcm q W : ℝ)
      PeriodicCoefficientPoisson.realRepresentative
      (fun x : Fin n → Fin (Nat.lcm q W) =>
        LocalizedPeriodicPhase.coefficient G q W Ω
          (IntegerLatticeResidues.representative x)) v =
      localizedCompleteCubicSum G q W Ω v := by
  simp only [FiniteCoefficientPoisson.character, phase_eq_residue]
  exact LocalizedPeriodicPhase.finite_fourier_eq G q W Ω v

end CubicTenVariables.LocalizedPoissonCharacter
