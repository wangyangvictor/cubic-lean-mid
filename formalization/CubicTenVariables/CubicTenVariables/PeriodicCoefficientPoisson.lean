import CubicTenVariables.FiniteCoefficientPoisson
import CubicTenVariables.IntegerLatticeResidues

/-! Poisson summation with an actual lattice-periodic complex coefficient.
The input is generic Schwartz Poisson; residue regrouping is proved. -/
set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.PeriodicCoefficientPoisson
open ScalarLatticePoisson IntegerLatticeResidues
open scoped BigOperators
variable {n : ℕ}

def realRepresentative {ℓ : ℕ} (b : Fin n → Fin ℓ) : Fin n → ℝ :=
  fun i => ((b i).val:ℝ)

theorem cast_assemble {ℓ : ℕ} (b : Fin n → Fin ℓ) (z : Fin n → ℤ) :
    (fun i => (assemble b z i:ℝ))=point (ℓ:ℝ) (realRepresentative b) z := by
  ext i
  simp only [assemble,representative,point,realRepresentative,Int.cast_add,
    Int.cast_mul,Int.cast_natCast]

/-- The periodic lattice sum and finite Fourier coefficients have exactly
the scalar-lattice covolume factor. Genuine summability is explicit. -/
theorem identity (lit : Literature.SteinShakarchi2011Poisson)
    (f : SchwartzMap (Fin n → ℝ) ℂ) (ℓ : ℕ) (hℓ : 0 < ℓ)
    (b : (Fin n → ℤ) → ℂ)
    (hper : ∀ r : Fin n → Fin ℓ, ∀ z : Fin n → ℤ,
      b (assemble r z)=b (representative r))
    (hs : Summable (fun x : Fin n → ℤ => b x*f (fun i => (x i:ℝ)))) :
    (∑' x : Fin n → ℤ, b x*f (fun i => (x i:ℝ))) =
      ((ℓ:ℂ)^n)⁻¹ * ∑' v : Fin n → ℤ,
        FiniteCoefficientPoisson.character (ℓ:ℝ) realRepresentative
          (fun r : Fin n → Fin ℓ => b (representative r)) v *
        fourier f (fun i => (v i:ℝ)/(ℓ:ℝ)) := by
  rw [IntegerLatticeResidues.tsum_eq_sum_tsum n ℓ hℓ _ hs]
  simp_rw [hper,cast_assemble,tsum_mul_left]
  exact FiniteCoefficientPoisson.weighted_identity lit f (ℓ:ℝ)
    (by exact_mod_cast hℓ) realRepresentative (fun r => b (representative r))

end CubicTenVariables.PeriodicCoefficientPoisson
