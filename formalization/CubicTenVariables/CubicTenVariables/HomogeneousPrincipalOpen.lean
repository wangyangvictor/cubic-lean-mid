import CubicTenVariables.ConePrincipalOpen
import CubicTenVariables.PolynomialExponentialFamily
import CubicTenVariables.CubicGradientScaling
import Mathlib.Data.Nat.Factorial.Basic

/-! Elementary bookkeeping for the homogeneous open needed in the cone
trace application: its residual is homogeneous, positive degree excludes
the origin, and one factorial removes all small finite fields. -/

set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.HomogeneousPrincipalOpen
open MvPolynomial PolynomialExponentialFamily
attribute [local instance] MvPolynomial.gradedAlgebra

theorem residual_isHomogeneous {σ K : Type*} [Field K]
    (I : Ideal (MvPolynomial σ K))
    (hI : I.IsHomogeneous (homogeneousSubmodule σ K))
    (g : MvPolynomial σ K) (j : ℕ) (hg : g.IsHomogeneous j) :
    (ConePrincipalOpen.residualIdeal I g).IsHomogeneous (homogeneousSubmodule σ K) := by
  apply hI.sup
  apply Ideal.homogeneous_span
  rintro p (rfl : p = g)
  exact ⟨j,hg⟩

theorem eval_zero_of_positive_degree {n : ℕ} (g : ParameterPolynomial n)
    (j : ℕ) (hj : 0 < j) (hg : g.IsHomogeneous j)
    (K : Type*) [Field K] :
    eval (0 : Fin n → K) (map (Int.castRingHom K) g) = 0 := by
  have he := CubicGradientScaling.homogeneous_eval₂_smul g hg
    (Int.castRingHom K) (0 : Fin n → K) (0 : K)
  simpa only [zero_smul, zero_pow (Nat.ne_of_gt hj), zero_mul,
    eval₂_eq_eval_map] using he

theorem parameterPoint_ne_zero {n t : ℕ} (G : Fin t → ParameterPolynomial n)
    (g : ParameterPolynomial n) (j : ℕ) (hj : 0 < j) (hg : g.IsHomogeneous j)
    (K : Type*) [Field K] [Fintype K] (v : Fin n → K)
    (hv : v ∈ parameterPoints G g K) : v ≠ 0 := by
  intro hzero
  have h := ((mem_parameterPoints G g K v).mp hv).2
  rw [hzero, eval_zero_of_positive_degree g j hj hg K] at h
  exact h rfl

theorem prime_le_card (p : ℕ) [Fact p.Prime]
    (K : Type*) [Field K] [Fintype K] [CharP K p] : p ≤ Fintype.card K := by
  simpa only [ZMod.card] using
    Fintype.card_le_of_injective (ZMod.castHom (dvd_refl p) K) (ZMod.castHom_injective K)

theorem cutoff_lt_card (B p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ B.factorial)
    (K : Type*) [Field K] [Fintype K] [CharP K p] : B < Fintype.card K := by
  have hBp : B < p := by
    by_contra h
    exact hp (Nat.dvd_factorial (Fact.out : p.Prime).pos (by omega))
  exact hBp.trans_le (prime_le_card p K)

end CubicTenVariables.HomogeneousPrincipalOpen
