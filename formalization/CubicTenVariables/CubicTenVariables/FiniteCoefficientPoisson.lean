import CubicTenVariables.Literature.ScalarLatticePoisson
import Mathlib.Analysis.Normed.Ring.InfiniteSum

/-! Finite complex coefficients may be combined inside the Fourier sum.
All required absolute convergence is derived from generic Schwartz Poisson;
no cancellation or arithmetic estimate is assumed. -/
set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.FiniteCoefficientPoisson
open ScalarLatticePoisson
open scoped BigOperators
variable {n : ℕ} {X : Type*} [Fintype X]

theorem norm_phase (c : ℝ) (a : Fin n → ℝ) (v : Fin n → ℤ) :
    ‖phase c a v‖=1 := by
  rw [phase,Complex.norm_exp]
  simp

def character (c : ℝ) (a : X → Fin n → ℝ) (b : X → ℂ) (v : Fin n → ℤ) : ℂ :=
  ∑ x, b x*phase c (a x) v

theorem summable_norm_character (lit : Literature.SteinShakarchi2011Poisson)
    (f : SchwartzMap (Fin n → ℝ) ℂ) (c : ℝ) (hc : 0 < c)
    (a : X → Fin n → ℝ) (b : X → ℂ) :
    Summable (fun v : Fin n → ℤ =>
      ‖character c a b v * fourier f (fun i => (v i:ℝ)/c)‖) := by
  have hf := (lit n f c hc 0).2.1
  have hb (v : Fin n → ℤ) : ‖character c a b v‖ ≤ ∑ x, ‖b x‖ := by
    apply (norm_sum_le _ _).trans
    simp only [norm_mul,norm_phase,mul_one]
    exact le_rfl
  exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun v => by rw [norm_mul]; exact mul_le_mul_of_nonneg_right (hb v) (norm_nonneg _))
    (hf.mul_left (∑ x, ‖b x‖))

/-- Arbitrary finite complex coefficients remain inside the dual series. -/
theorem weighted_identity (lit : Literature.SteinShakarchi2011Poisson)
    (f : SchwartzMap (Fin n → ℝ) ℂ) (c : ℝ) (hc : 0 < c)
    (a : X → Fin n → ℝ) (b : X → ℂ) :
    (∑ x, b x * ∑' z : Fin n → ℤ, f (point c (a x) z)) =
      ((c:ℂ)^n)⁻¹ * ∑' v : Fin n → ℤ,
        character c a b v * fourier f (fun i => (v i:ℝ)/c) := by
  classical
  have hf := (lit n f c hc 0).2.1
  have hs (x : X) : Summable (fun v : Fin n → ℤ =>
      b x*(phase c (a x) v * fourier f (fun i => (v i:ℝ)/c))) := by
    apply Summable.mul_left
    apply Summable.of_norm
    simpa only [norm_mul,norm_phase,one_mul] using hf
  simp_rw [(lit n f c hc _).2.2]
  calc
    _ = ((c:ℂ)^n)⁻¹ * ∑ x, b x * ∑' v : Fin n → ℤ,
        phase c (a x) v * fourier f (fun i => (v i:ℝ)/c) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      ring
    _ = _ := by
      congr 1
      simp only [← tsum_mul_left]
      rw [← Summable.tsum_finsetSum (s := Finset.univ) (fun x _ => hs x)]
      apply tsum_congr
      intro v
      simp only [character,Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro x _
      ring

end CubicTenVariables.FiniteCoefficientPoisson
