import CubicTenVariables.FlexibleLifting
import CubicTenVariables.CubicQuadraticGauss

/-! When T divides A, the terminal cubic term vanishes modulo T.
The actual attained terminal maximum is therefore bounded by the square
root of T^n times the actual Hessian-kernel cardinality, even at 2.
This supplies a literal weighted square-full lifting bound before the
remaining geometric kernel moments are estimated. -/

noncomputable section
namespace CubicTenVariables.QuadraticTerminalBound
open MvPolynomial HessianTheorem11 TerminalCubicSum SecondLiftSum FlexibleLifting
open scoped BigOperators

theorem terminalMax_zero_sq_le (T n : ℕ) [NeZero T]
    (F : MvPolynomial (Fin n) (ZMod T)) (hF : F.IsHomogeneous 3)
    (y : Fin n → ZMod T) :
    (terminalMax T F 0 y)^2 ≤
      (T : ℝ)^n * Nat.card {h : Fin n → ZMod T // (hessian F y).mulVec h = 0} := by
  obtain ⟨u, ell, he⟩ := terminalMax_attained T F 0 y
  rw [he]
  simpa only [terminalSum, terminalPhase, mul_zero, zero_mul, add_zero, zero_add, add_comm] using
    CubicQuadraticGauss.norm_mixed_quadraticAt_sum_sq_le T n F hF y u ell

theorem terminalMax_zero_le_sqrt (T n : ℕ) [NeZero T]
    (F : MvPolynomial (Fin n) (ZMod T)) (hF : F.IsHomogeneous 3)
    (y : Fin n → ZMod T) :
    terminalMax T F 0 y ≤ Real.sqrt
      ((T : ℝ)^n * Nat.card {h : Fin n → ZMod T // (hessian F y).mulVec h = 0}) :=
  Real.le_sqrt_of_sq_le (terminalMax_zero_sq_le T n F hF y)

/-- The kernel consists of actual residue vectors killed by the actual
Hessian of the reduced integer polynomial at the chosen base point. -/
def residueKernelRoot {n : ℕ} (F : MvPolynomial (Fin n) ℤ)
    (A T : ℕ) [NeZero T] (y : Fin n → Fin A) : ℝ :=
  Real.sqrt ((T : ℝ)^n * Nat.card {h : Fin n → ZMod T //
    (hessian (map (Int.castRingHom (ZMod T)) F)
      (fun i => ((y i).val : ZMod T))).mulVec h = 0})

theorem residueTerminalMax_le_kernelRoot {n : ℕ} (F : MvPolynomial (Fin n) ℤ)
    (hF : F.IsHomogeneous 3) (A T : ℕ) [NeZero T] (hTA : T ∣ A)
    (y : Fin n → Fin A) :
    residueTerminalMax F A T y ≤ residueKernelRoot F A T y := by
  have hz : (A : ZMod T) = 0 := by exact_mod_cast (ZMod.natCast_eq_zero_iff A T).mpr hTA
  unfold residueTerminalMax residueKernelRoot
  rw [hz]
  exact terminalMax_zero_le_sqrt T n _ (hF.map _) _

/-- Weighted lifting with its terminal factor replaced by a literal
Hessian-kernel sum. No profile-count or Smith-form premise is used. -/
theorem weighted_completeCubicSum_le_kernel {n : ℕ} (F : MvPolynomial (Fin n) ℤ)
    (hF : F.IsHomogeneous 3) (A T : ℕ) [NeZero A] [NeZero T] (hTA : T ∣ A)
    (V : Finset (Fin n → ℤ)) (w : (Fin n → ℤ) → ℝ)
    (hw : ∀ v ∈ V, 0 ≤ w v) :
    (∑ v ∈ V, w v * ‖completeCubicSum F (A^2*T) v‖) ≤
      (A : ℝ)^n * (Nat.totient (A^2*T) : ℝ) * WeightedResidueMaximum.maximum A V w *
        ∑ y : Fin n → Fin A, if (A : ℤ) ∣ eval (integerVector y) F then
          residueKernelRoot F A T y else 0 := by
  classical
  apply (weighted_completeCubicSum_le F hF A T V w hw).trans
  apply mul_le_mul_of_nonneg_left
  · unfold zeroFiberTerminalTotal
    apply Finset.sum_le_sum
    intro y _
    split_ifs
    · exact residueTerminalMax_le_kernelRoot F hF A T hTA y
    · rfl
  · exact mul_nonneg (mul_nonneg (by positivity) (by positivity))
      (WeightedResidueMaximum.maximum_nonneg A V w hw)

end CubicTenVariables.QuadraticTerminalBound
