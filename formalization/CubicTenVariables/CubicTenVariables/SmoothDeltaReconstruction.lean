import CubicTenVariables.SmoothDeltaKernel
import CubicTenVariables.DeltaKernelTruncation
import CubicTenVariables.RamanujanDivisorSwitch
import CubicTenVariables.SmoothDeltaDivisorCancellation

/-! Exact full-line reconstruction for the concrete smooth delta kernel.
The Fourier phase and the primitive numerator sums use precisely the delta
method's original conventions. Uniform analytic estimates are separate. -/

set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.SmoothDeltaReconstruction
open MeasureTheory DeltaMethod DeltaKernelTruncation SmoothDeltaKernel
open RamanujanDivisorSwitch
open scoped BigOperators

/-- Factor the rational part of the literal full-arc phase. -/
theorem fullArc_eq {Q : ℕ} (hQ : 2 ≤ Q) (q a : ℕ) (m : ℤ) :
    fullArc p Q q a m = residueExponential q ((a : ℤ)*m) *
      ((c Q : ℂ)/(Q : ℂ)^2) * (g Q q ((m : ℝ)/(Q : ℝ)^2) : ℂ) := by
  unfold fullArc
  simp_rw [realExponential_arc_phase]
  have he (θ : ℝ) :
      p Q q θ * (residueExponential q ((a : ℤ)*m) *
        realExponential (θ*(m : ℝ))) =
      residueExponential q ((a : ℤ)*m) *
        (p Q q θ * realExponential (θ*(m : ℝ))) := by ring
  simp_rw [he]
  rw [integral_const_mul,integral_integer_phase hQ q m]
  ring

/-- Sum the numerator phases without altering the denominator-one endpoint. -/
theorem fullApproximation_eq {Q : ℕ} (hQ : 2 ≤ Q) (m : ℤ) :
    fullApproximation p Q m = ((c Q : ℂ)/(Q : ℂ)^2) *
      ∑ q ∈ Finset.Icc 1 Q,
        ramanujan q m * (g Q q ((m : ℝ)/(Q : ℝ)^2) : ℂ) := by
  classical
  unfold fullApproximation
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro q hq
  rw [ramanujan_eq_Icc q (Finset.mem_Icc.mp hq).1 m,Finset.sum_mul,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  split_ifs with hcop
  · rw [fullArc_eq hQ q a m]
    ring
  · simp

/-- Exact reconstruction for every integer phase from the concrete smooth
kernel, with no literature or kernel-estimate hypothesis. -/
theorem full_identity {Q : ℕ} (hQ : 2 ≤ Q) (m : ℤ) :
    integerDelta m = fullApproximation p Q m := by
  rw [fullApproximation_eq hQ m,SmoothDeltaDivisorCancellation.normalized_sum_g hQ m]
  rfl

/-- For this concrete kernel, uniform rapid decay is the only remaining
hypothesis needed by the truncated integer-delta identity. -/
theorem delta_of_rapid_decay
    (hd : ∀ k : ℕ, 2 ≤ k → ∃ C : ℝ, 1 ≤ C ∧
      ∀ Q, 2 ≤ Q → ∀ q, 1 ≤ q → q ≤ Q → ∀ θ : ℝ,
        ‖p Q q θ‖ ≤ C*(1+(q : ℝ)*(Q : ℝ)*|θ|)^(-(k : ℝ))) :
    ∀ η : ℝ, 0 < η → ∀ N : ℕ, 1 ≤ N → ∃ C : ℝ, 1 ≤ C ∧
      ∀ Q, 2 ≤ Q → ∀ m : ℤ,
        ‖integerDelta m-deltaApproximation p Q η m‖ ≤ C*(Q : ℝ)^(-(N : ℝ)*η) :=
  delta_of_full_identity p (fun _Q hQ q _ _ => p_integrable hQ q)
    (fun _Q hQ m => full_identity hQ m) hd

end CubicTenVariables.SmoothDeltaReconstruction
