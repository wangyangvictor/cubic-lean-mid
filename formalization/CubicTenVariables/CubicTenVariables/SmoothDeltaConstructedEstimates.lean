import CubicTenVariables.SmoothDeltaAmplitudeIntegral
import CubicTenVariables.SmoothDeltaReconstruction

/-! The boundedness and truncated integer identity of the constructed smooth
delta kernel. Every analytic premise of the intermediate adapters is now
discharged for these two conclusions. The near-one estimate is separate. -/

set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.SmoothDeltaConstructedEstimates
open DeltaMethod SmoothDeltaKernel

/-- One absolute constant bounds the entire concrete kernel family. -/
theorem bounded : ∃ C : ℝ, 1 ≤ C ∧
    ∀ Q, 2 ≤ Q → ∀ q, 1 ≤ q → q ≤ Q → ∀ θ : ℝ, ‖p Q q θ‖ ≤ C := by
  obtain ⟨C,hC,hb⟩ := SmoothDeltaAmplitudeIntegral.rapid_decay 0
  refine ⟨C,hC,?_⟩
  intro Q hQ q hq hqQ θ
  simpa only [Nat.cast_zero,neg_zero,Real.rpow_zero,mul_one] using hb Q hQ q hq hqQ θ

/-- The literal truncated delta identity, for every integer, every positive
truncation parameter and every positive integral saving order. -/
theorem delta : ∀ η : ℝ, 0 < η → ∀ N : ℕ, 1 ≤ N → ∃ C : ℝ, 1 ≤ C ∧
    ∀ Q, 2 ≤ Q → ∀ m : ℤ,
      ‖integerDelta m-deltaApproximation p Q η m‖ ≤ C*(Q : ℝ)^(-(N : ℝ)*η) :=
  SmoothDeltaReconstruction.delta_of_rapid_decay
    (fun k _ => SmoothDeltaAmplitudeIntegral.rapid_decay k)

end CubicTenVariables.SmoothDeltaConstructedEstimates
