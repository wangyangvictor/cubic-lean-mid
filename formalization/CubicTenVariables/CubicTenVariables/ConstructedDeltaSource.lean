import CubicTenVariables.SmoothDeltaNearOne
import CubicTenVariables.SmoothDeltaConstructedEstimates

/-! The original scalar delta-kernel proposition, supplied by an actual
constructed family. The Q=1 and counting adapters retain every original
conclusion while discharging the Marmon--Vishe premise internally. -/

set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.ConstructedDeltaSource
open MvPolynomial MeasureTheory DeltaMethod
open scoped BigOperators ContDiff

/-- Every field of the original kernel interface is proved for the same
explicit family, with its original quantifier order and parameter ranges. -/
theorem kernel_estimates : KernelEstimates 2 SmoothDeltaKernel.p where
  smooth := fun Q _ q _ _ => SmoothDeltaKernel.p_contDiff Q q
  bounded := SmoothDeltaConstructedEstimates.bounded
  near_one := SmoothDeltaNearOne.exists_bound
  delta := SmoothDeltaConstructedEstimates.delta

/-- A proof of the existing literature proposition, not a new axiom. -/
theorem proved : Literature.MarmonVishe2019Proposition12 :=
  ⟨SmoothDeltaKernel.p,kernel_estimates⟩

theorem exists_source_kernels  :
    ∃ p : ℕ → ℕ → ℝ → ℂ, KernelEstimates 1 p :=
  DeltaMethod.exists_source_kernels proved

theorem exists_localized_count_error {n : ℕ}
    
    (F : MvPolynomial (Fin n) ℤ) (w : (Fin n → ℝ) → ℝ)
    (A W : ℕ) (Ω : Set (Fin n → ZMod W)) :
    ∃ p : ℕ → ℕ → ℝ → ℂ, KernelEstimates 1 p ∧
      ∀ η : ℝ, 0 < η → ∀ N : ℕ, 1 ≤ N → ∃ C : ℝ, 1 ≤ C ∧
        ∀ P Q : ℕ, 1 ≤ Q →
          ‖(localizedWeightedCount F w A P W Ω : ℂ) -
            ∑ q ∈ Finset.Icc 1 Q, ∑ a ∈ Finset.Icc 1 q, if Nat.Coprime a q then
              ∫ θ in arc Q q η, p Q q θ *
                localizedGeneratingSum F w A P W Ω ((a : ℝ)/(q : ℝ)+θ) else 0‖ ≤
          (∑ x ∈ integerBox n (A*P), |countingWeight w P W Ω x|) *
            (C*(Q : ℝ)^(-(N : ℝ)*η)) :=
  DeltaMethod.exists_localized_count_error proved F w A W Ω

theorem exists_localized_count_power_error {n : ℕ}
    
    (F : MvPolynomial (Fin n) ℤ) (w : (Fin n → ℝ) → ℝ)
    (M : ℝ) (hM : ∀ y, |w y| ≤ M)
    (A W : ℕ) (Ω : Set (Fin n → ZMod W)) :
    ∃ p : ℕ → ℕ → ℝ → ℂ, KernelEstimates 1 p ∧
      ∀ η : ℝ, 0 < η → ∀ N : ℕ, 1 ≤ N → ∃ C : ℝ, 1 ≤ C ∧
        ∀ P Q : ℕ, 1 ≤ P → 1 ≤ Q →
          ‖(localizedWeightedCount F w A P W Ω : ℂ) -
            ∑ q ∈ Finset.Icc 1 Q, ∑ a ∈ Finset.Icc 1 q, if Nat.Coprime a q then
              ∫ θ in arc Q q η, p Q q θ *
                localizedGeneratingSum F w A P W Ω ((a : ℝ)/(q : ℝ)+θ) else 0‖ ≤
          C*(P : ℝ)^n*(Q : ℝ)^(-(N : ℝ)*η) :=
  DeltaMethod.exists_localized_count_power_error proved F w M hM A W Ω

theorem exists_source_count_expansion {n : ℕ}
    
    (F : MvPolynomial (Fin n) ℤ) (w : (Fin n → ℝ) → ℝ) (A : ℕ)
    (hw : WeightSupportedInBox w A) (hw0 : w 0=0)
    (M : ℝ) (hM : ∀ y, |w y| ≤ M) :
    ∃ p : ℕ → ℕ → ℝ → ℂ, KernelEstimates 1 p ∧
      ∀ η : ℝ, 0 < η → ∀ N : ℕ, 1 ≤ N → ∃ C : ℝ, 1 ≤ C ∧
        ∀ P Q : ℕ, 1 ≤ P → 1 ≤ Q →
          ‖(((∑' x : Fin n → ℤ, if eval x F=0 then w (scaledIntegerPoint P x) else 0) : ℝ) : ℂ) -
            ∑ q ∈ Finset.Icc 1 Q, ∑ a ∈ Finset.Icc 1 q, if Nat.Coprime a q then
              ∫ θ in arc Q q η, p Q q θ *
                (∑' x : Fin n → ℤ, (w (scaledIntegerPoint P x) : ℂ)*
                  realExponential (((a : ℝ)/(q : ℝ)+θ)*(eval x F : ℝ))) else 0‖ ≤
          C*(P : ℝ)^n*(Q : ℝ)^(-(N : ℝ)*η) :=
  DeltaMethod.exists_source_count_expansion proved F w A hw hw0 M hM

end CubicTenVariables.ConstructedDeltaSource
