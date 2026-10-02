import CubicTenVariables.DeltaMethod
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-! Exact change of variables on the original delta-method arcs.
The physical scale is real and positive; the modulus parameters remain natural.
No limit, convergence or literature estimate is assumed in these identities. -/
set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.RescaledDeltaArc
open MeasureTheory

def domain (P : ℝ) (Q q : ℕ) (η : ℝ) : Set ℝ :=
  {β | |β| < P^3*((q:ℝ)*(Q:ℝ))^(-1+η)}

def integral (p : ℕ → ℕ → ℝ → ℂ) (P : ℝ) (Q q : ℕ) (η : ℝ)
    (J : ℝ → ℂ) : ℂ :=
  ∫ β in domain P Q q η, p Q q (β/P^3)*J β

theorem measurableSet_domain (P : ℝ) (Q q : ℕ) (η : ℝ) :
    MeasurableSet (domain P Q q η) :=
  (isOpen_lt continuous_abs continuous_const).measurableSet

theorem mul_mem_domain (P : ℝ) (hP : 0 < P) (Q q : ℕ) (η θ : ℝ) :
    P^3*θ ∈ domain P Q q η ↔ θ ∈ DeltaMethod.arc Q q η := by
  change |P^3*θ| < P^3*((q:ℝ)*(Q:ℝ))^(-1+η) ↔ _
  rw [abs_mul,abs_of_pos (pow_pos hP 3)]
  exact mul_lt_mul_iff_right₀ (pow_pos hP 3)

/-- Rescaling retains the exact clipped open arc and its full Jacobian. -/
theorem original_eq (p : ℕ → ℕ → ℝ → ℂ) (P : ℝ) (hP : 0 < P)
    (Q q : ℕ) (η : ℝ) (J : ℝ → ℂ) :
    (∫ θ in DeltaMethod.arc Q q η, p Q q θ*J (P^3*θ)) =
      (P^3)⁻¹ • integral p P Q q η J := by
  classical
  let f : ℝ → ℂ := (domain P Q q η).indicator (fun β => p Q q (β/P^3)*J β)
  have harc : MeasurableSet (DeltaMethod.arc Q q η) :=
    (isOpen_lt continuous_abs continuous_const).measurableSet
  have he : (DeltaMethod.arc Q q η).indicator (fun θ => p Q q θ*J (P^3*θ)) =
      fun θ => f (P^3*θ) := by
    funext θ
    by_cases hθ : θ ∈ DeltaMethod.arc Q q η
    · have hβ := (mul_mem_domain P hP Q q η θ).mpr hθ
      simp [f,hθ,hβ,pow_ne_zero 3 hP.ne']
    · have hβ := (mul_mem_domain P hP Q q η θ).not.mpr hθ
      simp [f,hθ,hβ]
  rw [← integral_indicator harc,he,Measure.integral_comp_mul_left]
  rw [abs_of_pos (inv_pos.mpr (pow_pos hP 3))]
  congr 1
  exact integral_indicator (measurableSet_domain P Q q η)

end CubicTenVariables.RescaledDeltaArc
