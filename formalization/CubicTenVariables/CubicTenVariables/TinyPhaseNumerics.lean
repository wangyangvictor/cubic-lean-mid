import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-! Exact ten-variable normalization of the elementary tiny-phase bound.
At width P^(-20) and Q=P^(3/2), its factor τ Q² P¹⁰ is P^(-7).
No analytic or literature estimate is assumed here. -/
set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.TinyPhaseNumerics

/-- The exact power of P in the ten-variable tiny-phase bound. -/
theorem normalization (P Q : ℝ) (hP : 0 < P) (hQ : Q=P^((3 : ℝ)/2)) :
    P^(-20 : ℝ)*Q^2*P^10 = P^(-7 : ℝ) := by
  rw [hQ, ← Real.rpow_mul_natCast hP.le ((3 : ℝ)/2) 2,
    ← Real.rpow_natCast P 10, ← Real.rpow_add hP,
    ← Real.rpow_add hP]
  norm_num

/-- This is exactly the factor ordering produced by the full-modulus
short-interval estimate, with all fixed constants retained. -/
theorem coefficient_identity (P Q K D : ℝ) (hP : 0 < P)
    (hQ : Q=P^((3 : ℝ)/2)) :
    2*P^(-20 : ℝ)*K*Q^2*P^10*D = 2*K*D*P^(-7 : ℝ) := by
  calc
    _ = (2*K*D)*(P^(-20 : ℝ)*Q^2*P^10) := by ring
    _ = _ := by rw [normalization P Q hP hQ]

/-- Direct conversion of any proved tiny-phase upper bound; no positivity
of K or D is needed for this equality-based numerical rewrite. -/
theorem bound (P Q K D B : ℝ) (hP : 0 < P) (hQ : Q=P^((3 : ℝ)/2))
    (hB : B ≤ 2*P^(-20 : ℝ)*K*Q^2*P^10*D) :
    B ≤ 2*K*D*P^(-7 : ℝ) := by
  rwa [coefficient_identity P Q K D hP hQ] at hB

/-- The same exact normalization at the natural scales used by the count. -/
theorem weighted_normalization_nat (P Q : ℕ) (K D : ℝ) (hP : 0 < P)
    (hQ : (Q : ℝ)=(P : ℝ)^((3 : ℝ)/2)) :
    2*(P : ℝ)^(-20 : ℝ)*K*(Q : ℝ)^2*(P : ℝ)^10*D =
      2*K*D*(P : ℝ)^(-7 : ℝ) :=
  coefficient_identity (P : ℝ) (Q : ℝ) K D (by exact_mod_cast hP) hQ

end CubicTenVariables.TinyPhaseNumerics
