import CubicTenVariables.TinyPhaseNumerics

/-! Elementary error bounds for flexible circle-method scales. The tiny
phase bound needs only Q≤P^(3/2); the scalar delta error needs only P≤Q.
No exact power relation or literature result is assumed. -/
set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.FlexibleCountingNumerics

/-- The full short-interval coefficient decreases when the modulus cutoff
is moved below P^(3/2). All fixed nonnegative factors are retained. -/
theorem tiny_coefficient_le (P Q K D : ℝ) (hP : 0 < P) (hQ : 0 ≤ Q)
    (hQP : Q ≤ P^((3:ℝ)/2)) (hK : 0 ≤ K) (hD : 0 ≤ D) :
    2*P^(-20:ℝ)*K*Q^2*P^10*D ≤ (2*K*D)*P^(-7:ℝ) := by
  calc
    _ ≤ 2*P^(-20:ℝ)*K*(P^((3:ℝ)/2))^2*P^10*D := by gcongr
    _ = _ := TinyPhaseNumerics.coefficient_identity P (P^((3:ℝ)/2)) K D hP rfl

/-- For every fixed positive phase loss, one natural order works uniformly
for all scales with P≤Q, with any prescribed power of decay. -/
theorem exists_delta_order (η A : ℝ) (hη : 0 < η) :
    ∃ N : ℕ, 1 ≤ N ∧ ∀ P Q : ℝ, 1 ≤ P → P ≤ Q →
      P^10*Q^(-(N:ℝ)*η) ≤ P^(-A) := by
  obtain ⟨N,hN⟩ := exists_nat_ge (max 1 ((10+A)/η))
  have hN1 : (1:ℝ) ≤ N := (le_max_left _ _).trans hN
  have hNA : (10+A)/η ≤ N := (le_max_right _ _).trans hN
  refine ⟨N,by exact_mod_cast hN1,?_⟩
  intro P Q hP hPQ
  have hP0 : 0 < P := zero_lt_one.trans_le hP
  have hexp : -(N:ℝ)*η ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (Nat.cast_nonneg N)) hη.le
  have hQpow : Q^(-(N:ℝ)*η) ≤ P^(-(N:ℝ)*η) :=
    Real.rpow_le_rpow_of_nonpos hP0 hPQ hexp
  have he : (10:ℝ)+(-(N:ℝ)*η) ≤ -A := by
    have h := (div_le_iff₀ hη).mp hNA
    linarith
  calc
    _ ≤ P^10*P^(-(N:ℝ)*η) := mul_le_mul_of_nonneg_left hQpow (by positivity)
    _ = P^((10:ℝ)+(-(N:ℝ)*η)) := by
      rw [← Real.rpow_natCast P 10,← Real.rpow_add hP0]
      norm_num
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hP he

end CubicTenVariables.FlexibleCountingNumerics
