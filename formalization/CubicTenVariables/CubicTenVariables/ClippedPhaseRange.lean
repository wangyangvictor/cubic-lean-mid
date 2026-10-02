import CubicTenVariables.DyadicFrequencyError
import CubicTenVariables.DeltaMethod

/-! A nonempty clipped source arc automatically satisfies the phase range
used by the dyadic saving. The opposite range contributes an empty domain.
The exact scales P=t² and Q=t³ avoid rounding P^(3/2). -/
set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.ClippedPhaseRange
open DyadicFrequencyError DeltaMethod

/-- Any point in a dyadic shell and its original delta arc forces the
strict upper range on the shell width. Only η≤1 is needed for monotonicity. -/
theorem phase_lt_of_mem (P R φ η : ℝ) (Q q : ℕ)
    (hP : 0 < P) (hR : 1 ≤ R) (hη : η ≤ 1)
    (hQ : (Q : ℝ)=P^((3 : ℝ)/2)) (hq : q ∈ moduli R)
    {θ : ℝ} (hθ : θ ∈ shell φ ∩ arc Q q η) :
    φ < (R*P^((3 : ℝ)/2))^(-1+η) := by
  have hRq := (mem_moduli R q).mp hq
  have hRpos : 0 < R := lt_of_lt_of_le zero_lt_one hR
  have hphase : |θ| < ((q : ℝ)*P^((3 : ℝ)/2))^(-1+η) := by
    simpa only [arc,Set.mem_setOf_eq,hQ] using hθ.2
  have hb : ((q : ℝ)*P^((3 : ℝ)/2))^(-1+η) ≤
      (R*P^((3 : ℝ)/2))^(-1+η) :=
    Real.rpow_le_rpow_of_nonpos (mul_pos hRpos (Real.rpow_pos_of_pos hP _))
      (mul_le_mul_of_nonneg_right hRq.1.le (Real.rpow_nonneg hP.le _)) (by linarith)
  exact (hθ.1.1.trans hphase).trans_le hb

/-- The non-strict phase hypothesis required by the saving theorem follows
automatically whenever the actual clipped block contains a phase. -/
theorem phase_le_of_mem (P R φ η : ℝ) (Q q : ℕ)
    (hP : 0 < P) (hR : 1 ≤ R) (hη : η ≤ 1)
    (hQ : (Q : ℝ)=P^((3 : ℝ)/2)) (hq : q ∈ moduli R)
    {θ : ℝ} (hθ : θ ∈ shell φ ∩ arc Q q η) :
    φ ≤ (R*P^((3 : ℝ)/2))^(-1+η) :=
  (phase_lt_of_mem P R φ η Q q hP hR hη hQ hq hθ).le

theorem phase_le_of_nonempty (P R φ η : ℝ) (Q q : ℕ)
    (hP : 0 < P) (hR : 1 ≤ R) (hη : η ≤ 1)
    (hQ : (Q : ℝ)=P^((3 : ℝ)/2)) (hq : q ∈ moduli R)
    (hne : (shell φ ∩ arc Q q η).Nonempty) :
    φ ≤ (R*P^((3 : ℝ)/2))^(-1+η) := by
  obtain ⟨θ,hθ⟩ := hne
  exact phase_le_of_mem P R φ η Q q hP hR hη hQ hq hθ

/-- Even equality at the putative upper endpoint leaves an empty clipped
block, because the source arc and shell have strict relevant endpoints. -/
theorem intersection_eq_empty_of_bound_le (P R φ η : ℝ) (Q q : ℕ)
    (hP : 0 < P) (hR : 1 ≤ R) (hη : η ≤ 1)
    (hQ : (Q : ℝ)=P^((3 : ℝ)/2)) (hq : q ∈ moduli R)
    (hφ : (R*P^((3 : ℝ)/2))^(-1+η) ≤ φ) :
    shell φ ∩ arc Q q η = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro θ hθ
  exact (not_lt_of_ge hφ) (phase_lt_of_mem P R φ η Q q hP hR hη hQ hq hθ)

/-- Failure of the saving theorem's admissibility condition contributes no
phase at any modulus in this dyadic block. -/
theorem intersection_eq_empty_of_not_le (P R φ η : ℝ) (Q q : ℕ)
    (hP : 0 < P) (hR : 1 ≤ R) (hη : η ≤ 1)
    (hQ : (Q : ℝ)=P^((3 : ℝ)/2)) (hq : q ∈ moduli R)
    (hφ : ¬ φ ≤ (R*P^((3 : ℝ)/2))^(-1+η)) :
    shell φ ∩ arc Q q η = ∅ :=
  intersection_eq_empty_of_bound_le P R φ η Q q hP hR hη hQ hq (le_of_lt (not_le.mp hφ))

/-- Exact square/cube scale identity over the nonnegative reals. -/
theorem square_rpow_three_halves (t : ℝ) (ht : 0 ≤ t) :
    (t^2)^((3 : ℝ)/2)=t^3 := by
  have h := (Real.rpow_natCast_mul ht 2 ((3 : ℝ)/2)).symm
  norm_num at h
  exact h

/-- The natural-number subsequence P=t²,Q=t³ has precisely Q=P^(3/2). -/
theorem nat_square_rpow_three_halves (t : ℕ) :
    ((t^2 : ℕ) : ℝ)^((3 : ℝ)/2)=((t^3 : ℕ) : ℝ) := by
  push_cast
  exact square_rpow_three_halves (t : ℝ) (Nat.cast_nonneg t)

theorem exact_scales (t : ℕ) (ht : 0 < t) :
    0 < t^2 ∧ 0 < t^3 ∧ ((t^3 : ℕ) : ℝ)=((t^2 : ℕ) : ℝ)^((3 : ℝ)/2) :=
  ⟨pow_pos ht _,pow_pos ht _,(nat_square_rpow_three_halves t).symm⟩

end CubicTenVariables.ClippedPhaseRange
