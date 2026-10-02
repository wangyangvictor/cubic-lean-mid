import CubicTenVariables.ClippedPhaseRange

/-! A slightly smaller delta-method scale is absorbed by the already
proved phase-loss parameter. All arcs retain their original Q and eta;
only the analytic majorant uses eta+nu. No analytic input is needed. -/
set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.CountingScaleRange
open DyadicFrequencyError DeltaMethod

/-- Lowering Q to P^(3/2-nu) enlarges its arc by at most the loss nu.
No upper bound on Q or nu is needed for this one-sided comparison. -/
theorem arc_radius_le (P R Q ν η : ℝ) (hP : 1 ≤ P) (hR : 1 ≤ R)
    (hν : 0 ≤ ν) (hη : 0 ≤ η) (hη1 : η ≤ 1)
    (hQ : P^((3:ℝ)/2-ν) ≤ Q) :
    (R*Q)^(-1+η) ≤ (R*P^((3:ℝ)/2))^(-1+(η+ν)) := by
  have hPpos : 0 < P := zero_lt_one.trans_le hP
  have hRpos : 0 < R := zero_lt_one.trans_le hR
  have hQpos : 0 < Q := (Real.rpow_pos_of_pos hPpos _).trans_le hQ
  have hlogQ := Real.log_le_log (Real.rpow_pos_of_pos hPpos ((3:ℝ)/2-ν)) hQ
  rw [Real.log_rpow hPpos] at hlogQ
  have hlogP : 0 ≤ Real.log P := Real.log_nonneg hP
  have hlogR : 0 ≤ Real.log R := Real.log_nonneg hR
  have hq := mul_nonneg (show 0 ≤ 1-η by linarith) (sub_nonneg.mpr hlogQ)
  have hr := mul_nonneg hν hlogR
  have hp := mul_nonneg (mul_nonneg hν (show 0 ≤ (1:ℝ)/2+η by linarith)) hlogP
  apply (Real.log_le_log_iff (by positivity) (by positivity)).mp
  simp (disch := positivity) only [Real.log_rpow,Real.log_mul]
  nlinarith only [hq,hr,hp]

/-- The same bound holds whenever the actual modulus is at least R. -/
theorem phase_le_of_lower_modulus (P R φ η ν : ℝ) (Q q : ℕ)
    (hP : 1 ≤ P) (hR : 1 ≤ R) (hν : 0 ≤ ν) (hη : 0 ≤ η) (hη1 : η ≤ 1)
    (hQ : P^((3:ℝ)/2-ν) ≤ (Q:ℝ)) (hq : R ≤ (q:ℝ))
    {θ : ℝ} (hθ : θ ∈ shell φ ∩ arc Q q η) :
    φ ≤ (R*P^((3:ℝ)/2))^(-1+(η+ν)) := by
  have hPpos : 0 < P := zero_lt_one.trans_le hP
  have hRpos : 0 < R := zero_lt_one.trans_le hR
  have hQpos : (0:ℝ) < Q := (Real.rpow_pos_of_pos hPpos _).trans_le hQ
  have hpoint : |θ| < ((q:ℝ)*(Q:ℝ))^(-1+η) := hθ.2
  have hqrad : ((q:ℝ)*(Q:ℝ))^(-1+η) ≤ (R*(Q:ℝ))^(-1+η) :=
    Real.rpow_le_rpow_of_nonpos (mul_pos hRpos hQpos)
      (mul_le_mul_of_nonneg_right hq hQpos.le) (by linarith)
  exact ((hθ.1.1.trans hpoint).le.trans hqrad).trans
    (arc_radius_le P R Q ν η hP hR hν hη hη1 hQ)

theorem phase_le_of_mem (P R φ η ν : ℝ) (Q q : ℕ)
    (hP : 1 ≤ P) (hR : 1 ≤ R) (hν : 0 ≤ ν) (hη : 0 ≤ η) (hη1 : η ≤ 1)
    (hQ : P^((3:ℝ)/2-ν) ≤ (Q:ℝ)) (hq : q ∈ moduli R)
    {θ : ℝ} (hθ : θ ∈ shell φ ∩ arc Q q η) :
    φ ≤ (R*P^((3:ℝ)/2))^(-1+(η+ν)) :=
  phase_le_of_lower_modulus P R φ η ν Q q hP hR hν hη hη1 hQ
    ((mem_moduli R q).mp hq).1.le hθ

theorem intersection_eq_empty_of_not_le (P R φ η ν : ℝ) (Q q : ℕ)
    (hP : 1 ≤ P) (hR : 1 ≤ R) (hν : 0 ≤ ν) (hη : 0 ≤ η) (hη1 : η ≤ 1)
    (hQ : P^((3:ℝ)/2-ν) ≤ (Q:ℝ)) (hq : q ∈ moduli R)
    (hφ : ¬ φ ≤ (R*P^((3:ℝ)/2))^(-1+(η+ν))) :
    shell φ ∩ arc Q q η = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro θ hθ
  exact hφ (phase_le_of_mem P R φ η ν Q q hP hR hν hη hη1 hQ hq hθ)

theorem one_phase_le_of_mem (P φ η ν : ℝ) (Q : ℕ)
    (hP : 1 ≤ P) (hν : 0 ≤ ν) (hη : 0 ≤ η) (hη1 : η ≤ 1)
    (hQ : P^((3:ℝ)/2-ν) ≤ (Q:ℝ))
    {θ : ℝ} (hθ : θ ∈ shell φ ∩ arc Q 1 η) :
    φ ≤ (P^((3:ℝ)/2))^(-1+(η+ν)) := by
  simpa only [one_mul] using phase_le_of_lower_modulus P 1 φ η ν Q 1
    hP le_rfl hν hη hη1 hQ (by norm_num) hθ

theorem one_intersection_eq_empty_of_not_le (P φ η ν : ℝ) (Q : ℕ)
    (hP : 1 ≤ P) (hν : 0 ≤ ν) (hη : 0 ≤ η) (hη1 : η ≤ 1)
    (hQ : P^((3:ℝ)/2-ν) ≤ (Q:ℝ))
    (hφ : ¬ φ ≤ (P^((3:ℝ)/2))^(-1+(η+ν))) :
    shell φ ∩ arc Q 1 η = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro θ hθ
  exact hφ (one_phase_le_of_mem P φ η ν Q hP hν hη hη1 hQ hθ)

end CubicTenVariables.CountingScaleRange
