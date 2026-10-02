import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Tactic

/-! Fixed smooth cutoffs for the scalar integer delta construction.
The positive bump has integral one and support `(1/4,1)`. The even cutoff
equals one near zero and has support `(-1/4,1/4)`. These are actual functions,
independent of every modulus, phase and decay order. -/

set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.SmoothDeltaCutoffs
open MeasureTheory
open scoped BigOperators ContDiff

private def omegaBump : ContDiffBump (5/8 : ℝ) :=
  ⟨1/8,3/8,by norm_num,by norm_num⟩

private def cutoffBump : ContDiffBump (0 : ℝ) :=
  ⟨1/8,1/4,by norm_num,by norm_num⟩

/-- The fixed normalized positive bump. -/
def omega : ℝ → ℝ := omegaBump.normed volume

/-- The fixed even cutoff at the origin. -/
def U : ℝ → ℝ := cutoffBump

theorem omega_contDiff : ContDiff ℝ ∞ omega := omegaBump.contDiff_normed

theorem omega_hasCompactSupport : HasCompactSupport omega :=
  omegaBump.hasCompactSupport_normed

theorem omega_nonneg (x : ℝ) : 0 ≤ omega x := omegaBump.nonneg_normed x

theorem omega_integral : ∫ x, omega x = 1 := omegaBump.integral_normed

theorem omega_support : Function.support omega = Set.Ioo (1/4 : ℝ) 1 := by
  rw [omega, omegaBump.support_normed_eq, Real.ball_eq_Ioo]
  norm_num [omegaBump]

theorem omega_tsupport : tsupport omega = Set.Icc (1/4 : ℝ) 1 := by
  rw [omega, omegaBump.tsupport_normed_eq, Real.closedBall_eq_Icc]
  norm_num [omegaBump]

theorem omega_pos_iff (x : ℝ) : 0 < omega x ↔ (1/4 : ℝ) < x ∧ x < 1 := by
  rw [← Set.mem_Ioo, ← omega_support, Function.mem_support]
  exact ⟨ne_of_gt, fun h => lt_of_le_of_ne (omega_nonneg x) (Ne.symm h)⟩

theorem U_contDiff : ContDiff ℝ ∞ U := cutoffBump.contDiff

theorem U_hasCompactSupport : HasCompactSupport U := cutoffBump.hasCompactSupport

theorem U_mem_Icc (x : ℝ) : U x ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨cutoffBump.nonneg,cutoffBump.le_one⟩

theorem U_eq_one {x : ℝ} (hx : |x| ≤ (1/8 : ℝ)) : U x = 1 := by
  apply cutoffBump.one_of_mem_closedBall
  simpa only [Metric.mem_closedBall,dist_zero_right,Real.norm_eq_abs,cutoffBump] using hx

@[simp] theorem U_zero : U 0 = 1 := U_eq_one (by norm_num)

theorem U_neg (x : ℝ) : U (-x) = U x := cutoffBump.neg x

theorem U_support : Function.support U = Set.Ioo (-(1/4) : ℝ) (1/4) := by
  rw [U,cutoffBump.support_eq,Real.ball_eq_Ioo]
  norm_num [cutoffBump]

theorem U_tsupport : tsupport U = Set.Icc (-(1/4) : ℝ) (1/4) := by
  rw [U,cutoffBump.tsupport_eq,Real.closedBall_eq_Icc]
  norm_num [cutoffBump]

/-- The last interior grid point is a strictly positive term, even for `Q=2`. -/
theorem sum_omega_pos {Q : ℕ} (hQ : 2 ≤ Q) :
    0 < ∑ j ∈ Finset.Icc 1 Q, omega ((j : ℝ)/(Q : ℝ)) := by
  have hQ0 : 0 < (Q : ℝ) := by exact_mod_cast (show 0 < Q by omega)
  have hQ2 : (2 : ℝ) ≤ Q := by exact_mod_cast hQ
  have hsub : ((Q-1 : ℕ) : ℝ) = (Q : ℝ)-1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ Q)]
    norm_num
  apply Finset.sum_pos' (fun j _ => omega_nonneg _)
  refine ⟨Q-1,Finset.mem_Icc.mpr ⟨by omega,by omega⟩,?_⟩
  rw [omega_pos_iff,hsub]
  constructor
  · apply (lt_div_iff₀ hQ0).mpr
    linarith
  · apply (div_lt_iff₀ hQ0).mpr
    linarith

/-- The actual finite Riemann-sum normalization. -/
def normalizer (Q : ℕ) : ℝ :=
  (Q : ℝ)⁻¹ * ∑ j ∈ Finset.Icc 1 Q, omega ((j : ℝ)/(Q : ℝ))

theorem normalizer_pos {Q : ℕ} (hQ : 2 ≤ Q) : 0 < normalizer Q := by
  exact mul_pos (inv_pos.mpr (by exact_mod_cast (show 0 < Q by omega)))
    (sum_omega_pos hQ)

end CubicTenVariables.SmoothDeltaCutoffs
