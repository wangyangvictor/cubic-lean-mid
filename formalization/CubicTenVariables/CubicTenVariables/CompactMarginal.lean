import CubicTenVariables.CompactMarginalSupport
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Const
import Mathlib.Analysis.Normed.Group.Bounded

/-! Smoothness of the actual marginal of a compactly supported density.

Differentiation takes place under a literal integral over the compact
projection of the support. The derivative density is the Fréchet derivative
in the first coordinate. Its compact support supplies a uniform integrable
bound. Induction proves every finite differentiability order and hence
smoothness. No marginal, differentiability, or domination premise is assumed.
-/

noncomputable section
namespace CubicTenVariables.CompactMarginal
open MeasureTheory Filter
open scoped Topology ContDiff

variable {m : ℕ}

/-- The actual partial derivative in the scalar coordinate of the density. -/
def firstDerivative (a : ℝ × (Fin m → ℝ) → ℝ) (p : ℝ × (Fin m → ℝ)) : ℝ :=
  fderiv ℝ a p (1, 0)

theorem hasCompactSupport_firstDerivative (a : ℝ × (Fin m → ℝ) → ℝ)
    (ha : HasCompactSupport a) : HasCompactSupport (firstDerivative a) :=
  ha.fderiv_apply ℝ (1, 0)

theorem continuous_firstDerivative (a : ℝ × (Fin m → ℝ) → ℝ)
    (ha : ContDiff ℝ 1 a) : Continuous (firstDerivative a) :=
  (ha.continuous_fderiv le_rfl).clm_apply continuous_const

theorem contDiff_firstDerivative (a : ℝ × (Fin m → ℝ) → ℝ)
    (ha : ContDiff ℝ ∞ a) : ContDiff ℝ ∞ (firstDerivative a) :=
  (ha.fderiv_right (by simp)).clm_apply contDiff_const

/-- The derivative along a fixed fiber is the first-coordinate derivative
of the actual joint density. -/
theorem hasDerivAt_slice (a : ℝ × (Fin m → ℝ) → ℝ)
    (ha : ContDiff ℝ 1 a) (t : ℝ) (y : Fin m → ℝ) :
    HasDerivAt (fun s => a (s, y)) (firstDerivative a (t, y)) t := by
  have hpair : HasDerivAt (fun s : ℝ => (s, y)) (1, 0) t :=
    (hasDerivAt_id t).prodMk (hasDerivAt_const t y)
  simpa only [firstDerivative, Function.comp_def] using
    ((ha.differentiable le_rfl (t, y)).hasFDerivAt.comp_hasDerivAt t hpair)

/-- The derivative density vanishes outside the original density's closed
support, even if its own support is smaller. -/
theorem firstDerivative_eq_zero_of_notMem_tsupport
    (a : ℝ × (Fin m → ℝ) → ℝ) (p : ℝ × (Fin m → ℝ))
    (hp : p ∉ tsupport a) : firstDerivative a p = 0 := by
  simp only [firstDerivative, fderiv_of_notMem_tsupport ℝ hp,
    ContinuousLinearMap.zero_apply]

/-- For a compactly supported `C¹` density, the marginal's derivative is
the marginal of its actual first partial derivative. -/
theorem hasDerivAt_marginal (a : ℝ × (Fin m → ℝ) → ℝ)
    (ha : ContDiff ℝ 1 a) (hc : HasCompactSupport a) (t : ℝ) :
    HasDerivAt (marginal a) (marginal (firstDerivative a) t) t := by
  let K : Set (Fin m → ℝ) := Prod.snd '' tsupport a
  have hK : IsCompact K := hc.isCompact.image continuous_snd
  have hdcont := continuous_firstDerivative a ha
  have hdcompact := hasCompactSupport_firstDerivative a hc
  obtain ⟨C, hC⟩ := hdcont.bounded_above_of_compact_support hdcompact
  have hFcont (s : ℝ) : Continuous (fun y : Fin m → ℝ => a (s, y)) :=
    ha.continuous.comp (continuous_const.prodMk continuous_id)
  have hDcont (s : ℝ) : Continuous (fun y : Fin m → ℝ => firstDerivative a (s, y)) :=
    hdcont.comp (continuous_const.prodMk continuous_id)
  have hDzero (s : ℝ) (y : Fin m → ℝ) (hy : y ∉ K) :
      firstDerivative a (s, y) = 0 := by
    apply firstDerivative_eq_zero_of_notMem_tsupport
    intro hp
    exact hy ⟨(s, y), hp, rfl⟩
  have hDint (s : ℝ) : (∫ y in K, firstDerivative a (s, y)) =
      marginal (firstDerivative a) s :=
    setIntegral_eq_integral_of_forall_compl_eq_zero (hDzero s)
  have hFint : (fun s : ℝ => ∫ y in K, a (s, y)) = marginal a := by
    funext s
    exact (marginal_eq_setIntegral a s).symm
  have hderiv := (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict K) (F := fun s y => a (s, y))
    (F' := fun s y => firstDerivative a (s, y)) (x₀ := t)
    (bound := fun _ => C) (show (0 : ℝ) < 1 by norm_num)
    (Eventually.of_forall fun s => (hFcont s).aestronglyMeasurable)
    ((hFcont t).continuousOn.integrableOn_compact hK)
    ((hDcont t).aestronglyMeasurable)
    (Eventually.of_forall fun y s _ => hC (s, y))
    (integrableOn_const hK.measure_ne_top)
    (Eventually.of_forall fun y s _ => hasDerivAt_slice a ha s y)).2
  rw [hFint, hDint] at hderiv
  exact hderiv

/-- Differentiation of the actual marginal, with no separately assumed
domination or differentiability statement. -/
theorem deriv_marginal (a : ℝ × (Fin m → ℝ) → ℝ)
    (ha : ContDiff ℝ 1 a) (hc : HasCompactSupport a) :
    deriv (marginal a) = marginal (firstDerivative a) := by
  funext t
  exact (hasDerivAt_marginal a ha hc t).deriv

/-- Every actual smooth compactly supported density has a smooth marginal. -/
theorem contDiff_marginal (a : ℝ × (Fin m → ℝ) → ℝ)
    (ha : ContDiff ℝ ∞ a) (hc : HasCompactSupport a) :
    ContDiff ℝ ∞ (marginal a) := by
  apply contDiff_infty.mpr
  intro N
  induction N generalizing a with
  | zero => exact contDiff_zero.mpr (continuous_marginal a ha.continuous hc)
  | succ N ih =>
      apply contDiff_succ_iff_hasFDerivAt.mpr
      refine ⟨fun t => (1 : ℝ →L[ℝ] ℝ).smulRight (marginal (firstDerivative a) t),
        contDiff_const.smulRight (ih (firstDerivative a)
          (contDiff_firstDerivative a ha) (hasCompactSupport_firstDerivative a hc)), ?_⟩
      intro t
      exact (hasDerivAt_marginal a (ha.of_le (by simp)) hc t).hasFDerivAt

end CubicTenVariables.CompactMarginal
