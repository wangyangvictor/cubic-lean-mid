import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-! Splitting an actual coordinate before taking the one-dimensional marginal.

The coordinate insertion is the inverse of mathlib's measure-preserving
`piFinSuccAbove` equivalence. All uses of Fubini below have an explicit
fixed-frequency integrability proof. No integration over frequency is
interchanged with the spatial integral. -/

noncomputable section
namespace CubicTenVariables.CoordinateMarginal
open scoped Topology ContDiff
open MeasureTheory

/-- Insert the distinguished real coordinate into the remaining tuple. -/
def coordinateInsert {m : ℕ} (i : Fin (m + 1))
    (p : ℝ × (Fin m → ℝ)) : Fin (m + 1) → ℝ :=
  i.insertNth p.1 p.2

@[simp] theorem coordinateInsert_same {m : ℕ} (i : Fin (m + 1))
    (p : ℝ × (Fin m → ℝ)) : coordinateInsert i p i = p.1 :=
  Fin.insertNth_apply_same _ _ _

@[simp] theorem coordinateInsert_succAbove {m : ℕ} (i : Fin (m + 1))
    (p : ℝ × (Fin m → ℝ)) (j : Fin m) : coordinateInsert i p (i.succAbove j) = p.2 j :=
  Fin.insertNth_apply_succAbove _ _ _ _

theorem coordinateInsert_eq_measurableEquiv_symm {m : ℕ} (i : Fin (m + 1)) :
    coordinateInsert i = (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) i).symm :=
  rfl

theorem contDiff_coordinateInsert {m : ℕ} (i : Fin (m + 1)) :
    ContDiff ℝ ∞ (coordinateInsert i) := by
  apply contDiff_pi.mpr
  rw [i.forall_iff_succAbove]
  constructor
  · simpa only [coordinateInsert_same] using
      (contDiff_fst : ContDiff ℝ ∞ (fun p : ℝ × (Fin m → ℝ) => p.1))
  · intro j
    simpa only [coordinateInsert_succAbove] using
      (contDiff_apply ℝ ℝ j).comp
        (contDiff_snd : ContDiff ℝ ∞ (fun p : ℝ × (Fin m → ℝ) => p.2))

/-- The same coordinate equivalence as a homeomorphism. -/
def coordinateHomeomorph {m : ℕ} (i : Fin (m + 1)) :
    (Fin (m + 1) → ℝ) ≃ₜ ℝ × (Fin m → ℝ) where
  toEquiv := (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) i).toEquiv
  continuous_toFun := (continuous_apply i).prodMk
    (continuous_pi fun j => continuous_apply (i.succAbove j))
  continuous_invFun := (contDiff_coordinateInsert i).continuous

/-- The actual density expressed in the split coordinates. -/
def splitDensity {m : ℕ} (i : Fin (m + 1)) (a : (Fin (m + 1) → ℝ) → ℝ)
    (p : ℝ × (Fin m → ℝ)) : ℝ :=
  a (coordinateInsert i p)

/-- The literal integral over the remaining coordinates. -/
def coordinateMarginal {m : ℕ} (i : Fin (m + 1)) (a : (Fin (m + 1) → ℝ) → ℝ)
    (t : ℝ) : ℝ :=
  ∫ y : Fin m → ℝ, splitDensity i a (t, y)

theorem continuous_splitDensity {m : ℕ} (i : Fin (m + 1))
    (a : (Fin (m + 1) → ℝ) → ℝ) (ha : Continuous a) :
    Continuous (splitDensity i a) :=
  ha.comp (contDiff_coordinateInsert i).continuous

theorem contDiff_splitDensity {m : ℕ} (i : Fin (m + 1))
    (a : (Fin (m + 1) → ℝ) → ℝ) (ha : ContDiff ℝ ∞ a) :
    ContDiff ℝ ∞ (splitDensity i a) :=
  ha.comp (contDiff_coordinateInsert i)

theorem hasCompactSupport_splitDensity {m : ℕ} (i : Fin (m + 1))
    (a : (Fin (m + 1) → ℝ) → ℝ) (ha : HasCompactSupport a) :
    HasCompactSupport (splitDensity i a) :=
  ha.comp_homeomorph (coordinateHomeomorph i).symm

theorem hasCompactSupport_splitDensity_slice {m : ℕ} (i : Fin (m + 1))
    (a : (Fin (m + 1) → ℝ) → ℝ) (ha : HasCompactSupport a) (t : ℝ) :
    HasCompactSupport (fun y : Fin m → ℝ => splitDensity i a (t, y)) := by
  apply HasCompactSupport.of_support_subset_isCompact
    ((hasCompactSupport_splitDensity i a ha).isCompact.image continuous_snd)
  intro y hy
  exact ⟨(t, y), subset_tsupport (splitDensity i a) hy, rfl⟩

theorem coordinateMarginal_nonneg {m : ℕ} (i : Fin (m + 1))
    (a : (Fin (m + 1) → ℝ) → ℝ) (ha : ∀ z, 0 ≤ a z) (t : ℝ) :
    0 ≤ coordinateMarginal i a t :=
  integral_nonneg fun y => ha (coordinateInsert i (t, y))

/-- A positive density value on the zero-coordinate slice makes its
ordinary slice integral strictly positive. -/
theorem coordinateMarginal_zero_pos {m : ℕ} (i : Fin (m + 1))
    (a : (Fin (m + 1) → ℝ) → ℝ) (ha : Continuous a) (hc : HasCompactSupport a)
    (hnonneg : ∀ z, 0 ≤ a z) (z : Fin (m + 1) → ℝ)
    (hzi : z i = 0) (hz : 0 < a z) : 0 < coordinateMarginal i a 0 := by
  have hins : coordinateInsert i (0, i.removeNth z) = z := by
    simpa only [coordinateInsert, hzi] using i.insertNth_self_removeNth z
  apply Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero
    ((continuous_splitDensity i a ha).comp (continuous_const.prodMk continuous_id))
    (hasCompactSupport_splitDensity_slice i a hc 0)
    (fun y => hnonneg (coordinateInsert i (0, y)))
  show splitDensity i a (0, i.removeNth z) ≠ 0
  simpa only [splitDensity, hins] using ne_of_gt hz

/-- Separating the actual chosen coordinate preserves the standard product
volume, with no additional constant. -/
theorem coordinateInsert_measurePreserving {m : ℕ} (i : Fin (m + 1)) :
    MeasurePreserving (coordinateInsert i) :=
  (volume_preserving_piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) i).symm

/-- At every fixed frequency, the ambient oscillatory integral is the
one-dimensional Fourier integral of the actual coordinate marginal. -/
theorem coordinate_integral_eq_marginal {m : ℕ} (i : Fin (m + 1))
    (a : (Fin (m + 1) → ℝ) → ℝ) (ha : Continuous a) (hc : HasCompactSupport a)
    (β : ℝ) :
    (∫ z : Fin (m + 1) → ℝ, (a z : ℂ) *
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (β : ℂ) * (z i : ℂ))) =
    ∫ t : ℝ, (coordinateMarginal i a t : ℂ) *
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (β : ℂ) * (t : ℂ)) := by
  let q : (Fin (m + 1) → ℝ) → ℂ := fun z => (a z : ℂ) *
    Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (β : ℂ) * (z i : ℂ))
  have hq : Integrable q := by
    have hcont : Continuous q := by dsimp [q]; fun_prop
    have hcomp : HasCompactSupport q :=
      (hc.comp_left (g := fun t : ℝ => (t : ℂ)) (by simp)).mul_right
    exact hcont.integrable_of_hasCompactSupport hcomp
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) i
  have hp : MeasurePreserving e.symm := coordinateInsert_measurePreserving i
  have hqsplit : Integrable (fun p => q (coordinateInsert i p)) :=
    (hp.integrable_comp_emb e.symm.measurableEmbedding).mpr hq
  calc
    (∫ z, q z) = ∫ p : ℝ × (Fin m → ℝ), q (coordinateInsert i p) :=
      (hp.integral_comp' q).symm
    _ = ∫ t : ℝ, ∫ y : Fin m → ℝ, q (coordinateInsert i (t, y)) :=
      integral_prod _ hqsplit
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with t
      simp only [q, coordinateInsert_same]
      rw [integral_mul_const, integral_complex_ofReal]
      rfl

end CubicTenVariables.CoordinateMarginal
