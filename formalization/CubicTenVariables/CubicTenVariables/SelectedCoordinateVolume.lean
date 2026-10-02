import CubicTenVariables.SelectedGradientSliceVolume
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Integral.Lebesgue.Map

/-! Exact Lebesgue disintegration into independently selected input
coordinates and their complement. The map is a coordinate permutation and
product equivalence, so there is no Jacobian loss or literature premise. -/
set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.SelectedCoordinateVolume
open MeasureTheory SelectedGradientCoordinates SelectedGradientSliceVolume
open scoped ENNReal BigOperators
variable {n r : ℕ}

/-- The actual coordinate reconstruction as a measurable equivalence. -/
def combineMeasurableEquiv (cols : Fin r → Fin n) (hc : Function.Injective cols) :
    ((Fin r → ℝ) × (Complement cols → ℝ)) ≃ᵐ (Fin n → ℝ) :=
  (MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin r ⊕ Complement cols => ℝ)).symm.trans
    (MeasurableEquiv.piCongrLeft (fun _ : Fin n => ℝ) (indexEquiv cols hc))

@[simp] theorem combineMeasurableEquiv_apply (cols : Fin r → Fin n)
    (hc : Function.Injective cols) (z : Fin r → ℝ) (w : Complement cols → ℝ) :
    combineMeasurableEquiv cols hc (z,w)=combine cols hc z w := by
  funext i
  obtain ⟨j,rfl⟩ := (indexEquiv cols hc).surjective i
  change MeasurableEquiv.piCongrLeft (fun _ : Fin n => ℝ) (indexEquiv cols hc)
    ((MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin r ⊕ Complement cols => ℝ)).symm (z,w))
      (indexEquiv cols hc j)=_
  rw [MeasurableEquiv.piCongrLeft_apply_apply]
  cases j <;> simp [MeasurableEquiv.sumPiEquivProdPi,Equiv.sumPiEquivProdPi]

/-- Reconstruction preserves exactly the product of the two Lebesgue measures. -/
theorem measurePreserving_combine (cols : Fin r → Fin n) (hc : Function.Injective cols) :
    MeasurePreserving (fun zw : (Fin r → ℝ) × (Complement cols → ℝ) =>
      combine cols hc zw.1 zw.2) volume volume := by
  have h := (volume_measurePreserving_piCongrLeft (fun _ : Fin n => ℝ) (indexEquiv cols hc)).comp
    (volume_measurePreserving_sumPiEquivProdPi_symm (fun _ : Fin r ⊕ Complement cols => ℝ))
  change MeasurePreserving (combineMeasurableEquiv cols hc) volume volume at h
  simpa only [show (combineMeasurableEquiv cols hc :
      ((Fin r → ℝ) × (Complement cols → ℝ)) → (Fin n → ℝ)) =
      (fun zw => combine cols hc zw.1 zw.2) from funext fun zw =>
        combineMeasurableEquiv_apply cols hc zw.1 zw.2] using h

theorem measurable_combine (cols : Fin r → Fin n) (hc : Function.Injective cols) :
    Measurable (fun zw : (Fin r → ℝ) × (Complement cols → ℝ) =>
      combine cols hc zw.1 zw.2) := (measurePreserving_combine cols hc).measurable

/-- The individual fixed-complement slice is measurable. -/
theorem measurableSet_slice (cols : Fin r → Fin n) (hc : Function.Injective cols)
    (S : Set (Fin n → ℝ)) (hS : MeasurableSet S) (w : Complement cols → ℝ) :
    MeasurableSet {z : Fin r → ℝ | combine cols hc z w ∈ S} :=
  hS.preimage ((measurable_combine cols hc).comp (measurable_id.prodMk measurable_const))

/-- The resulting ENNReal-valued slice-volume function is measurable. -/
theorem measurable_slice_volume (cols : Fin r → Fin n) (hc : Function.Injective cols)
    (S : Set (Fin n → ℝ)) (hS : MeasurableSet S) :
    Measurable (fun w : Complement cols → ℝ =>
      volume {z : Fin r → ℝ | combine cols hc z w ∈ S}) := by
  exact measurable_measure_prodMk_right (hS.preimage (measurable_combine cols hc))

/-- Exact Fubini disintegration of an arbitrary measurable set, including
infinite-volume sets and zero-dimensional selected/complement factors. -/
theorem volume_eq_lintegral_slices (cols : Fin r → Fin n) (hc : Function.Injective cols)
    (S : Set (Fin n → ℝ)) (hS : MeasurableSet S) :
    volume S = ∫⁻ w : Complement cols → ℝ,
      volume {z : Fin r → ℝ | combine cols hc z w ∈ S} := by
  have h := (measurePreserving_combine cols hc).measure_preimage hS.nullMeasurableSet
  rw [← h]
  exact Measure.prod_apply_symm (hS.preimage (measurable_combine cols hc))

/-- Compact sets satisfy the same literal coordinate-slice formula. -/
theorem volume_eq_lintegral_slices_of_isCompact (cols : Fin r → Fin n)
    (hc : Function.Injective cols) (S : Set (Fin n → ℝ)) (hS : IsCompact S) :
    volume S = ∫⁻ w : Complement cols → ℝ,
      volume {z : Fin r → ℝ | combine cols hc z w ∈ S} :=
  volume_eq_lintegral_slices cols hc S hS.measurableSet

/-- Nonnegative measurable integrands obey the same rearrangement, for use
with finite sums and indicator functions in the local-supremum argument. -/
theorem lintegral_eq_lintegral_slices (cols : Fin r → Fin n) (hc : Function.Injective cols)
    (f : (Fin n → ℝ) → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ x : Fin n → ℝ, f x) =
      ∫⁻ w : Complement cols → ℝ, ∫⁻ z : Fin r → ℝ, f (combine cols hc z w) := by
  rw [← (measurePreserving_combine cols hc).lintegral_comp hf]
  exact lintegral_prod_symm _ (hf.comp (measurable_combine cols hc)).aemeasurable

/-- The finite rearrangement needed when the chosen maximizing frequency
depends on the outer lattice center. -/
theorem sum_volume_eq_lintegral_sum_slices {ι : Type*}
    (cols : Fin r → Fin n) (hc : Function.Injective cols)
    (T : Finset ι) (S : ι → Set (Fin n → ℝ))
    (hS : ∀ i ∈ T, MeasurableSet (S i)) :
    (∑ i ∈ T, volume (S i)) = ∫⁻ w : Complement cols → ℝ,
      ∑ i ∈ T, volume {z : Fin r → ℝ | combine cols hc z w ∈ S i} := by
  rw [lintegral_finset_sum T (fun i hi => measurable_slice_volume cols hc (S i) (hS i hi))]
  exact Finset.sum_congr rfl fun i hi => volume_eq_lintegral_slices cols hc (S i) (hS i hi)

/-- Compactness ensures that the iterated integral is finite; the formula
therefore cannot hide an infinite-volume conversion to a real number. -/
theorem lintegral_slices_ne_top_of_isCompact (cols : Fin r → Fin n)
    (hc : Function.Injective cols) (S : Set (Fin n → ℝ)) (hS : IsCompact S) :
    (∫⁻ w : Complement cols → ℝ, volume {z : Fin r → ℝ | combine cols hc z w ∈ S}) ≠ ⊤ := by
  rw [← volume_eq_lintegral_slices_of_isCompact cols hc S hS]
  exact hS.measure_lt_top.ne

end CubicTenVariables.SelectedCoordinateVolume
