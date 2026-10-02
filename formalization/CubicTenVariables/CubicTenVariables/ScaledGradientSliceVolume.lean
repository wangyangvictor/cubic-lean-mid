import CubicTenVariables.RealRegularGradientChart
import CubicTenVariables.SelectedGradientSliceVolume
import CubicTenVariables.GradientWindowScaling

/-! Actual normalized scalar-gradient windows and their seven-dimensional
slices. The scalar may have either sign; the volume estimate requires only
that it be nonzero. All localization boxes are the fixed chart boxes. -/
set_option autoImplicit false
set_option maxHeartbeats 1500000
noncomputable section
namespace CubicTenVariables.ScaledGradientSliceVolume
open MvPolynomial MeasureTheory RealRegularGradientChart SelectedGradientCoordinates
open SelectedGradientSliceVolume GradientWindowScaling
open scoped BigOperators ENNReal

attribute [local instance] Classical.propDecidable

/-- The slice of the existing actual gradient window at fixed untouched inputs. -/
def slice (F : MvPolynomial (Fin 10) ℝ) (D : Data F)
    (β : ℝ) (a : Fin 10 → ℝ) (δ : ℝ) (w : Complement D.cols → ℝ) : Set (Fin 7 → ℝ) :=
  {z | combine D.cols D.cols_injective z w ∈ window F D.box 1 β a δ}

theorem mem_window_one_iff (F : MvPolynomial (Fin 10) ℝ) (D : Data F)
    (β : ℝ) (a : Fin 10 → ℝ) (δ : ℝ) (x : Fin 10 → ℝ) :
    x ∈ window F D.box 1 β a δ ↔
      x ∈ D.box ∧ ∀ i, |β*eval x (pderiv i F)-a i| ≤ δ := by
  simp only [window, Set.mem_setOf_eq, inv_one, one_smul]

/-- Compactness concerns the literal full-gradient window, without deleting
any of its ten inequalities. It also holds at zero scalar or negative width. -/
theorem isCompact_window (F : MvPolynomial (Fin 10) ℝ) (D : Data F)
    (β : ℝ) (a : Fin 10 → ℝ) (δ : ℝ) : IsCompact (window F D.box 1 β a δ) := by
  have hc : IsClosed {x : Fin 10 → ℝ | ∀ i, |β*eval x (pderiv i F)-a i| ≤ δ} := by
    simp only [Set.setOf_forall]
    apply isClosed_iInter
    intro i
    exact isClosed_le
      ((continuous_const.mul (NormedPolynomialChart.contDiff_eval (pderiv i F)).continuous).sub
        continuous_const).abs continuous_const
  simpa only [window, inv_one, one_smul] using D.box_compact.inter_right hc

theorem measurableSet_window (F : MvPolynomial (Fin 10) ℝ) (D : Data F)
    (β : ℝ) (a : Fin 10 → ℝ) (δ : ℝ) : MeasurableSet (window F D.box 1 β a δ) :=
  (isCompact_window F D β a δ).measurableSet

theorem isClosed_slice (F : MvPolynomial (Fin 10) ℝ) (D : Data F)
    (β : ℝ) (a : Fin 10 → ℝ) (δ : ℝ) (w : Complement D.cols → ℝ) :
    IsClosed (slice F D β a δ w) := by
  have hc : Continuous (fun z : Fin 7 → ℝ => combine D.cols D.cols_injective z w) :=
    (isometry_iff_dist_eq.mpr (dist_combine D.cols D.cols_injective w)).continuous
  exact (isCompact_window F D β a δ).isClosed.preimage hc

theorem measurableSet_slice (F : MvPolynomial (Fin 10) ℝ) (D : Data F)
    (β : ℝ) (a : Fin 10 → ℝ) (δ : ℝ) (w : Complement D.cols → ℝ) :
    MeasurableSet (slice F D β a δ w) :=
  (isClosed_slice F D β a δ w).measurableSet

/-- Retaining the seven selected inequalities gives a containing slice with
the exact normalized radius δ/|β|. No sign restriction on β is imposed. -/
theorem slice_subset_selected (F : MvPolynomial (Fin 10) ℝ) (D : Data F)
    (β : ℝ) (hβ : β ≠ 0) (a : Fin 10 → ℝ) (δ : ℝ) (w : Complement D.cols → ℝ) :
    slice F D β a δ w ⊆
      sliceFiber F D.rows D.cols D.cols_injective D.box w
        (fun i => β⁻¹*a (D.rows i)) (δ/|β|) := by
  intro z hz
  obtain ⟨hx,hg⟩ := (mem_window_one_iff F D β a δ _).mp hz
  refine ⟨hx,?_⟩
  intro i
  exact (scalar_window_iff β _ (a (D.rows i)) δ hβ).mp (hg (D.rows i))

/-- One constant precedes the scalar, width, all ten output frequencies and
the untouched input slice. -/
theorem exists_uniform_bound (F : MvPolynomial (Fin 10) ℝ) (D : Data F) :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ (β : ℝ), β ≠ 0 → ∀ (δ : ℝ), 0 ≤ δ →
      ∀ (a : Fin 10 → ℝ) (w : Complement D.cols → ℝ),
      volume (slice F D β a δ w) ≤ ENNReal.ofReal (A*min 1 ((δ/|β|)^7)) := by
  obtain ⟨B,hB,hbox⟩ := D.exists_box_bound
  obtain ⟨A,hA,hbound⟩ := exists_bounded_bound F D.rows D.cols D.cols_injective
    D.domain D.box D.antiConstant D.antilipschitz D.box_subset_domain B hB hbox
  refine ⟨A,hA,?_⟩
  intro β hβ δ hδ a w
  exact (measure_mono (slice_subset_selected F D β hβ a δ w)).trans
    (hbound w (fun i => β⁻¹*a (D.rows i)) (δ/|β|) (div_nonneg hδ (abs_nonneg β)))

/-- A fixed box in the three untouched input coordinates contains every
nonempty slice, independently of scalar, width and output frequencies. -/
def complementBox (F : MvPolynomial (Fin 10) ℝ) (D : Data F) :
    Set (Complement D.cols → ℝ) :=
  Set.Icc (fun i => D.point i-2*D.radius) (fun i => D.point i+2*D.radius)

theorem card_complement_cols (F : MvPolynomial (Fin 10) ℝ) (D : Data F) :
    Fintype.card (Complement D.cols) = 3 := by
  have h := Fintype.card_congr (indexEquiv D.cols D.cols_injective)
  simp only [Fintype.card_sum, Fintype.card_fin] at h
  omega

theorem volume_complementBox (F : MvPolynomial (Fin 10) ℝ) (D : Data F) :
    volume (complementBox F D) = ENNReal.ofReal ((4*D.radius)^3) := by
  rw [complementBox, Real.volume_Icc_pi]
  have he (i : Complement D.cols) :
      (D.point i+2*D.radius)-(D.point i-2*D.radius)=4*D.radius := by ring
  simp only [he, Finset.prod_const, Finset.card_univ, card_complement_cols,
    ENNReal.ofReal_pow (mul_nonneg (by norm_num : (0:ℝ) ≤ 4) D.radius_pos.le)]

theorem volume_complementBox_ne_top (F : MvPolynomial (Fin 10) ℝ) (D : Data F) :
    volume (complementBox F D) ≠ ⊤ := by
  rw [volume_complementBox]
  exact ENNReal.ofReal_ne_top

theorem mem_complementBox_of_mem_slice (F : MvPolynomial (Fin 10) ℝ) (D : Data F)
    (β : ℝ) (a : Fin 10 → ℝ) (δ : ℝ) (w : Complement D.cols → ℝ)
    (z : Fin 7 → ℝ) (hz : z ∈ slice F D β a δ w) : w ∈ complementBox F D := by
  have hx := ((mem_window_one_iff F D β a δ _).mp hz).1
  have hb : ∀ i : Complement D.cols, |w i-D.point i| ≤ 2*D.radius := by
    intro i
    have hi := (norm_le_pi_norm
      (combine D.cols D.cols_injective z w-D.point) i.val).trans hx
    simpa only [Pi.sub_apply, combine_complement, Real.norm_eq_abs] using hi
  exact ⟨fun i => by have h := (abs_le.mp (hb i)).1; linarith,
    fun i => by have h := (abs_le.mp (hb i)).2; linarith⟩

theorem slice_eq_empty_of_not_mem_complementBox
    (F : MvPolynomial (Fin 10) ℝ) (D : Data F)
    (β : ℝ) (a : Fin 10 → ℝ) (δ : ℝ) (w : Complement D.cols → ℝ)
    (hw : w ∉ complementBox F D) : slice F D β a δ w = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro z hz
  exact hw (mem_complementBox_of_mem_slice F D β a δ w z hz)

end CubicTenVariables.ScaledGradientSliceVolume
