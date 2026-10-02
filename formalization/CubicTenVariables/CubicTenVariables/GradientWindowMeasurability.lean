import CubicTenVariables.AveragedGradientVolume
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Order.Lattice

/-! Measurability and finite-shell integrability of the actual gradient
window volumes, finite local maxima and their unrestricted lattice sum.
The uniform spatial bound comes from the fixed compact chart box. -/
set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.GradientWindowMeasurability
open MvPolynomial MeasureTheory RealRegularGradientChart GradientWindowScaling
open LocalSupremumWindow AveragedGradientVolume
open scoped BigOperators ENNReal
attribute [local instance] Classical.propDecidable

variable {F : MvPolynomial (Fin 10) ℝ}

/-- Joint measurability in the phase parameter and physical point. -/
theorem measurableSet_joint_window (F : MvPolynomial (Fin 10) ℝ) (D : Data F)
    (P : ℝ) (a : Fin 10 → ℝ) (δ : ℝ) :
    MeasurableSet {z : ℝ × (Fin 10 → ℝ) | z.2 ∈
      GradientWindowScaling.window F D.box P z.1 a δ} := by
  have hbox : IsClosed {z : ℝ × (Fin 10 → ℝ) | P⁻¹ • z.2 ∈ D.box} :=
    D.box_compact.isClosed.preimage (continuous_const.smul continuous_snd)
  have hg : IsClosed {z : ℝ × (Fin 10 → ℝ) |
      ∀ i, |z.1*eval z.2 (pderiv i F)-a i| ≤ δ} := by
    simp only [Set.setOf_forall]
    apply isClosed_iInter
    intro i
    exact isClosed_le
      ((continuous_fst.mul ((NormedPolynomialChart.contDiff_eval (pderiv i F)).continuous.comp
        continuous_snd)).sub continuous_const).abs continuous_const
  exact (hbox.inter hg).measurableSet

/-- The actual ENNReal-valued volume is measurable, including phase zero. -/
theorem measurable_window_volume (F : MvPolynomial (Fin 10) ℝ) (D : Data F)
    (P : ℝ) (a : Fin 10 → ℝ) (δ : ℝ) :
    Measurable (fun α : ℝ => volume (GradientWindowScaling.window F D.box P α a δ)) :=
  measurable_measure_prodMk_left (measurableSet_joint_window F D P a δ)

theorem measurable_window_real (F : MvPolynomial (Fin 10) ℝ) (D : Data F)
    (P : ℝ) (a : Fin 10 → ℝ) (δ : ℝ) :
    Measurable (fun α : ℝ =>
      (volume (GradientWindowScaling.window F D.box P α a δ)).toReal) :=
  (measurable_window_volume F D P a δ).ennreal_toReal

/-- The containing compact-box bound before any real conversion. -/
theorem window_volume_le (F : MvPolynomial (Fin 10) ℝ) (hF : F.IsHomogeneous 3)
    (D : Data F) (P : ℝ) (hP : 0 < P) (α : ℝ) (a : Fin 10 → ℝ) (δ : ℝ) :
    volume (GradientWindowScaling.window F D.box P α a δ) ≤
      ENNReal.ofReal (P^10)*volume D.box := by
  rw [PhysicalGradientWindow.volume_window F hF D P hP]
  apply mul_le_mul_right
  apply measure_mono
  intro x hx
  simpa only [GradientWindowScaling.window,Set.mem_setOf_eq,inv_one,one_smul] using hx.1

theorem window_real_nonneg (F : MvPolynomial (Fin 10) ℝ) (D : Data F)
    (P α : ℝ) (a : Fin 10 → ℝ) (δ : ℝ) :
    0 ≤ (volume (GradientWindowScaling.window F D.box P α a δ)).toReal :=
  ENNReal.toReal_nonneg

/-- A fixed compact spatial bound is uniform in phase, frequency and width.
Finiteness of the containing measure is proved before converting to real. -/
theorem window_real_le (F : MvPolynomial (Fin 10) ℝ) (hF : F.IsHomogeneous 3)
    (D : Data F) (P : ℝ) (hP : 0 < P) (α : ℝ) (a : Fin 10 → ℝ) (δ : ℝ) :
    (volume (GradientWindowScaling.window F D.box P α a δ)).toReal ≤
      P^10*(volume D.box).toReal := by
  rw [PhysicalGradientWindow.volume_window_toReal F hF D P hP]
  apply mul_le_mul_of_nonneg_left _ (pow_nonneg hP.le 10)
  apply ENNReal.toReal_mono D.box_compact.measure_lt_top.ne
  apply measure_mono
  intro x hx
  simpa only [GradientWindowScaling.window,Set.mem_setOf_eq,inv_one,one_smul] using hx.1

/-- Integrability on every finite-measure phase set, for any real measure. -/
theorem integrableOn_window_real (F : MvPolynomial (Fin 10) ℝ) (hF : F.IsHomogeneous 3)
    (D : Data F) (P : ℝ) (hP : 0 < P) (a : Fin 10 → ℝ) (δ : ℝ)
    (μ : Measure ℝ) (E : Set ℝ) (hE : μ E ≠ ⊤) :
    IntegrableOn (fun α : ℝ =>
      (volume (GradientWindowScaling.window F D.box P α a δ)).toReal) E μ := by
  apply (integrableOn_const (C := P^10*(volume D.box).toReal) hE).mono'
    (measurable_window_real F D P a δ).aestronglyMeasurable
  exact Filter.Eventually.of_forall fun α => by
    simpa only [Real.norm_eq_abs,abs_of_nonneg ENNReal.toReal_nonneg] using
      window_real_le F hF D P hP α a δ

/-- The same bound proves integrability after any measurable phase
substitution, including multiplication by zero or a negative scalar. -/
theorem integrableOn_window_real_comp (F : MvPolynomial (Fin 10) ℝ)
    (hF : F.IsHomogeneous 3) (D : Data F) (P : ℝ) (hP : 0 < P)
    (a : Fin 10 → ℝ) (δ : ℝ) (κ : ℝ → ℝ) (hκ : Measurable κ)
    (μ : Measure ℝ) (E : Set ℝ) (hE : μ E ≠ ⊤) :
    IntegrableOn (fun θ : ℝ =>
      (volume (GradientWindowScaling.window F D.box P (κ θ) a δ)).toReal) E μ := by
  apply (integrableOn_const (C := P^10*(volume D.box).toReal) hE).mono'
    ((measurable_window_real F D P a δ).comp hκ).aestronglyMeasurable
  exact Filter.Eventually.of_forall fun θ => by
    simpa only [Function.comp_apply,Real.norm_eq_abs,abs_of_nonneg ENNReal.toReal_nonneg] using
      window_real_le F hF D P hP (κ θ) a δ

/-- Measurability of a maximum over an actual fixed finite lattice window. -/
theorem measurable_maximum (S : Finset (Fin 10 → ℤ))
    (g : ℝ → (Fin 10 → ℤ) → ℝ) (hg : ∀ a ∈ S, Measurable (fun α => g α a))
    (v : Fin 10 → ℤ) (L : ℝ) :
    Measurable (fun α : ℝ => maximum S (g α) v L) := by
  by_cases h : (LocalSupremumWindow.window S v L).Nonempty
  · simp only [maximum,dif_pos h]
    have hm := Finset.measurable_sup' h
      (f := fun a α => g α a)
      (fun a ha => hg a ((mem_window S v a L).mp ha).1)
    convert hm using 1
    ext α
    simp
  · simpa only [maximum,dif_neg h] using (measurable_const (a := (0 : ℝ)))

theorem measurable_localMaximum (F : MvPolynomial (Fin 10) ℝ) (D : Data F)
    (P B δ L : ℝ) (v : Fin 10 → ℤ) :
    Measurable (fun α : ℝ => localMaximum F D.box P α B δ L v) :=
  measurable_maximum (frequencies 10 B) _
    (fun a _ => measurable_window_real F D P (fun i => (a i : ℝ)) δ) v L

theorem localMaximum_le (F : MvPolynomial (Fin 10) ℝ) (hF : F.IsHomogeneous 3)
    (D : Data F) (P : ℝ) (hP : 0 < P) (α B δ L : ℝ) (v : Fin 10 → ℤ) :
    localMaximum F D.box P α B δ L v ≤ P^10*(volume D.box).toReal := by
  apply maximum_le _ _ _ _ _ (mul_nonneg (pow_nonneg hP.le 10) ENNReal.toReal_nonneg)
  intro a _
  exact window_real_le F hF D P hP α _ δ

theorem integrableOn_localMaximum (F : MvPolynomial (Fin 10) ℝ) (hF : F.IsHomogeneous 3)
    (D : Data F) (P : ℝ) (hP : 0 < P) (B δ L : ℝ) (v : Fin 10 → ℤ)
    (μ : Measure ℝ) (E : Set ℝ) (hE : μ E ≠ ⊤) :
    IntegrableOn (fun α : ℝ => localMaximum F D.box P α B δ L v) E μ := by
  apply (integrableOn_const (C := P^10*(volume D.box).toReal) hE).mono'
    (measurable_localMaximum F D P B δ L v).aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro α
  have hn : 0 ≤ localMaximum F D.box P α B δ L v :=
    maximum_nonneg _ _ (fun _ _ => ENNReal.toReal_nonneg) _ _
  simpa only [Real.norm_eq_abs,abs_of_nonneg hn] using
    localMaximum_le F hF D P hP α B δ L v

theorem integrableOn_localMaximum_comp (F : MvPolynomial (Fin 10) ℝ)
    (hF : F.IsHomogeneous 3) (D : Data F) (P : ℝ) (hP : 0 < P)
    (B δ L : ℝ) (v : Fin 10 → ℤ) (κ : ℝ → ℝ) (hκ : Measurable κ)
    (μ : Measure ℝ) (E : Set ℝ) (hE : μ E ≠ ⊤) :
    IntegrableOn (fun θ : ℝ => localMaximum F D.box P (κ θ) B δ L v) E μ := by
  apply (integrableOn_const (C := P^10*(volume D.box).toReal) hE).mono'
    ((measurable_localMaximum F D P B δ L v).comp hκ).aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro θ
  have hn : 0 ≤ localMaximum F D.box P (κ θ) B δ L v :=
    maximum_nonneg _ _ (fun _ _ => ENNReal.toReal_nonneg) _ _
  simpa only [Function.comp_apply,Real.norm_eq_abs,abs_of_nonneg hn] using
    localMaximum_le F hF D P hP (κ θ) B δ L v

/-- The finite set of possible lattice centers is independent of phase. -/
theorem volumeSum_eq_finite (F : MvPolynomial (Fin 10) ℝ) (D : Data F)
    (P α B δ L : ℝ) :
    volumeSum F D.box P α B δ L =
      ∑ v ∈ centers (frequencies 10 B) ⌈max L 0⌉₊, localMaximum F D.box P α B δ L v :=
  tsum_maximum_eq_sum _ _ L

theorem measurable_volumeSum (F : MvPolynomial (Fin 10) ℝ) (D : Data F)
    (P B δ L : ℝ) : Measurable (fun α : ℝ => volumeSum F D.box P α B δ L) := by
  simp_rw [volumeSum_eq_finite F D P]
  exact Finset.measurable_sum _ fun v _ => measurable_localMaximum F D P B δ L v

theorem integrableOn_volumeSum (F : MvPolynomial (Fin 10) ℝ) (hF : F.IsHomogeneous 3)
    (D : Data F) (P : ℝ) (hP : 0 < P) (B δ L : ℝ)
    (μ : Measure ℝ) (E : Set ℝ) (hE : μ E ≠ ⊤) :
    IntegrableOn (fun α : ℝ => volumeSum F D.box P α B δ L) E μ := by
  simp_rw [volumeSum_eq_finite F D P]
  exact integrable_finset_sum _ fun v _ => integrableOn_localMaximum F hF D P hP B δ L v μ E hE

theorem integrableOn_volumeSum_comp (F : MvPolynomial (Fin 10) ℝ)
    (hF : F.IsHomogeneous 3) (D : Data F) (P : ℝ) (hP : 0 < P)
    (B δ L : ℝ) (κ : ℝ → ℝ) (hκ : Measurable κ)
    (μ : Measure ℝ) (E : Set ℝ) (hE : μ E ≠ ⊤) :
    IntegrableOn (fun θ : ℝ => volumeSum F D.box P (κ θ) B δ L) E μ := by
  simp_rw [volumeSum_eq_finite F D P]
  exact integrable_finset_sum _ fun v _ =>
    integrableOn_localMaximum_comp F hF D P hP B δ L v κ hκ μ E hE

/-- Exact integration of the lattice sum as a finite sum of integrals. -/
theorem integral_volumeSum_eq_sum (F : MvPolynomial (Fin 10) ℝ) (hF : F.IsHomogeneous 3)
    (D : Data F) (P : ℝ) (hP : 0 < P) (B δ L : ℝ)
    (μ : Measure ℝ) (E : Set ℝ) (hE : μ E ≠ ⊤) :
    (∫ α in E, volumeSum F D.box P α B δ L ∂μ) =
      ∑ v ∈ centers (frequencies 10 B) ⌈max L 0⌉₊,
        ∫ α in E, localMaximum F D.box P α B δ L v ∂μ := by
  simp_rw [volumeSum_eq_finite F D P]
  exact integral_finset_sum _ fun v _ => integrableOn_localMaximum F hF D P hP B δ L v μ E hE

end CubicTenVariables.GradientWindowMeasurability
