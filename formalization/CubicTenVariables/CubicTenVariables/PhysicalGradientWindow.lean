import CubicTenVariables.ScaledGradientSliceVolume

/-! Exact physical scaling of actual cubic-gradient windows, retaining scalar
zero and all ten window inequalities. The normalized window is the existing
window at scale one. -/
set_option autoImplicit false
set_option maxHeartbeats 1500000
noncomputable section
namespace CubicTenVariables.PhysicalGradientWindow
open MvPolynomial MeasureTheory RealRegularGradientChart GradientWindowScaling
open OscillatoryLocalization

/-- Cubic homogeneity gives the exact scalar αP² in the normalized gradient.
No division by α is used. -/
theorem mem_window_smul_iff {n : ℕ} (F : MvPolynomial (Fin n) ℝ)
    (hF : F.IsHomogeneous 3) (K : Set (Fin n → ℝ))
    (P : ℝ) (hP : 0 < P) (α : ℝ) (a y : Fin n → ℝ) (δ : ℝ) :
    P • y ∈ window F K P α a δ ↔ y ∈ window F K 1 (α*P^2) a δ := by
  simp only [window,Set.mem_setOf_eq,inv_smul_smul₀ hP.ne',inv_one,one_smul]
  apply and_congr_right
  intro _
  apply forall_congr'
  intro i
  have hp := eval_homogeneous_smul (pderiv i F) hF.pderiv P y
  change eval (P • y) (pderiv i F)=P^2*eval y (pderiv i F) at hp
  rw [hp,← mul_assoc]

/-- Equality of literal sets, including α = 0 and arbitrary real width. -/
theorem window_eq_image (F : MvPolynomial (Fin 10) ℝ) (hF : F.IsHomogeneous 3)
    (D : Data F) (P : ℝ) (hP : 0 < P) (α : ℝ) (a : Fin 10 → ℝ) (δ : ℝ) :
    window F D.box P α a δ = (fun y => P • y) '' window F D.box 1 (α*P^2) a δ := by
  ext x
  constructor
  · intro hx
    refine ⟨P⁻¹ • x,?_,smul_inv_smul₀ hP.ne' x⟩
    apply (mem_window_smul_iff F hF D.box P hP α a (P⁻¹ • x) δ).mp
    simpa only [smul_inv_smul₀ hP.ne'] using hx
  · rintro ⟨y,hy,rfl⟩
    exact (mem_window_smul_iff F hF D.box P hP α a y δ).mpr hy

/-- Exact Lebesgue scaling before real conversion. -/
theorem volume_window (F : MvPolynomial (Fin 10) ℝ) (hF : F.IsHomogeneous 3)
    (D : Data F) (P : ℝ) (hP : 0 < P) (α : ℝ) (a : Fin 10 → ℝ) (δ : ℝ) :
    volume (window F D.box P α a δ) = ENNReal.ofReal (P^10)*
      volume (window F D.box 1 (α*P^2) a δ) := by
  rw [window_eq_image F hF D P hP]
  have h := volume_affine_image (0 : Fin 10 → ℝ) P
    (window F D.box 1 (α*P^2) a δ)
  simpa only [zero_add,abs_of_pos (pow_pos hP 10)] using h

theorem volume_window_toReal (F : MvPolynomial (Fin 10) ℝ) (hF : F.IsHomogeneous 3)
    (D : Data F) (P : ℝ) (hP : 0 < P) (α : ℝ) (a : Fin 10 → ℝ) (δ : ℝ) :
    (volume (window F D.box P α a δ)).toReal = P^10*
      (volume (window F D.box 1 (α*P^2) a δ)).toReal := by
  rw [volume_window F hF D P hP, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (pow_nonneg hP.le 10)]

/-- Finiteness follows from the actual normalized compact window, not from
any convention for converting infinite measure to a real number. -/
theorem isCompact_window (F : MvPolynomial (Fin 10) ℝ) (hF : F.IsHomogeneous 3)
    (D : Data F) (P : ℝ) (hP : 0 < P) (α : ℝ) (a : Fin 10 → ℝ) (δ : ℝ) :
    IsCompact (window F D.box P α a δ) := by
  rw [window_eq_image F hF D P hP]
  exact (ScaledGradientSliceVolume.isCompact_window F D (α*P^2) a δ).image
    (continuous_const.smul continuous_id)

theorem measurableSet_window (F : MvPolynomial (Fin 10) ℝ) (hF : F.IsHomogeneous 3)
    (D : Data F) (P : ℝ) (hP : 0 < P) (α : ℝ) (a : Fin 10 → ℝ) (δ : ℝ) :
    MeasurableSet (window F D.box P α a δ) :=
  (isCompact_window F hF D P hP α a δ).measurableSet

theorem volume_window_ne_top (F : MvPolynomial (Fin 10) ℝ) (hF : F.IsHomogeneous 3)
    (D : Data F) (P : ℝ) (hP : 0 < P) (α : ℝ) (a : Fin 10 → ℝ) (δ : ℝ) :
    volume (window F D.box P α a δ) ≠ ⊤ :=
  (isCompact_window F hF D P hP α a δ).measure_lt_top.ne

end CubicTenVariables.PhysicalGradientWindow
