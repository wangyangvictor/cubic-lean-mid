import CubicTenVariables.GradientChartVolume
import CubicTenVariables.OscillatoryLocalizationWindow

/-! Exact scaling of literal cubic-gradient windows in Lebesgue measure. -/
set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.GradientWindowScaling
open MvPolynomial MeasureTheory OscillatoryLocalization GradientChartVolume
open scoped BigOperators
variable {n : ℕ}

/-- Physical points whose normalized locations lie in K and whose actual
cubic gradients lie in the displayed translated box. -/
def window (F : MvPolynomial (Fin n) ℝ) (K : Set (Fin n → ℝ))
    (P α : ℝ) (v : Fin n → ℝ) (Δ : ℝ) : Set (Fin n → ℝ) :=
  {x | P⁻¹ • x ∈ K ∧ ∀ i, |α*eval x (pderiv i F)-v i| ≤ Δ}

theorem scalar_window_iff (a b v Δ : ℝ) (ha : a ≠ 0) :
    |a*b-v| ≤ Δ ↔ |b-a⁻¹*v| ≤ Δ/|a| := by
  have he : a*b-v=a*(b-a⁻¹*v) := by field_simp
  rw [he,abs_mul,le_div_iff₀ (abs_pos.mpr ha)]
  rw [mul_comm |a|]

theorem mem_window_smul (F : MvPolynomial (Fin n) ℝ) (hF : F.IsHomogeneous 3)
    (K : Set (Fin n → ℝ)) (P α : ℝ) (hP : 0 < P) (hα : α ≠ 0)
    (v y : Fin n → ℝ) (Δ : ℝ) :
    P • y ∈ window F K P α v Δ ↔
      y ∈ fiber F K ((α*P^2)⁻¹ • v) (Δ/(|α| * P^2)) := by
  simp only [window,fiber,Set.mem_setOf_eq,inv_smul_smul₀ hP.ne']
  apply and_congr_right
  intro _
  apply forall_congr'
  intro i
  have hpartial := eval_homogeneous_smul (pderiv i F) hF.pderiv P y
  change eval (P • y) (pderiv i F)=P^2*eval y (pderiv i F) at hpartial
  rw [hpartial,← mul_assoc]
  have h := scalar_window_iff (α*P^2) (eval y (pderiv i F)) (v i) Δ
    (mul_ne_zero hα (pow_ne_zero _ hP.ne'))
  simpa only [Pi.smul_apply,smul_eq_mul,abs_mul,abs_of_pos (pow_pos hP 2)] using h

theorem window_eq_image (F : MvPolynomial (Fin n) ℝ) (hF : F.IsHomogeneous 3)
    (K : Set (Fin n → ℝ)) (P α : ℝ) (hP : 0 < P) (hα : α ≠ 0)
    (v : Fin n → ℝ) (Δ : ℝ) :
    window F K P α v Δ = (fun y => P • y) ''
      fiber F K ((α*P^2)⁻¹ • v) (Δ/(|α| * P^2)) := by
  ext x
  constructor
  · intro hx
    refine ⟨P⁻¹ • x,?_,smul_inv_smul₀ hP.ne' x⟩
    apply (mem_window_smul F hF K P α hP hα v (P⁻¹ • x) Δ).mp
    simpa only [smul_inv_smul₀ hP.ne'] using hx
  · rintro ⟨y,hy,rfl⟩
    exact (mem_window_smul F hF K P α hP hα v y Δ).mpr hy

/-- Equality is for the actual Lebesgue measure, before real conversion. -/
theorem volume_window (F : MvPolynomial (Fin n) ℝ) (hF : F.IsHomogeneous 3)
    (K : Set (Fin n → ℝ)) (P α : ℝ) (hP : 0 < P) (hα : α ≠ 0)
    (v : Fin n → ℝ) (Δ : ℝ) :
    volume (window F K P α v Δ) = ENNReal.ofReal (P^n)*
      volume (fiber F K ((α*P^2)⁻¹ • v) (Δ/(|α| * P^2))) := by
  rw [window_eq_image F hF K P α hP hα]
  have h := volume_affine_image (0 : Fin n → ℝ) P
    (fiber F K ((α*P^2)⁻¹ • v) (Δ/(|α| * P^2)))
  simpa only [zero_add,abs_of_pos (pow_pos hP n)] using h

theorem volume_window_real (F : MvPolynomial (Fin n) ℝ) (hF : F.IsHomogeneous 3)
    (K : Set (Fin n → ℝ)) (P α : ℝ) (hP : 0 < P) (hα : α ≠ 0)
    (v : Fin n → ℝ) (Δ : ℝ) :
    (volume (window F K P α v Δ)).toReal = P^n*
      (volume (fiber F K ((α*P^2)⁻¹ • v) (Δ/(|α| * P^2)))).toReal := by
  rw [volume_window F hF K P α hP hα,ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (pow_nonneg hP.le n)]

end CubicTenVariables.GradientWindowScaling
