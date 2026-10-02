import CubicTenVariables.CubicLocalizedFourierFamily
import CubicTenVariables.Literature.PolynomialOscillatoryIntegral
import Mathlib.MeasureTheory.Integral.Prod

/-! Exact normalized bump localization of a cubic oscillatory integral and its
shifted Fourier representation. Translation invariance proves the version in
which the two scale Jacobians have already canceled. No oscillatory estimate is
assumed, and no gradient-window conclusion is asserted. -/

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace CubicTenVariables.CubicBumpLocalization
open MvPolynomial MeasureTheory HessianTheorem11
open scoped BigOperators ContDiff Topology
variable {n : ℕ}

/-- Literal physical wave, with the negative frequency convention. -/
def wave (F : MvPolynomial (Fin n) ℝ) (w : (Fin n → ℝ) → ℝ)
    (t : ℝ) (u : Fin n → ℝ) (x : Fin n → ℝ) : ℂ :=
  (w x : ℂ) * Complex.exp
    (2 * (Real.pi : ℂ) * Complex.I * ((t * eval x F - ∑ i, u i*x i : ℝ) : ℂ))

/-- The localized integral after rescaling the bump variable. -/
def localized (F : MvPolynomial (Fin n) ℝ) (w φ : (Fin n → ℝ) → ℝ)
    (t δ : ℝ) (u y : Fin n → ℝ) : ℂ :=
  ∫ z : Fin n → ℝ, wave F w t u (y + δ • z) * (φ z : ℂ)

private def shear (δ : ℝ) :
    ((Fin n → ℝ) × (Fin n → ℝ)) ≃ₜ ((Fin n → ℝ) × (Fin n → ℝ)) where
  toFun p := (p.1 + δ • p.2,p.2)
  invFun p := (p.1 - δ • p.2,p.2)
  left_inv p := by simp
  right_inv p := by simp
  continuous_toFun := (continuous_fst.add (continuous_const.smul continuous_snd)).prodMk continuous_snd
  continuous_invFun := (continuous_fst.sub (continuous_const.smul continuous_snd)).prodMk continuous_snd

private theorem translated_product_compact (f : (Fin n → ℝ) → ℂ)
    (φ : (Fin n → ℝ) → ℝ) (hf : HasCompactSupport f) (hφ : HasCompactSupport φ)
    (δ : ℝ) : HasCompactSupport (fun p : (Fin n → ℝ) × (Fin n → ℝ) =>
      f (p.1 + δ • p.2) * (φ p.2 : ℂ)) := by
  have hp : HasCompactSupport (fun p : (Fin n → ℝ) × (Fin n → ℝ) =>
      f p.1 * (φ p.2 : ℂ)) := by
    apply HasCompactSupport.intro' (hf.prod hφ) (isClosed_closure.prod isClosed_closure)
    intro p hp
    by_cases h1 : p.1 ∈ tsupport f
    · have h2 : p.2 ∉ tsupport φ := fun h2 => hp ⟨h1,h2⟩
      simp [image_eq_zero_of_notMem_tsupport h2]
    · simp [image_eq_zero_of_notMem_tsupport h1]
  exact hp.comp_homeomorph (shear δ)

/-- Averaging a normalized bump leaves the integral unchanged. This formulation
is already normalized: no inverse scale or dimension factor remains. -/
theorem normalized_bump (f : (Fin n → ℝ) → ℂ) (φ : (Fin n → ℝ) → ℝ)
    (hf : Continuous f) (hcf : HasCompactSupport f) (hφ : Continuous φ)
    (hcφ : HasCompactSupport φ) (hnorm : ∫ z, φ z = 1) (δ : ℝ) :
    (∫ x, f x) = ∫ y : Fin n → ℝ, ∫ z : Fin n → ℝ,
      f (y + δ • z) * (φ z : ℂ) := by
  rw [integral_integral_swap_of_hasCompactSupport
    ((hf.comp (continuous_fst.add (continuous_const.smul continuous_snd))).mul
      (Complex.continuous_ofReal.comp (hφ.comp continuous_snd)))
    (translated_product_compact f φ hcf hcφ δ)]
  simp only [integral_mul_const, integral_add_right_eq_self]
  rw [integral_const_mul, integral_complex_ofReal, hnorm]
  simp

private theorem wave_continuous (F : MvPolynomial (Fin n) ℝ)
    (w : (Fin n → ℝ) → ℝ) (hw : Continuous w) (t : ℝ) (u : Fin n → ℝ) :
    Continuous (wave F w t u) := by
  apply (Complex.continuous_ofReal.comp hw).mul
  apply Complex.continuous_exp.comp
  apply continuous_const.mul
  apply Complex.continuous_ofReal.comp
  exact (continuous_const.mul (PolynomialCalculus.contDiff_eval F).continuous).sub
    (continuous_finset_sum _ fun i _ => continuous_const.mul (continuous_apply i))

private theorem wave_compact (F : MvPolynomial (Fin n) ℝ)
    (w : (Fin n → ℝ) → ℝ) (hw : HasCompactSupport w) (t : ℝ) (u : Fin n → ℝ) :
    HasCompactSupport (wave F w t u) :=
  (hw.comp_left (g := fun x : ℝ => (x : ℂ)) (by simp)).mul_right

/-- The exact normalized decomposition of the literal oscillatory integral. -/
theorem integral_eq_localized (F : MvPolynomial (Fin n) ℝ)
    (w φ : (Fin n → ℝ) → ℝ) (hw : Continuous w) (hcw : HasCompactSupport w)
    (hφ : Continuous φ) (hcφ : HasCompactSupport φ) (hnorm : ∫ z, φ z = 1)
    (t δ : ℝ) (u : Fin n → ℝ) :
    PolynomialOscillatory.integral F w t u = ∫ y, localized F w φ t δ u y :=
  normalized_bump (wave F w t u) φ (wave_continuous F w hw t u)
    (wave_compact F w hcw t u) hφ hcφ hnorm δ

/-- The Fourier frequency is exactly `δ (u − t ∇F(y))`; the omitted constant
phase has modulus one. This identity is valid even at scale zero. -/
theorem localized_eq_fourier (F : MvPolynomial (Fin n) ℝ) (hF : F.IsHomogeneous 3)
    (w φ : (Fin n → ℝ) → ℝ) (t δ : ℝ) (u y : Fin n → ℝ) :
    localized F w φ t δ u y =
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I *
        ((t * eval y F - ∑ i, u i*y i : ℝ) : ℂ)) *
      ScalarLatticePoisson.fourier
        (CubicLocalizedFourierFamily.amplitude F w φ y δ (t * δ^2))
        (δ • (u - t • gradient F y)) := by
  rw [ScalarLatticePoisson.fourier_eq_volume_integral, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with z
  have hlin : (∑ i, u i*(y + δ • z) i) =
      (∑ i, u i*y i) + δ*(∑ i, u i*z i) := by
    simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul,mul_add,Finset.sum_add_distrib]
    rw [Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hfreq : (∑ i, (δ • (u - t • gradient F y)) i*z i) =
      δ*((∑ i, u i*z i) - t*CubicTaylorExpansion.directional F y z) := by
    simp only [Pi.sub_apply,Pi.smul_apply,smul_eq_mul,CubicTaylorExpansion.directional,
      dotProduct,mul_sub,sub_mul,Finset.sum_sub_distrib,Finset.mul_sum]
    congr 1 <;> apply Finset.sum_congr rfl <;> intro i _ <;> ring
  have hphase := CubicLocalizedFourierFamily.scaled_remainder F hF y z t δ
  change wave F w t u (y + δ • z) * (φ z : ℂ) = _
  unfold wave CubicLocalizedFourierFamily.amplitude
  rw [hlin,hfreq]
  have hr : t * eval (y + δ • z) F - ((∑ i, u i*y i) + δ*(∑ i, u i*z i)) =
      (t * eval y F - ∑ i, u i*y i) +
      (t * δ^2) * CubicLocalizedFourierFamily.remainder F y δ z -
      δ*((∑ i, u i*z i) - t*CubicTaylorExpansion.directional F y z) := by
    linarith
  have hexp (a b c : ℝ) :
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (a+b-c : ℝ)) =
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (a : ℂ)) *
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (b : ℂ)) *
      Complex.exp (-2 * (Real.pi : ℂ) * Complex.I * (c : ℂ)) := by
    rw [← Complex.exp_add, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [hr,hexp]
  ring

/-- Removing the unit constant phase preserves the norm exactly. -/
theorem norm_localized_eq_fourier (F : MvPolynomial (Fin n) ℝ) (hF : F.IsHomogeneous 3)
    (w φ : (Fin n → ℝ) → ℝ) (t δ : ℝ) (u y : Fin n → ℝ) :
    ‖localized F w φ t δ u y‖ =
      ‖ScalarLatticePoisson.fourier
        (CubicLocalizedFourierFamily.amplitude F w φ y δ (t * δ^2))
        (δ • (u - t • gradient F y))‖ := by
  rw [localized_eq_fourier F hF,norm_mul]
  simp [Complex.norm_exp,Complex.mul_re,Complex.mul_im]

/-- The center lies in the enlarged box whenever both weights are nonzero. -/
theorem localized_eq_zero_outside (F : MvPolynomial (Fin n) ℝ)
    (w φ : (Fin n → ℝ) → ℝ) (S : ℝ)
    (hsw : ∀ x ∈ tsupport w, ‖x‖ ≤ S)
    (hsφ : ∀ z ∈ tsupport φ, ‖z‖ ≤ 1)
    (t δ : ℝ) (hδ : δ ∈ Set.Icc (0 : ℝ) 1) (u y : Fin n → ℝ)
    (hy : ¬ ‖y‖ ≤ S + 1) : localized F w φ t δ u y = 0 := by
  apply integral_eq_zero_of_ae
  filter_upwards [] with z
  by_cases hφz : φ z = 0
  · simp [wave,hφz]
  by_cases hwz : w (y + δ • z) = 0
  · simp [wave,hwz]
  exfalso
  apply hy
  have hz := hsφ z (subset_tsupport φ hφz)
  have hx := hsw (y + δ • z) (subset_tsupport w hwz)
  calc
    ‖y‖ = ‖(y + δ • z) - δ • z‖ := by simp
    _ ≤ ‖y + δ • z‖ + ‖δ • z‖ := norm_sub_le _ _
    _ ≤ S + 1 := by
      rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hδ.1]
      nlinarith [norm_nonneg z, hδ.1, hδ.2]

/-- Exact enlarged-center integral bound. Its constant precedes the physical
phase, frequency and positive scale. Normalization of the fixed bump is an
explicit elementary hypothesis; no oscillatory-integral estimate is an input. -/
theorem exists_integral_bound (F : MvPolynomial (Fin n) ℝ) (hF : F.IsHomogeneous 3)
    (w φ : (Fin n → ℝ) → ℝ) (hw : ContDiff ℝ ∞ w) (hcw : HasCompactSupport w)
    (hφ : ContDiff ℝ ∞ φ) (hcφ : HasCompactSupport φ) (hnorm : ∫ z, φ z = 1)
    (S : ℝ) (_hS : 0 ≤ S) (hsw : ∀ x ∈ tsupport w, ‖x‖ ≤ S)
    (hsφ : ∀ z ∈ tsupport φ, ‖z‖ ≤ 1) (Λ : ℝ) (hΛ : 0 ≤ Λ) (N : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (t : ℝ) (u : Fin n → ℝ) (δ : ℝ),
      0 < δ → δ ≤ 1 → |t * δ^2| ≤ Λ →
      ‖PolynomialOscillatory.integral F w t u‖ ≤
        C * ∫ y in Metric.closedBall (0 : Fin n → ℝ) (S+1),
          1 / (1 + δ * ‖u - t • gradient F y‖)^N := by
  let Y := Metric.closedBall (0 : Fin n → ℝ) (S+1)
  have hY : IsCompact Y := isCompact_closedBall _ _
  obtain ⟨C,hC,hbound⟩ := CubicLocalizedFourierFamily.exists_uniform_bound
    F w φ hw hφ hcφ Y hY Λ hΛ N
  refine ⟨C,hC,?_⟩
  intro t u δ hδ0 hδ1 ht
  have hδ : δ ∈ Set.Icc (0 : ℝ) 1 := ⟨hδ0.le,hδ1⟩
  have hℓ : t * δ^2 ∈ Set.Icc (-Λ) Λ := abs_le.mp ht
  have hp : ∀ y ∈ Y, ‖localized F w φ t δ u y‖ ≤
      C / (1 + δ * ‖u - t • gradient F y‖)^N := by
    intro y hy
    rw [norm_localized_eq_fourier F hF]
    simpa only [norm_smul,Real.norm_eq_abs,abs_of_pos hδ0] using
      hbound y hy δ hδ (t*δ^2) hℓ (δ • (u - t • gradient F y))
  have hz : ∀ y, y ∉ Y → localized F w φ t δ u y = 0 := by
    intro y hy
    apply localized_eq_zero_outside F w φ S hsw hsφ t δ hδ u y
    simpa only [Y,Metric.mem_closedBall,dist_zero_right] using hy
  have hcont : Continuous (fun p : (Fin n → ℝ) × (Fin n → ℝ) =>
      wave F w t u (p.1 + δ • p.2) * (φ p.2 : ℂ)) :=
    ((wave_continuous F w hw.continuous t u).comp
      (continuous_fst.add (continuous_const.smul continuous_snd))).mul
      (Complex.continuous_ofReal.comp (hφ.continuous.comp continuous_snd))
  have hint : Integrable (localized F w φ t δ u) :=
    (hcont.integrable_of_hasCompactSupport (translated_product_compact
      (wave F w t u) φ (wave_compact F w hcw t u) hcφ δ)).integral_prod_left
  have hg : Continuous (fun y : Fin n → ℝ =>
      C / (1 + δ * ‖u - t • gradient F y‖)^N) := by
    apply continuous_const.div
    · apply Continuous.pow
      apply continuous_const.add
      apply continuous_const.mul
      apply Continuous.norm
      apply continuous_const.sub
      apply continuous_const.smul
      exact continuous_pi fun i => (PolynomialCalculus.contDiff_eval (pderiv i F)).continuous
    · intro y
      exact ne_of_gt (pow_pos (by positivity) N)
  calc
    ‖PolynomialOscillatory.integral F w t u‖ = ‖∫ y, localized F w φ t δ u y‖ := by
      rw [integral_eq_localized F w φ hw.continuous hcw hφ.continuous hcφ hnorm]
    _ ≤ ∫ y, ‖localized F w φ t δ u y‖ := norm_integral_le_integral_norm _
    _ = ∫ y in Y, ‖localized F w φ t δ u y‖ :=
      (setIntegral_eq_integral_of_forall_compl_eq_zero (fun y hy => by rw [hz y hy,norm_zero])).symm
    _ ≤ ∫ y in Y, C / (1 + δ * ‖u - t • gradient F y‖)^N := by
      apply integral_mono_ae hint.norm.integrableOn (hg.continuousOn.integrableOn_compact hY)
      filter_upwards [ae_restrict_mem hY.measurableSet] with y hy
      exact hp y hy
    _ = C * ∫ y in Y, 1 / (1 + δ * ‖u - t • gradient F y‖)^N := by
      rw [← integral_const_mul]
      congr 1
      ext y
      ring

end CubicTenVariables.CubicBumpLocalization
