import CubicTenVariables.Literature.PolynomialOscillatoryIntegral
import CubicTenVariables.AffinePolynomialSlice
import HessianTheorem11.LocalCubicNormalForm

/-! Controlled affine charts for the enlarged-box oscillatory input.
All chart changes, formal derivatives and integral normalizations are proved.
The only analytic estimate is the explicit generic literature premise. -/
set_option autoImplicit false
set_option maxHeartbeats 1500000
noncomputable section
namespace CubicTenVariables.OscillatoryLocalization
open MvPolynomial MeasureTheory HessianTheorem11
open HessianTheorem11.PolynomialRestriction
open scoped BigOperators Topology ContDiff

variable {n : ℕ}

def chartPoint (x₀ : Fin n → ℝ) (ρ : ℝ) (y : Fin n → ℝ) : Fin n → ℝ :=
  x₀ + ρ • y

def chartPolynomial (F : MvPolynomial (Fin n) ℝ) (x₀ : Fin n → ℝ) (ρ : ℝ) :
    MvPolynomial (Fin n) ℝ := aeval (fun i => C (x₀ i) + C ρ * X i) F

def chartWeight (w : (Fin n → ℝ) → ℝ) (x₀ : Fin n → ℝ) (ρ : ℝ) :
    (Fin n → ℝ) → ℝ := fun x => w (ρ⁻¹ • (x-x₀))

/-- Literal physical integral from the manuscript, with negative frequency. -/
def scaledIntegral (F : MvPolynomial (Fin n) ℝ) (w : (Fin n → ℝ) → ℝ)
    (P θ : ℝ) (β : Fin n → ℝ) : ℂ :=
  PolynomialOscillatory.integral F (fun x => w (P⁻¹ • x)) θ β

theorem eval_chartPolynomial (F : MvPolynomial (Fin n) ℝ)
    (x₀ : Fin n → ℝ) (ρ : ℝ) (y : Fin n → ℝ) :
    eval y (chartPolynomial F x₀ ρ) = eval (chartPoint x₀ ρ y) F := by
  change aeval y (aeval (fun i => C (x₀ i) + C ρ * X i) F) =
    aeval (chartPoint x₀ ρ y) F
  rw [comp_aeval_apply]
  have he : (fun i => aeval y (C (x₀ i) + C ρ * X i)) = chartPoint x₀ ρ y := by
    funext i
    simp [chartPoint]
  rw [he]

theorem pderiv_chartPolynomial (F : MvPolynomial (Fin n) ℝ)
    (x₀ : Fin n → ℝ) (ρ : ℝ) (j : Fin n) :
    pderiv j (chartPolynomial F x₀ ρ) =
      C ρ * chartPolynomial (pderiv j F) x₀ ρ := by
  classical
  unfold chartPolynomial
  rw [pderiv_aeval]
  simp [mul_comm,Pi.single_apply]

theorem gradient_chartPolynomial (F : MvPolynomial (Fin n) ℝ)
    (x₀ : Fin n → ℝ) (ρ : ℝ) (y : Fin n → ℝ) :
    gradient (chartPolynomial F x₀ ρ) y = ρ • gradient F (chartPoint x₀ ρ y) := by
  funext i
  simp [gradient,pderiv_chartPolynomial,eval_chartPolynomial]

theorem eval_homogeneous_smul (F : MvPolynomial (Fin n) ℝ) {d : ℕ}
    (hF : F.IsHomogeneous d) (P : ℝ) (x : Fin n → ℝ) :
    eval (P • x) F = P^d * eval x F := by
  simpa only [eval₂_id,Pi.smul_apply,smul_eq_mul] using
    LocalCubicNormalForm.homogeneous_eval₂_common_scalar F hF (RingHom.id ℝ) x P

/-- The printed enlarged unit box can be placed inside any prescribed
neighborhood of x₀. This is independent of every phase and frequency. -/
theorem exists_chart_inside (x₀ : Fin n → ℝ) (U : Set (Fin n → ℝ)) (hU : U ∈ 𝓝 x₀) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ y : Fin n → ℝ, ‖y‖ ≤ 2 → chartPoint x₀ ρ y ∈ U := by
  obtain ⟨ε,hε,hsub⟩ := Metric.mem_nhds_iff.mp hU
  refine ⟨ε/4,by positivity,?_⟩
  intro y hy
  apply hsub
  rw [Metric.mem_ball,dist_eq_norm]
  have he : chartPoint x₀ (ε/4) y-x₀=(ε/4) • y := by simp [chartPoint]
  rw [he,norm_smul,Real.norm_eq_abs,abs_of_pos (by positivity : 0 < ε/4)]
  have hm := mul_le_mul_of_nonneg_left hy (by positivity : 0 ≤ ε/4)
  linarith

@[simp] theorem chartWeight_chartPoint (w : (Fin n → ℝ) → ℝ)
    (x₀ : Fin n → ℝ) (ρ : ℝ) (hρ : ρ ≠ 0) (y : Fin n → ℝ) :
    chartWeight w x₀ ρ (chartPoint x₀ ρ y) = w y := by
  simp [chartWeight,chartPoint,hρ]

/-- Fixed chart normalization of the actual integral, including its exact
unit complex factor and the full Jacobian. -/
theorem scaledIntegral_chart (F : MvPolynomial (Fin n) ℝ)
    (hF : F.IsHomogeneous 3) (w : (Fin n → ℝ) → ℝ)
    (x₀ : Fin n → ℝ) (ρ P : ℝ) (hρ : 0 < ρ) (hP : 0 < P)
    (θ : ℝ) (β : Fin n → ℝ) :
    scaledIntegral F (chartWeight w x₀ ρ) P θ β =
      ((P*ρ)^n : ℝ) • (Complex.exp
        (2*(Real.pi : ℂ)*Complex.I*((-P*(∑ i, β i*x₀ i) : ℝ) : ℂ)) *
      PolynomialOscillatory.integral (chartPolynomial F x₀ ρ) w (θ*P^3) ((P*ρ) • β)) := by
  let J : (Fin n → ℝ) → ℂ := fun x =>
    (chartWeight w x₀ ρ (P⁻¹ • x) : ℂ) * Complex.exp
      (2*(Real.pi : ℂ)*Complex.I*((θ*eval x F-∑ i, β i*x i : ℝ) : ℂ))
  have hchange : scaledIntegral F (chartWeight w x₀ ρ) P θ β =
      ((P*ρ)^n : ℝ) • ∫ y : Fin n → ℝ, J (P • x₀+(P*ρ) • y) := by
    have hs := Measure.integral_comp_smul_of_nonneg volume
      (fun x => J (P • x₀+x)) (P*ρ) (hR := (mul_pos hP hρ).le)
    rw [Module.finrank_pi,Fintype.card_fin] at hs
    rw [hs,integral_add_left_eq_self,smul_smul]
    simp [scaledIntegral,PolynomialOscillatory.integral,J,(mul_pos hP hρ).ne']
  rw [hchange]
  congr 1
  unfold PolynomialOscillatory.integral
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with y
  have hpoint : P • x₀+(P*ρ) • y=P • chartPoint x₀ ρ y := by
    simp [chartPoint,smul_add,smul_smul]
  have hw : chartWeight w x₀ ρ (P⁻¹ • (P • x₀+(P*ρ) • y))=w y := by
    rw [hpoint,inv_smul_smul₀ hP.ne',chartWeight_chartPoint w x₀ ρ hρ.ne']
  have hf : eval (P • x₀+(P*ρ) • y) F=P^3*eval y (chartPolynomial F x₀ ρ) := by
    rw [hpoint,eval_homogeneous_smul F hF,eval_chartPolynomial]
  have hd : (∑ i, β i*(P • x₀+(P*ρ) • y) i) =
      P*(∑ i, β i*x₀ i)+(∑ i, ((P*ρ) • β) i*y i) := by
    simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul,mul_add,Finset.sum_add_distrib,
      Finset.mul_sum]
    apply congrArg₂ (· + ·) <;> apply Finset.sum_congr rfl <;> intro i hi <;> ring
  change (chartWeight w x₀ ρ (P⁻¹ • (P • x₀+(P*ρ) • y)) : ℂ) * _ = _
  rw [hw,hf,hd]
  rw [mul_left_comm (Complex.exp _) (w y : ℂ),← Complex.exp_add]
  congr 2
  push_cast
  ring

/-- The constant phase introduced by translation has norm one. -/
theorem norm_scaledIntegral_chart (F : MvPolynomial (Fin n) ℝ)
    (hF : F.IsHomogeneous 3) (w : (Fin n → ℝ) → ℝ)
    (x₀ : Fin n → ℝ) (ρ P : ℝ) (hρ : 0 < ρ) (hP : 0 < P)
    (θ : ℝ) (β : Fin n → ℝ) :
    ‖scaledIntegral F (chartWeight w x₀ ρ) P θ β‖ =
      (P*ρ)^n * ‖PolynomialOscillatory.integral (chartPolynomial F x₀ ρ)
        w (θ*P^3) ((P*ρ) • β)‖ := by
  rw [scaledIntegral_chart F hF w x₀ ρ P hρ hP θ β,norm_smul,norm_mul]
  simp [Complex.norm_exp,Complex.mul_re,Complex.mul_im,
    Real.norm_eq_abs,abs_of_pos hP,abs_of_pos hρ]

/-- Literal chart localization supplied by the generic enlarged-box lemma.
Its constants precede P, θ, β and R, and every relevant normalized y has
norm at most 2, so `exists_chart_inside` controls the entire region. -/
theorem localization_on_chart (lit : Literature.BrowningHeathBrown2009Lemma6)
    (hn : 1 ≤ n) (F : MvPolynomial (Fin n) ℝ) (hF : F.IsHomogeneous 3)
    (w : (Fin n → ℝ) → ℝ) (hw : ContDiff ℝ ∞ w) (hc : HasCompactSupport w)
    (hwn : ∀ x, 0 ≤ w x) (hs : ∀ x ∈ tsupport w, ‖x‖ ≤ 1)
    (x₀ : Fin n → ℝ) (ρ : ℝ) (hρ : 0 < ρ) :
    ∃ H : ℝ, 1 ≤ H ∧ ∀ N : ℕ, 1 ≤ N → ∃ C R₀ : ℝ, 1 ≤ C ∧ 1 ≤ R₀ ∧
      ∀ P : ℝ, 0 < P → ∀ (θ : ℝ) (β : Fin n → ℝ) (R : ℝ), R₀ ≤ R →
      ‖scaledIntegral F (chartWeight w x₀ ρ) P θ β‖ ≤
        (P*ρ)^n * C * (R^(-(N : ℝ)) +
          (volume (PolynomialOscillatory.window (chartPolynomial F x₀ ρ)
            1 H (θ*P^3) ((P*ρ) • β) R)).toReal) := by
  obtain ⟨H,hH,h⟩ := lit n hn (chartPolynomial F x₀ ρ) w hw hc hwn 1 (by norm_num) hs
  refine ⟨H,hH,?_⟩
  intro N hN
  obtain ⟨C,R₀,hC,hR₀,hbound⟩ := h N hN
  refine ⟨C,R₀,hC,hR₀,?_⟩
  intro P hP θ β R hR
  rw [norm_scaledIntegral_chart F hF w x₀ ρ P hρ hP θ β]
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left
    (hbound (θ*P^3) ((P*ρ) • β) R hR) (pow_nonneg (mul_pos hP hρ).le n)

end CubicTenVariables.OscillatoryLocalization
