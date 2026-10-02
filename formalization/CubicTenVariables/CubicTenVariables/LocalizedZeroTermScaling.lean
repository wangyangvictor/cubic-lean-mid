import CubicTenVariables.LocalizedPoissonCount
import CubicTenVariables.RescaledDeltaArc
import CubicTenVariables.SingularIntegral

/-! Exact rescaling of the localized zero-frequency term. The arithmetic
coefficient is the literal localized singular-series term, and the real
integral uses the same weight as the counting function. Convergence and
positivity are separate obligations, not inferred from totalized identities. -/
set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.LocalizedZeroTermScaling
open MvPolynomial MeasureTheory OscillatoryLocalization LocalizedPoissonArc
open scoped BigOperators
variable {n : ℕ}

theorem scaledIntegral_zero (F : MvPolynomial (Fin n) ℝ) (hF : F.IsHomogeneous 3)
    (w : (Fin n → ℝ) → ℝ) (P θ : ℝ) (hP : 0 < P) :
    scaledIntegral F w P θ 0 = P^n • cubicOscillatoryIntegral F w (P^3*θ) := by
  let J : (Fin n → ℝ) → ℂ := fun x => (w (P⁻¹ • x) : ℂ)*Complex.exp
    (2*(Real.pi:ℂ)*Complex.I*((θ*eval x F:ℝ):ℂ))
  have hs := Measure.integral_comp_smul_of_nonneg volume J P (hR := hP.le)
  rw [Module.finrank_pi,Fintype.card_fin] at hs
  have he : (fun x => J (P • x)) = cubicOscillatoryIntegrand F w (P^3*θ) := by
    funext x
    dsimp [J,cubicOscillatoryIntegrand]
    rw [inv_smul_smul₀ hP.ne',eval_homogeneous_smul F hF]
    congr 2
    push_cast
    ring
  rw [he] at hs
  have hid : scaledIntegral F w P θ 0 = ∫ x, J x := by
    simp [scaledIntegral,PolynomialOscillatory.integral,J]
  rw [hid]
  change _ = P^n • ∫ x, cubicOscillatoryIntegrand F w (P^3*θ) x
  rw [hs,smul_smul]
  simp [hP.ne']

theorem zeroContribution_eq (G : MvPolynomial (Fin n) ℤ) (hG : G.IsHomogeneous 3)
    (w : (Fin n → ℝ) → ℝ) (P q W : ℕ) (hP : 0 < P) (hq : 0 < q)
    (Ω : Set (Fin n → ZMod W)) (θ : ℝ) :
    zeroContribution G w P q W Ω θ =
      (P:ℂ)^n * localizedSingularSeriesTerm G W Ω q *
        cubicOscillatoryIntegral (map (Int.castRingHom ℝ) G) w ((P:ℝ)^3*θ) := by
  have hf : localizedFrequency q W (0 : Fin n → ℤ) = 0 := by
    ext i
    simp [localizedFrequency]
  rw [zeroContribution,LocalizedPoisson.frequencyTerm,hf,
    scaledIntegral_zero _ (hG.map _) w (P:ℝ) θ (by exact_mod_cast hP)]
  simp only [localizedSingularSeriesTerm,if_neg hq.ne',Complex.real_smul,
    Complex.ofReal_pow,Complex.ofReal_natCast,div_eq_mul_inv]
  ring

/-- Exact rescaled zero-frequency integral in arbitrary dimension. -/
theorem zeroTerm_eq (G : MvPolynomial (Fin n) ℤ) (hG : G.IsHomogeneous 3)
    (w : (Fin n → ℝ) → ℝ) (P Q W : ℕ) (hP : 0 < P)
    (Ω : Set (Fin n → ZMod W)) (η : ℝ) (p : ℕ → ℕ → ℝ → ℂ) :
    LocalizedPoissonCount.zeroTerm G w P Q W Ω η p =
      ((P:ℂ)^n / (P:ℂ)^3) * ∑ q ∈ Finset.Icc 1 Q,
        localizedSingularSeriesTerm G W Ω q *
          RescaledDeltaArc.integral p (P:ℝ) Q q η
            (cubicOscillatoryIntegral (map (Int.castRingHom ℝ) G) w) := by
  unfold LocalizedPoissonCount.zeroTerm
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro q hq
  have hqpos : 0 < q := (Finset.mem_Icc.mp hq).1
  simp_rw [zeroContribution_eq G hG w P q W hP hqpos Ω]
  have hi : (fun θ : ℝ => p Q q θ *
      ((P:ℂ)^n * localizedSingularSeriesTerm G W Ω q *
        cubicOscillatoryIntegral (map (Int.castRingHom ℝ) G) w ((P:ℝ)^3*θ))) =
      fun θ => ((P:ℂ)^n * localizedSingularSeriesTerm G W Ω q) *
        (p Q q θ*cubicOscillatoryIntegral (map (Int.castRingHom ℝ) G) w
          ((P:ℝ)^3*θ)) := by funext θ; ring
  rw [hi,integral_const_mul,RescaledDeltaArc.original_eq p (P:ℝ)
    (by exact_mod_cast hP)]
  simp only [Complex.real_smul,Complex.ofReal_inv,Complex.ofReal_pow,
    Complex.ofReal_natCast,div_eq_mul_inv]
  ring

/-- In ten variables the Jacobian is exactly P^7, on the original q≤Q range. -/
theorem zeroTerm_eq_ten (G : MvPolynomial (Fin 10) ℤ) (hG : G.IsHomogeneous 3)
    (w : (Fin 10 → ℝ) → ℝ) (P Q W : ℕ) (hP : 0 < P)
    (Ω : Set (Fin 10 → ZMod W)) (η : ℝ) (p : ℕ → ℕ → ℝ → ℂ) :
    LocalizedPoissonCount.zeroTerm G w P Q W Ω η p =
      (P:ℂ)^7 * ∑ q ∈ Finset.Icc 1 Q,
        localizedSingularSeriesTerm G W Ω q *
          RescaledDeltaArc.integral p (P:ℝ) Q q η
            (cubicOscillatoryIntegral (map (Int.castRingHom ℝ) G) w) := by
  rw [zeroTerm_eq G hG w P Q W hP Ω η p]
  congr 1
  have hp : (P:ℂ) ≠ 0 := by exact_mod_cast hP.ne'
  field_simp

end CubicTenVariables.LocalizedZeroTermScaling
