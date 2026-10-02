import CubicTenVariables.LocalizedFrequencyComparison

/-! The elementary absolute-mass bound for the literal physical integral.
Continuity and compact support give genuine integrability. No homogeneity,
geometric hypothesis or literature input is used. The localized coefficient
corollary retains the exact lcm normalization, in every dimension. -/
set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.OscillatoryTrivialBound
open MvPolynomial MeasureTheory OscillatoryLocalization
open scoped BigOperators Topology
variable {n : ℕ}

theorem scaled_weight_integrable (w : (Fin n → ℝ) → ℝ)
    (hw : Continuous w) (hc : HasCompactSupport w) (P : ℝ) (hP : P ≠ 0) :
    Integrable (fun x : Fin n → ℝ => w (P⁻¹ • x)) := by
  have hs : HasCompactSupport (fun x : Fin n → ℝ => w (P⁻¹ • x)) := by
    have h := chartWeight_compact w hc (0 : Fin n → ℝ) P hP
    change HasCompactSupport (fun x => w (P⁻¹ • (x-0))) at h
    simpa only [sub_zero] using h
  exact Continuous.integrable_of_hasCompactSupport (by fun_prop) hs

/-- The phase has modulus one; the physical integrand is integrable even
when the weight is merely continuous. -/
theorem scaled_integrand_integrable (F : MvPolynomial (Fin n) ℝ)
    (w : (Fin n → ℝ) → ℝ) (hw : Continuous w) (hc : HasCompactSupport w)
    (P θ : ℝ) (β : Fin n → ℝ) (hP : P ≠ 0) :
    Integrable (fun x : Fin n → ℝ => (w (P⁻¹ • x) : ℂ)*Complex.exp
      (2*(Real.pi : ℂ)*Complex.I*((θ*eval x F-∑ i,β i*x i : ℝ) : ℂ))) := by
  have hs : HasCompactSupport (fun x : Fin n → ℝ => w (P⁻¹ • x)) := by
    have h := chartWeight_compact w hc (0 : Fin n → ℝ) P hP
    change HasCompactSupport (fun x => w (P⁻¹ • (x-0))) at h
    simpa only [sub_zero] using h
  apply Continuous.integrable_of_hasCompactSupport
  · have hF := F.continuous_eval
    fun_prop
  · exact (hs.comp_left (g := fun t : ℝ => (t : ℂ)) (by simp)).mul_right

/-- The exact Jacobian for the absolute mass of the scaled weight. -/
theorem scaled_absolute_mass (w : (Fin n → ℝ) → ℝ) (P : ℝ) (hP : 0 ≤ P) :
    (∫ x : Fin n → ℝ, |w (P⁻¹ • x)|) = P^n * ∫ x : Fin n → ℝ, |w x| := by
  simpa only [Module.finrank_pi,Fintype.card_fin,smul_eq_mul] using
    Measure.integral_comp_inv_smul_of_nonneg volume (fun x : Fin n → ℝ => |w x|) hP

/-- Uniform in the entire polynomial phase and all frequencies. -/
theorem norm_scaledIntegral_le (F : MvPolynomial (Fin n) ℝ)
    (w : (Fin n → ℝ) → ℝ) (hw : Continuous w) (hc : HasCompactSupport w)
    (P : ℝ) (hP : 0 < P) (θ : ℝ) (β : Fin n → ℝ) :
    ‖scaledIntegral F w P θ β‖ ≤ P^n * ∫ x : Fin n → ℝ, |w x| := by
  rw [← scaled_absolute_mass w P hP.le]
  apply norm_integral_le_of_norm_le (scaled_weight_integrable w hw hc P hP.ne').abs
  exact Filter.Eventually.of_forall fun x => by
    simp [Complex.norm_exp,Complex.mul_re,Complex.mul_im]

/-- The covolume cancels the full lattice-point loss in the localized
complete sum. This bounds every individual frequency, including zero. -/
theorem norm_normalized_localized_term_le (G : MvPolynomial (Fin n) ℤ)
    (w : (Fin n → ℝ) → ℝ) (hw : Continuous w) (hc : HasCompactSupport w)
    (P : ℝ) (hP : 0 < P) (q W : ℕ) (hq : 0 < q) (hW : 0 < W)
    (Ω : Set (Fin n → ZMod W)) (θ : ℝ) (v : Fin n → ℤ) :
    ‖((Nat.lcm q W:ℂ)^n)⁻¹ *
      (localizedCompleteCubicSum G q W Ω v *
        scaledIntegral (map (Int.castRingHom ℝ) G) w P θ (localizedFrequency q W v))‖ ≤
      (q:ℝ)*P^n*(∫ x : Fin n → ℝ, |w x|) := by
  have hl : (0:ℝ) < Nat.lcm q W := by exact_mod_cast Nat.lcm_pos hq hW
  have hmass : 0 ≤ ∫ x : Fin n → ℝ, |w x| := integral_nonneg fun _ => abs_nonneg _
  have hsum := LocalizedFrequencyComparison.trivial_bound G q W hq hW Ω v
  have hint := norm_scaledIntegral_le (map (Int.castRingHom ℝ) G) w hw hc P hP θ
    (localizedFrequency q W v)
  simp only [norm_mul,norm_inv,norm_pow,Complex.norm_natCast]
  calc
    _ ≤ ((Nat.lcm q W:ℝ)^n)⁻¹ *
        (((q:ℝ)*(Nat.lcm q W:ℝ)^n)*(P^n*(∫ x : Fin n → ℝ, |w x|))) := by
      gcongr
    _ = _ := by field_simp

end CubicTenVariables.OscillatoryTrivialBound
