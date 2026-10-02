import CubicTenVariables.SmoothDeltaKernel
import CubicTenVariables.ScaledFourierL1Decay

/-! The Fourier estimate for the actual finite smooth delta amplitude.
The scaled derivative integral bounds remain explicit here. Proving those
bounds, uniformly in `Q,q`, is the separate analytic kernel problem. -/

set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.SmoothDeltaDecay
open MeasureTheory SmoothDeltaKernel
open scoped FourierTransform ContDiff

theorem amplitude_iteratedDeriv_integrable (Q q j : ℕ) :
    Integrable (iteratedDeriv j (amplitude Q q)) := by
  apply ((amplitude_contDiff Q q).continuous_iteratedDeriv j
    (by exact_mod_cast le_top)).integrable_of_hasCompactSupport
  rw [iteratedDeriv_eq_equiv_comp]
  exact ((amplitude_hasCompactSupport Q q).iteratedFDeriv j).comp_left (map_zero _)

/-- Literal kernel decay at the required scale `q*Q`. The hypotheses concern
the two actual derivative integrals and the actual normalizing constant. -/
theorem norm_p_le_of_integral_bounds {Q q : ℕ} (hQ : 2 ≤ Q) (hq : 1 ≤ q)
    (N : ℕ) (B C : ℝ) (hB : 0 ≤ B) (hc : c Q ≤ C)
    (h0 : (∫ y : ℝ, ‖amplitude Q q y‖) ≤ B)
    (hN : ((q : ℝ)/(Q : ℝ))^N *
      (∫ y : ℝ, ‖iteratedDeriv N (amplitude Q q) y‖) ≤ B) (θ : ℝ) :
    ‖p Q q θ‖ ≤ (C*(2 : ℝ)^N*B) *
      (1+(q : ℝ)*(Q : ℝ)*|θ|)^(-(N : ℝ)) := by
  have hQR : 0 < (Q : ℝ) := by exact_mod_cast (show 0 < Q by omega)
  have hqR : 0 < (q : ℝ) := by exact_mod_cast (show 0 < q by omega)
  have hbound := ScaledFourierL1Decay.norm_fourier_le (amplitude Q q) N
    ((amplitude_contDiff Q q).of_le (by exact_mod_cast le_top))
    (fun j _ => amplitude_iteratedDeriv_integrable Q q j)
    ((q : ℝ)/(Q : ℝ)) B (div_pos hqR hQR) h0 hN ((Q : ℝ)^2*θ)
  have he : (q : ℝ)/(Q : ℝ)*|((Q : ℝ)^2*θ)| =
      (q : ℝ)*(Q : ℝ)*|θ| := by
    rw [abs_mul,abs_of_nonneg (sq_nonneg _)]
    field_simp
  rw [he] at hbound
  have hp : ‖p Q q θ‖ = c Q * ‖𝓕 (amplitude Q q) ((Q : ℝ)^2*θ)‖ := by
    rw [p,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (c_pos hQ)]
    rfl
  rw [hp]
  calc
    _ ≤ c Q * ((2 : ℝ)^N*B*(1+(q : ℝ)*(Q : ℝ)*|θ|)^(-(N : ℝ))) :=
      mul_le_mul_of_nonneg_left hbound (c_pos hQ).le
    _ ≤ C * ((2 : ℝ)^N*B*(1+(q : ℝ)*(Q : ℝ)*|θ|)^(-(N : ℝ))) :=
      mul_le_mul_of_nonneg_right hc (by positivity)
    _ = _ := by ring

/-- Uniform derivative integrals and bounded normalization imply uniform
rapid decay. The constants precede both modulus parameters. -/
theorem rapid_decay_of_integral_bounds
    (hc : ∃ C : ℝ, 1 ≤ C ∧ ∀ Q, 2 ≤ Q → c Q ≤ C)
    (hd : ∀ N : ℕ, ∃ B : ℝ, 1 ≤ B ∧
      ∀ Q : ℕ, 2 ≤ Q → ∀ q : ℕ, 1 ≤ q → q ≤ Q →
        ((q : ℝ)/(Q : ℝ))^N *
          (∫ y : ℝ, ‖iteratedDeriv N (amplitude Q q) y‖) ≤ B) :
    ∀ N : ℕ, ∃ C : ℝ, 1 ≤ C ∧
      ∀ Q, 2 ≤ Q → ∀ q, 1 ≤ q → q ≤ Q → ∀ θ : ℝ,
        ‖p Q q θ‖ ≤ C*(1+(q : ℝ)*(Q : ℝ)*|θ|)^(-(N : ℝ)) := by
  obtain ⟨C,hC,hc⟩ := hc
  obtain ⟨B0,hB0,h0⟩ := hd 0
  intro N
  obtain ⟨BN,hBN,hN⟩ := hd N
  let D := C*(2 : ℝ)^N*max B0 BN
  refine ⟨max 1 D,le_max_left _ _,?_⟩
  intro Q hQ q hq hqQ θ
  have hlow : (∫ y : ℝ, ‖amplitude Q q y‖) ≤ max B0 BN := by
    have hh : (∫ y : ℝ, ‖amplitude Q q y‖) ≤ B0 := by
      simpa only [pow_zero,one_mul,iteratedDeriv_zero] using h0 Q hQ q hq hqQ
    exact hh.trans (le_max_left _ _)
  have hhigh : ((q : ℝ)/(Q : ℝ))^N *
      (∫ y : ℝ, ‖iteratedDeriv N (amplitude Q q) y‖) ≤ max B0 BN :=
    (hN Q hQ q hq hqQ).trans (le_max_right _ _)
  apply (norm_p_le_of_integral_bounds hQ hq N (max B0 BN) C
    ((zero_le_one.trans hB0).trans (le_max_left _ _)) (hc Q hQ) hlow hhigh θ).trans
  exact mul_le_mul_of_nonneg_right (le_max_right 1 D) (Real.rpow_nonneg (by positivity) _)

end CubicTenVariables.SmoothDeltaDecay
