import CubicTenVariables.DyadicWindowIntegral
import CubicTenVariables.DyadicOscillatoryControl

/-! Integration of the actual finite-frequency oscillatory error. All
measurability and integrability obligations are discharged for the literal
physical window. Cubic oscillatory localization is proved internally. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
namespace CubicTenVariables.DyadicFiniteLocalization
open MvPolynomial MeasureTheory RealRegularGradientChart OscillatoryLocalization
open DyadicFrequencyError DyadicPhaseSubstitution GradientWindowMeasurability
open LocalSupremumWindow DyadicWindowIntegral
open scoped BigOperators

/-- Integration of a pointwise localized estimate in the original phase shell. -/
theorem frequencyMass_le_localized (G : MvPolynomial (Fin 10) ℤ)
    (hG : G.IsHomogeneous 3) (D : Data (map (Int.castRingHom ℝ) G))
    (P φ C δ : ℝ) (N : ℕ) (hP : 0 < P) (hφ : 0 ≤ φ) (hC : 0 ≤ C)
    (q : ℕ) (a : Fin 10 → ℤ)
    (hb : ∀ θ ∈ shell φ,
      ‖scaledIntegral (map (Int.castRingHom ℝ) G) D.weight.weight P θ
        ((q : ℝ)⁻¹ • (fun i => (a i : ℝ)))‖ ≤
      C*(P^(-(N : ℝ)) + (volume (GradientWindowScaling.window
        (map (Int.castRingHom ℝ) G) D.box P ((q : ℝ)*θ)
        (fun i => (a i : ℝ)) δ)).toReal)) :
    frequencyMass G D.weight.weight P φ q a ≤
      C*(4*φ*P^(-(N : ℝ)) + ∫ θ in shell φ,
        (volume (GradientWindowScaling.window (map (Int.castRingHom ℝ) G)
          D.box P ((q : ℝ)*θ) (fun i => (a i : ℝ)) δ)).toReal) := by
  have hi := frequency_integrable G D.weight.weight D.weight.smooth.continuous
    D.weight.compact P φ hP.ne' q a
  have hw := integrableOn_window_real_comp _ (hG.map _) D P hP
    (fun i => (a i : ℝ)) δ (fun θ => (q : ℝ)*θ)
    (measurable_const.mul measurable_id) volume (shell φ) (volume_shell_ne_top φ)
  have hc : IntegrableOn (fun _ : ℝ => P^(-(N : ℝ))) (shell φ) :=
    integrableOn_const (volume_shell_ne_top φ)
  have hv : (volume (shell φ)).toReal ≤ 4*φ := by
    simpa only [ENNReal.toReal_ofReal (by positivity : 0 ≤ 4*φ)] using
      ENNReal.toReal_mono ENNReal.ofReal_ne_top (volume_shell_le φ)
  calc
    _ ≤ ∫ θ in shell φ, C*(P^(-(N : ℝ)) +
          (volume (GradientWindowScaling.window (map (Int.castRingHom ℝ) G)
            D.box P ((q : ℝ)*θ) (fun i => (a i : ℝ)) δ)).toReal) :=
      setIntegral_mono_on hi ((hc.add hw).const_mul C) (measurableSet_shell φ) hb
    _ = C*((volume (shell φ)).toReal*P^(-(N : ℝ)) + ∫ θ in shell φ,
          (volume (GradientWindowScaling.window (map (Int.castRingHom ℝ) G)
            D.box P ((q : ℝ)*θ) (fun i => (a i : ℝ)) δ)).toReal) := by
      rw [integral_const_mul,integral_add hc hw]
      simp [MeasureTheory.measureReal_def]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (add_le_add (mul_le_mul_of_nonneg_right hv (Real.rpow_nonneg hP.le _)) le_rfl) hC

/-- The original q-dependent phase is replaced by one common dyadic phase. -/
theorem weighted_window_integral_le (G : MvPolynomial (Fin 10) ℤ)
    (hG : G.IsHomogeneous 3) (D : Data (map (Int.castRingHom ℝ) G))
    (P R φ δ : ℝ) (hP : 0 < P) (hR : 0 < R) (hφ : 0 ≤ φ)
    (q : ℕ) (hq : q ∈ moduli R) (a : Fin 10 → ℤ) :
    ((q : ℝ)^10)⁻¹*(∫ θ in shell φ,
      (volume (GradientWindowScaling.window (map (Int.castRingHom ℝ) G)
        D.box P ((q : ℝ)*θ) (fun i => (a i : ℝ)) δ)).toReal) ≤
    (R^10)⁻¹*(∫ τ in annulus φ (4*φ),
      (volume (GradientWindowScaling.window (map (Int.castRingHom ℝ) G)
        D.box P (R*τ) (fun i => (a i : ℝ)) δ)).toReal) := by
  have hm := (measurable_window_real _ D P (fun i => (a i : ℝ)) δ).comp
    ((measurable_const (a := R)).mul measurable_id)
  have hi := integrableOn_window_real_comp _ (hG.map _) D P hP
    (fun i => (a i : ℝ)) δ (fun τ => R*τ)
    (measurable_const.mul measurable_id) volume (annulus φ (4*φ))
    (volume_expanded_ne_top φ hφ)
  obtain ⟨hqR,hq2R⟩ := (mem_moduli R q).mp hq
  have hs := weighted_integral_le _ hm (fun _ => ENNReal.toReal_nonneg)
    R q φ hR hqR.le hq2R hφ hi
  have he (θ : ℝ) : R*((q : ℝ)*θ/R)=(q : ℝ)*θ := by field_simp
  simpa only [Function.comp_apply,id_eq,he,shell,annulus] using hs

/-- The finite phase integral is an actual sum of finite window integrals. -/
theorem localizedError_eq_sum (G : MvPolynomial (Fin 10) ℤ)
    (hG : G.IsHomogeneous 3) (D : Data (map (Int.castRingHom ℝ) G))
    (P R φ B δ : ℝ) (hP : 0 < P) (hφ : 0 ≤ φ) :
    localizedError G (map (Int.castRingHom ℝ) G) D P R φ B δ =
      ∑ q ∈ moduli R, (R^10)⁻¹ * ∑ a ∈ frequencies 10 B,
        ‖completeCubicSum G q a‖ * (∫ τ in annulus φ (4*φ),
          (volume (GradientWindowScaling.window (map (Int.castRingHom ℝ) G)
            D.box P (R*τ) (fun i => (a i : ℝ)) δ)).toReal) := by
  have hi (q : ℕ) (a : Fin 10 → ℤ) : IntegrableOn (fun τ =>
      ‖completeCubicSum G q a‖ * (volume (GradientWindowScaling.window
        (map (Int.castRingHom ℝ) G) D.box P (R*τ) (fun i => (a i : ℝ)) δ)).toReal)
      (annulus φ (4*φ)) :=
    (integrableOn_window_real_comp _ (hG.map _) D P hP
      (fun i => (a i : ℝ)) δ (fun τ => R*τ) (measurable_const.mul measurable_id)
      volume (annulus φ (4*φ)) (volume_expanded_ne_top φ hφ)).const_mul _
  unfold localizedError integrand
  rw [integral_finset_sum _ (fun q _ => integrable_finset_sum _ (fun a _ => hi q a))]
  simp_rw [integral_finset_sum _ (fun a _ => hi _ a),integral_const_mul]
  exact Finset.mul_sum _ _ _

/-- The literal truncated dyadic error is bounded by a negligible finite
complete-sum term and the common-phase localized error. -/
theorem truncatedError_le_localized (G : MvPolynomial (Fin 10) ℤ)
    (hG : G.IsHomogeneous 3) (D : Data (map (Int.castRingHom ℝ) G))
    (P R φ B δ C : ℝ) (N : ℕ) (hP : 0 < P) (hR : 1 ≤ R)
    (hφ : 0 < φ) (hC : 0 ≤ C)
    (hb : ∀ q ∈ moduli R, ∀ a ∈ frequencies 10 B, ∀ θ ∈ shell φ,
      ‖scaledIntegral (map (Int.castRingHom ℝ) G) D.weight.weight P θ
        ((q : ℝ)⁻¹ • (fun i => (a i : ℝ)))‖ ≤
      C*(P^(-(N : ℝ)) + (volume (GradientWindowScaling.window
        (map (Int.castRingHom ℝ) G) D.box P ((q : ℝ)*θ)
        (fun i => (a i : ℝ)) δ)).toReal)) :
    truncatedError G D.weight.weight P R φ B ≤
      C*(4*φ*P^(-(N : ℝ)) *
        (∑ q ∈ moduli R, ((q : ℝ)^10)⁻¹ * ∑ a ∈ frequencies 10 B,
          ‖completeCubicSum G q a‖) +
        localizedError G (map (Int.castRingHom ℝ) G) D P R φ B δ) := by
  let J (a : Fin 10 → ℤ) : ℝ := ∫ τ in annulus φ (4*φ),
    (volume (GradientWindowScaling.window (map (Int.castRingHom ℝ) G)
      D.box P (R*τ) (fun i => (a i : ℝ)) δ)).toReal
  have hterm (q : ℕ) (hq : q ∈ moduli R) (a : Fin 10 → ℤ)
      (ha : a ∈ frequencies 10 B) :
      ((q : ℝ)^10)⁻¹*(‖completeCubicSum G q a‖*frequencyMass G D.weight.weight P φ q a) ≤
      C*((4*φ*P^(-(N : ℝ)))*((q : ℝ)^10)⁻¹*‖completeCubicSum G q a‖ +
        (R^10)⁻¹*(‖completeCubicSum G q a‖*J a)) := by
    have hm := frequencyMass_le_localized G hG D P φ C δ N hP hφ.le hC q a (hb q hq a ha)
    have hs := weighted_window_integral_le G hG D P R φ δ hP
      (zero_lt_one.trans_le hR) hφ.le q hq a
    let I : ℝ := ∫ θ in shell φ,
      (volume (GradientWindowScaling.window (map (Int.castRingHom ℝ) G)
        D.box P ((q : ℝ)*θ) (fun i => (a i : ℝ)) δ)).toReal
    change frequencyMass G D.weight.weight P φ q a ≤ C*(4*φ*P^(-(N : ℝ))+I) at hm
    change ((q : ℝ)^10)⁻¹*I ≤ (R^10)⁻¹*J a at hs
    calc
      _ ≤ ((q : ℝ)^10)⁻¹*(‖completeCubicSum G q a‖*(C*(4*φ*P^(-(N : ℝ))+I))) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hm (norm_nonneg _)) (by positivity)
      _ = C*((4*φ*P^(-(N : ℝ)))*((q : ℝ)^10)⁻¹*‖completeCubicSum G q a‖ +
          ‖completeCubicSum G q a‖*(((q : ℝ)^10)⁻¹*I)) := by ring
      _ ≤ C*((4*φ*P^(-(N : ℝ)))*((q : ℝ)^10)⁻¹*‖completeCubicSum G q a‖ +
          ‖completeCubicSum G q a‖*((R^10)⁻¹*J a)) :=
        mul_le_mul_of_nonneg_left (add_le_add le_rfl
          (mul_le_mul_of_nonneg_left hs (norm_nonneg _))) hC
      _ = _ := by ring
  rw [localizedError_eq_sum G hG D P R φ B δ hP hφ.le]
  change _ ≤ C*(4*φ*P^(-(N : ℝ)) *
    (∑ q ∈ moduli R, ((q : ℝ)^10)⁻¹ * ∑ a ∈ frequencies 10 B,
      ‖completeCubicSum G q a‖) +
    ∑ q ∈ moduli R, (R^10)⁻¹ * ∑ a ∈ frequencies 10 B,
      ‖completeCubicSum G q a‖*J a)
  calc
    _ = ∑ q ∈ moduli R, ∑ a ∈ frequencies 10 B,
        ((q : ℝ)^10)⁻¹*(‖completeCubicSum G q a‖*frequencyMass G D.weight.weight P φ q a) := by
      simp only [truncatedError,Finset.mul_sum]
    _ ≤ ∑ q ∈ moduli R, ∑ a ∈ frequencies 10 B,
        C*((4*φ*P^(-(N : ℝ)))*((q : ℝ)^10)⁻¹*‖completeCubicSum G q a‖ +
          (R^10)⁻¹*(‖completeCubicSum G q a‖*J a)) :=
      Finset.sum_le_sum fun q hq => Finset.sum_le_sum fun a ha => hterm q hq a ha
    _ = _ := by
      simp only [mul_add,Finset.sum_add_distrib,Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro q hq
      apply Finset.sum_congr rfl
      intro a ha
      ring

/-- Proved cubic localization supplies one constant and threshold before every dyadic
parameter and cutoff. No integrability premise is left to the caller. -/
theorem exists_truncatedError_le_localized
    
    (G : MvPolynomial (Fin 10) ℤ) (hG : G.IsHomogeneous 3)
    (D : Data (map (Int.castRingHom ℝ) G)) (η : ℝ) (hη : 0 < η) (N : ℕ) :
    ∃ C P₀ : ℝ, 1 ≤ C ∧ 1 ≤ P₀ ∧ ∀ P : ℝ, P₀ ≤ P →
      ∀ R φ B : ℝ, 1 ≤ R → 0 < φ →
      truncatedError G D.weight.weight P R φ B ≤
        C*(4*φ*P^(-(N : ℝ)) *
          (∑ q ∈ moduli R, ((q : ℝ)^10)⁻¹ * ∑ a ∈ frequencies 10 B,
            ‖completeCubicSum G q a‖) +
          localizedError G (map (Int.castRingHom ℝ) G) D P R φ B
            (P^η*GradientVolumeNumerics.Vzero P R φ)) := by
  obtain ⟨C,P₀,hC,hP₀,hb⟩ :=
    DyadicOscillatoryControl.exists_localization_bound D (hG.map _) η hη N
  refine ⟨C,P₀,hC,hP₀,?_⟩
  intro P hP R φ B hR hφ
  apply truncatedError_le_localized G hG D P R φ B _ C N
    (zero_lt_one.trans_le (hP₀.trans hP)) hR hφ (zero_le_one.trans hC)
  intro q hq a _ θ hθ
  obtain ⟨hqR,hq2R⟩ := (mem_moduli R q).mp hq
  exact hb P hP R φ q θ hR hφ ((zero_lt_one.trans_le hR).trans hqR) hq2R hθ.2 _

end CubicTenVariables.DyadicFiniteLocalization
