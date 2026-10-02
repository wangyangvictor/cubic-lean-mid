import CubicTenVariables.DyadicFiniteLocalization
import CubicTenVariables.LocalizedDyadicFrequencyError
import CubicTenVariables.LocalizedWindowIntegral
import CubicTenVariables.LocalizedOscillatoryControl
import CubicTenVariables.LocalizedPhaseSubstitution

/-! Finite-frequency localization for the actual restricted complete sums.
The original dyadic modulus q and the true oscillatory denominator lcm(q,W)
remain distinct. All window integrability obligations are proved internally. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
namespace CubicTenVariables.LocalizedFiniteLocalization
open MvPolynomial MeasureTheory RealRegularGradientChart OscillatoryLocalization
open DyadicFrequencyError DyadicPhaseSubstitution GradientWindowMeasurability
open LocalSupremumWindow LocalizedWindowIntegral
open scoped BigOperators

/-- The original q-dependent phase is replaced by one common dyadic phase. -/
theorem weighted_window_integral_le (G : MvPolynomial (Fin 10) ℤ)
    (hG : G.IsHomogeneous 3) (D : Data (map (Int.castRingHom ℝ) G))
    (W : ℕ) (hW : 0 < W) (Ω : Set (Fin 10 → ZMod W))
    (P R φ δ : ℝ) (hP : 0 < P) (hR : 0 < R) (hφ : 0 ≤ φ)
    (q : ℕ) (hq : q ∈ moduli R) (a : Fin 10 → ℤ) :
    ((Nat.lcm q W : ℝ)^10)⁻¹*(∫ θ in shell φ,
      (volume (GradientWindowScaling.window (map (Int.castRingHom ℝ) G)
        D.box P ((Nat.lcm q W : ℝ)*θ) (fun i => (a i : ℝ)) δ)).toReal) ≤
    (R^10)⁻¹*(∫ τ in annulus φ (4*(W:ℝ)*φ),
      (volume (GradientWindowScaling.window (map (Int.castRingHom ℝ) G)
        D.box P (R*τ) (fun i => (a i : ℝ)) δ)).toReal) := by
  have hm := (measurable_window_real _ D P (fun i => (a i : ℝ)) δ).comp
    ((measurable_const (a := R)).mul measurable_id)
  have hi := integrableOn_window_real_comp _ (hG.map _) D P hP
    (fun i => (a i : ℝ)) δ (fun τ => R*τ)
    (measurable_const.mul measurable_id) volume (annulus φ (4*(W:ℝ)*φ))
    (LocalizedPhaseSubstitution.volume_expanded_ne_top φ (W:ℝ))
  obtain ⟨hqR,hq2R⟩ := (mem_moduli R q).mp hq
  have hq0 : 0 < q := by exact_mod_cast hR.trans hqR
  have hbounds := LocalizedFrequencyComparison.denominator_bounds q W hq0 hW
  have hlow : R ≤ (Nat.lcm q W : ℝ) :=
    hqR.le.trans (by exact_mod_cast hbounds.1)
  have hupp : (Nat.lcm q W : ℝ) ≤ 2*((W:ℝ)*R) := by
    calc
      _ ≤ (W:ℝ)*(q:ℝ) := by exact_mod_cast hbounds.2
      _ ≤ (W:ℝ)*(2*R) := mul_le_mul_of_nonneg_left hq2R (Nat.cast_nonneg W)
      _ = _ := by ring
  have hs := LocalizedPhaseSubstitution.weighted_integral_le _ hm
    (fun _ => ENNReal.toReal_nonneg) R (Nat.lcm q W : ℝ) φ (W:ℝ)
    hR hlow hupp hφ hi
  have he (θ : ℝ) : R*((Nat.lcm q W : ℝ)*θ/R)=(Nat.lcm q W : ℝ)*θ := by field_simp
  simpa only [Function.comp_apply,id_eq,he,shell,annulus] using hs

/-- The finite phase integral is an actual sum of finite window integrals. -/
theorem localizedError_eq_sum (G : MvPolynomial (Fin 10) ℤ)
    (hG : G.IsHomogeneous 3) (D : Data (map (Int.castRingHom ℝ) G))
    (W : ℕ) (hW : 0 < W) (Ω : Set (Fin 10 → ZMod W))
    (P R φ B δ : ℝ) (hP : 0 < P) (hφ : 0 ≤ φ) :
    localizedError G W Ω (map (Int.castRingHom ℝ) G) D P R φ B δ =
      ∑ q ∈ moduli R, (R^10)⁻¹ * ∑ a ∈ frequencies 10 B,
        ‖localizedCompleteCubicSum G q W Ω a‖ * (∫ τ in annulus φ (4*(W:ℝ)*φ),
          (volume (GradientWindowScaling.window (map (Int.castRingHom ℝ) G)
            D.box P (R*τ) (fun i => (a i : ℝ)) δ)).toReal) := by
  have hi (q : ℕ) (a : Fin 10 → ℤ) : IntegrableOn (fun τ =>
      ‖localizedCompleteCubicSum G q W Ω a‖ * (volume (GradientWindowScaling.window
        (map (Int.castRingHom ℝ) G) D.box P (R*τ) (fun i => (a i : ℝ)) δ)).toReal)
      (annulus φ (4*(W:ℝ)*φ)) :=
    (integrableOn_window_real_comp _ (hG.map _) D P hP
      (fun i => (a i : ℝ)) δ (fun τ => R*τ) (measurable_const.mul measurable_id)
      volume (annulus φ (4*(W:ℝ)*φ)) (LocalizedPhaseSubstitution.volume_expanded_ne_top φ (W:ℝ))).const_mul _
  unfold localizedError integrand
  rw [integral_finset_sum _ (fun q _ => integrable_finset_sum _ (fun a _ => hi q a))]
  simp_rw [integral_finset_sum _ (fun a _ => hi _ a),integral_const_mul]
  exact Finset.mul_sum _ _ _

/-- The literal truncated dyadic error is bounded by a negligible finite
complete-sum term and the common-phase localized error. -/
theorem truncatedError_le_localized (G : MvPolynomial (Fin 10) ℤ)
    (hG : G.IsHomogeneous 3) (D : Data (map (Int.castRingHom ℝ) G))
    (W : ℕ) (hW : 0 < W) (Ω : Set (Fin 10 → ZMod W))
    (P R φ B δ C : ℝ) (N : ℕ) (hP : 0 < P) (hR : 1 ≤ R)
    (hφ : 0 < φ) (hC : 0 ≤ C)
    (hb : ∀ q ∈ moduli R, ∀ a ∈ frequencies 10 B, ∀ θ ∈ shell φ,
      ‖scaledIntegral (map (Int.castRingHom ℝ) G) D.weight.weight P θ
        ((Nat.lcm q W : ℝ)⁻¹ • (fun i => (a i : ℝ)))‖ ≤
      C*(P^(-(N : ℝ)) + (volume (GradientWindowScaling.window
        (map (Int.castRingHom ℝ) G) D.box P ((Nat.lcm q W : ℝ)*θ)
        (fun i => (a i : ℝ)) δ)).toReal)) :
    LocalizedDyadicFrequencyError.truncatedError G W Ω D.weight.weight P R φ B ≤
      C*(4*φ*P^(-(N : ℝ)) *
        (∑ q ∈ moduli R, ((Nat.lcm q W : ℝ)^10)⁻¹ * ∑ a ∈ frequencies 10 B,
          ‖localizedCompleteCubicSum G q W Ω a‖) +
        localizedError G W Ω (map (Int.castRingHom ℝ) G) D P R φ B δ) := by
  let J (a : Fin 10 → ℤ) : ℝ := ∫ τ in annulus φ (4*(W:ℝ)*φ),
    (volume (GradientWindowScaling.window (map (Int.castRingHom ℝ) G)
      D.box P (R*τ) (fun i => (a i : ℝ)) δ)).toReal
  have hterm (q : ℕ) (hq : q ∈ moduli R) (a : Fin 10 → ℤ)
      (ha : a ∈ frequencies 10 B) :
      ((Nat.lcm q W : ℝ)^10)⁻¹*(‖localizedCompleteCubicSum G q W Ω a‖*frequencyMass G D.weight.weight P φ (Nat.lcm q W) a) ≤
      C*((4*φ*P^(-(N : ℝ)))*((Nat.lcm q W : ℝ)^10)⁻¹*‖localizedCompleteCubicSum G q W Ω a‖ +
        (R^10)⁻¹*(‖localizedCompleteCubicSum G q W Ω a‖*J a)) := by
    have hm := DyadicFiniteLocalization.frequencyMass_le_localized G hG D P φ C δ N hP hφ.le hC (Nat.lcm q W) a (hb q hq a ha)
    have hs := weighted_window_integral_le G hG D W hW Ω P R φ δ hP
      (zero_lt_one.trans_le hR) hφ.le q hq a
    let I : ℝ := ∫ θ in shell φ,
      (volume (GradientWindowScaling.window (map (Int.castRingHom ℝ) G)
        D.box P ((Nat.lcm q W : ℝ)*θ) (fun i => (a i : ℝ)) δ)).toReal
    change frequencyMass G D.weight.weight P φ (Nat.lcm q W) a ≤ C*(4*φ*P^(-(N : ℝ))+I) at hm
    change ((Nat.lcm q W : ℝ)^10)⁻¹*I ≤ (R^10)⁻¹*J a at hs
    calc
      _ ≤ ((Nat.lcm q W : ℝ)^10)⁻¹*(‖localizedCompleteCubicSum G q W Ω a‖*(C*(4*φ*P^(-(N : ℝ))+I))) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hm (norm_nonneg _)) (by positivity)
      _ = C*((4*φ*P^(-(N : ℝ)))*((Nat.lcm q W : ℝ)^10)⁻¹*‖localizedCompleteCubicSum G q W Ω a‖ +
          ‖localizedCompleteCubicSum G q W Ω a‖*(((Nat.lcm q W : ℝ)^10)⁻¹*I)) := by ring
      _ ≤ C*((4*φ*P^(-(N : ℝ)))*((Nat.lcm q W : ℝ)^10)⁻¹*‖localizedCompleteCubicSum G q W Ω a‖ +
          ‖localizedCompleteCubicSum G q W Ω a‖*((R^10)⁻¹*J a)) :=
        mul_le_mul_of_nonneg_left (add_le_add le_rfl
          (mul_le_mul_of_nonneg_left hs (norm_nonneg _))) hC
      _ = _ := by ring
  rw [localizedError_eq_sum G hG D W hW Ω P R φ B δ hP hφ.le]
  change _ ≤ C*(4*φ*P^(-(N : ℝ)) *
    (∑ q ∈ moduli R, ((Nat.lcm q W : ℝ)^10)⁻¹ * ∑ a ∈ frequencies 10 B,
      ‖localizedCompleteCubicSum G q W Ω a‖) +
    ∑ q ∈ moduli R, (R^10)⁻¹ * ∑ a ∈ frequencies 10 B,
      ‖localizedCompleteCubicSum G q W Ω a‖*J a)
  calc
    _ = ∑ q ∈ moduli R, ∑ a ∈ frequencies 10 B,
        ((Nat.lcm q W : ℝ)^10)⁻¹*(‖localizedCompleteCubicSum G q W Ω a‖*frequencyMass G D.weight.weight P φ (Nat.lcm q W) a) := by
      simp only [LocalizedDyadicFrequencyError.truncatedError,Finset.mul_sum]
    _ ≤ ∑ q ∈ moduli R, ∑ a ∈ frequencies 10 B,
        C*((4*φ*P^(-(N : ℝ)))*((Nat.lcm q W : ℝ)^10)⁻¹*‖localizedCompleteCubicSum G q W Ω a‖ +
          (R^10)⁻¹*(‖localizedCompleteCubicSum G q W Ω a‖*J a)) :=
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
    (D : Data (map (Int.castRingHom ℝ) G))
    (W : ℕ) (hW : 0 < W) (Ω : Set (Fin 10 → ZMod W)) (η : ℝ) (hη : 0 < η) (N : ℕ) :
    ∃ C P₀ : ℝ, 1 ≤ C ∧ 1 ≤ P₀ ∧ ∀ P : ℝ, P₀ ≤ P →
      ∀ R φ B : ℝ, 1 ≤ R → 0 < φ →
      LocalizedDyadicFrequencyError.truncatedError G W Ω D.weight.weight P R φ B ≤
        C*(4*φ*P^(-(N : ℝ)) *
          (∑ q ∈ moduli R, ((Nat.lcm q W : ℝ)^10)⁻¹ * ∑ a ∈ frequencies 10 B,
            ‖localizedCompleteCubicSum G q W Ω a‖) +
          localizedError G W Ω (map (Int.castRingHom ℝ) G) D P R φ B
            (P^η*GradientVolumeNumerics.Vzero P R φ)) := by
  obtain ⟨C,P₀,hC,hP₀,hb⟩ :=
    LocalizedOscillatoryControl.exists_localization_bound D (hG.map _)
      (W:ℝ) (by exact_mod_cast hW) η hη N
  refine ⟨C,P₀,hC,hP₀,?_⟩
  intro P hP R φ B hR hφ
  apply truncatedError_le_localized G hG D W hW Ω P R φ B _ C N
    (zero_lt_one.trans_le (hP₀.trans hP)) hR hφ (zero_le_one.trans hC)
  intro q hq a _ θ hθ
  obtain ⟨hqR,hq2R⟩ := (mem_moduli R q).mp hq
  have hq0 : 0 < q := by exact_mod_cast (zero_lt_one.trans_le hR).trans hqR
  have hℓ0 : (0:ℝ) < Nat.lcm q W := by exact_mod_cast Nat.lcm_pos hq0 hW
  have hℓR : (Nat.lcm q W : ℝ) ≤ 2*((W:ℝ)*R) := by
    calc
      _ ≤ (W:ℝ)*(q:ℝ) := by
        exact_mod_cast (LocalizedFrequencyComparison.denominator_bounds q W hq0 hW).2
      _ ≤ (W:ℝ)*(2*R) := mul_le_mul_of_nonneg_left hq2R (Nat.cast_nonneg W)
      _ = _ := by ring
  exact hb P hP R φ (Nat.lcm q W : ℝ) θ hR hφ hℓ0 hℓR hθ.2 _

end CubicTenVariables.LocalizedFiniteLocalization
