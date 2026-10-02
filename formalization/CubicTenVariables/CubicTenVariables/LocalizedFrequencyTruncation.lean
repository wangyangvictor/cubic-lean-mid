import CubicTenVariables.LocalizedDyadicFrequencyError
import CubicTenVariables.LocalizedOscillatoryControl
import CubicTenVariables.ArithmeticFrequencyTail
import CubicTenVariables.DyadicFrequencyTruncation

/-! Summability and rapid finite-frequency truncation for the literal
localized dyadic error. The lcm(q,W) denominator is retained throughout;
cubic oscillatory localization is proved internally. -/
set_option autoImplicit false
set_option maxHeartbeats 1500000
noncomputable section
namespace CubicTenVariables.LocalizedFrequencyTruncation
open MvPolynomial MeasureTheory RealRegularGradientChart DyadicFrequencyError
open LocalSupremumNumerics LocalSupremumWindow
open scoped BigOperators

/-- Rapid decay of the shell-integrated mass with the true localized
frequency denominator and the common original dyadic cutoff. -/
theorem exists_frequencyMass_bound 
    (G : MvPolynomial (Fin 10) ℤ) (hG : G.IsHomogeneous 3)
    (D : Data (map (Int.castRingHom ℝ) G)) (W : ℕ) (hW : 0 < W)
    (η : ℝ) (hη : 0 < η) (A N : ℕ) :
    ∃ C P₀ : ℝ, 1 ≤ C ∧ 1 ≤ P₀ ∧ ∀ P : ℝ, P₀ ≤ P →
      ∀ R φ : ℝ, 1 ≤ R → 0 < φ → ∀ q : ℕ,
      q ∈ moduli R → (Nat.lcm q W : ℝ) ≤ P^2 →
      ∀ v : Fin 10 → ℤ, v ≠ 0 → v ∉ frequencies 10 (P^η*V P R φ) →
      frequencyMass G D.weight.weight P φ (Nat.lcm q W) v ≤
        (4*φ*C)*P^(-(A : ℝ))*‖(fun i => (v i : ℝ))‖^(-(N : ℝ)) := by
  have hW1 : (1:ℝ) ≤ W := by exact_mod_cast hW
  obtain ⟨C,P₀,hC,hP₀,hb⟩ := LocalizedOscillatoryControl.exists_rapid_bound
    D (hG.map _) W hW1 η hη A N
  refine ⟨C,P₀,hC,hP₀,?_⟩
  intro P hP R φ hR hφ q hq hlcmP v hv hnot
  obtain ⟨hqR,hq2R⟩ := (mem_moduli R q).mp hq
  have hPpos : 0 < P := zero_lt_one.trans_le (hP₀.trans hP)
  have hqpos : (0:ℝ) < q := (zero_lt_one.trans_le hR).trans hqR
  have hqnat : 0 < q := by exact_mod_cast hqpos
  have hlcmpos : (0:ℝ) < Nat.lcm q W := by exact_mod_cast Nat.lcm_pos hqnat hW
  have hlcmR : (Nat.lcm q W : ℝ) ≤ 2*((W:ℝ)*R) := by
    calc
      _ ≤ (W:ℝ)*(q:ℝ) := by exact_mod_cast (LocalizedFrequencyComparison.denominator_bounds q W hqnat hW).2
      _ ≤ (W:ℝ)*(2*R) := mul_le_mul_of_nonneg_left hq2R (Nat.cast_nonneg _)
      _ = _ := by ring
  have hcut : P^η*V P R φ ≤ ‖(fun i => (v i : ℝ))‖ := by
    by_contra! h
    apply hnot
    apply (mem_frequencies _ v).mpr
    refine ⟨hv,?_⟩
    intro i
    have hi : |(v i : ℝ)| ≤ ‖(fun i => (v i : ℝ))‖ := by
      simpa only [Real.norm_eq_abs] using norm_le_pi_norm (fun i => (v i : ℝ)) i
    exact hi.trans h.le
  have hmass := frequencyMass_le G D.weight.weight D.weight.smooth.continuous
    D.weight.compact P φ hPpos.ne' hφ.le (Nat.lcm q W) v
    (C*P^(-(A : ℝ))*‖(fun i => (v i : ℝ))‖^(-(N : ℝ))) (by positivity)
    (fun θ hθ => hb P hP R φ (Nat.lcm q W) θ hR hφ hlcmpos hlcmR hlcmP hθ.2 _ hcut)
  convert hmass using 1
  ring

/-- The exact coefficient estimate q*λ^10 cancels the literal λ^-10
normalization. Thus no extra W-power is lost in the summed tail. -/
theorem exists_weighted_bound 
    (G : MvPolynomial (Fin 10) ℤ) (hG : G.IsHomogeneous 3)
    (D : Data (map (Int.castRingHom ℝ) G)) (W : ℕ) (hW : 0 < W)
    (Ω : Set (Fin 10 → ZMod W)) (η : ℝ) (hη : 0 < η) (A : ℕ) :
    ∃ C P₀ : ℝ, 1 ≤ C ∧ 1 ≤ P₀ ∧ ∀ P : ℝ, P₀ ≤ P →
      ∀ R φ : ℝ, 1 ≤ R → 0 < φ → 2*(W:ℝ)*R ≤ P^2 →
      (∀ q ∈ moduli R, Summable
        (LocalizedDyadicFrequencyError.term G W Ω D.weight.weight P φ q)) ∧
      LocalizedFrequencyComparison.error G W Ω D.weight.weight P R φ ≤
        LocalizedDyadicFrequencyError.truncatedError G W Ω D.weight.weight P R φ
          (P^η*V P R φ) + C*φ*P^(-(A : ℝ))*(∑ q ∈ moduli R, (q : ℝ)) := by
  classical
  obtain ⟨C,P₀,hC,hP₀,hmass⟩ := exists_frequencyMass_bound G hG D W hW η hη A 11
  obtain ⟨K,hK,htail⟩ := ArithmeticFrequencyTail.exists_bound 10 11 (by decide)
  refine ⟨4*K*C,P₀,by nlinarith,hP₀,?_⟩
  intro P hP R φ hR hφ hRP
  have hPpos : 0 < P := zero_lt_one.trans_le (hP₀.trans hP)
  let T := frequencies 10 (P^η*V P R φ)
  have hb (q : ℕ) (hq : q ∈ moduli R) := by
    have hqpos : (0:ℝ) < q := (zero_lt_one.trans_le hR).trans ((mem_moduli R q).mp hq).1
    have hqnat : 0 < q := by exact_mod_cast hqpos
    have hlcmP : (Nat.lcm q W : ℝ) ≤ P^2 := by
      calc
        _ ≤ (W:ℝ)*(q:ℝ) := by exact_mod_cast (LocalizedFrequencyComparison.denominator_bounds q W hqnat hW).2
        _ ≤ (W:ℝ)*(2*R) := mul_le_mul_of_nonneg_left ((mem_moduli R q).mp hq).2 (Nat.cast_nonneg _)
        _ = 2*(W:ℝ)*R := by ring
        _ ≤ _ := hRP
    exact htail (fun v => ‖localizedCompleteCubicSum G q W Ω v‖)
      ((q:ℝ)*(Nat.lcm q W:ℝ)^10) (fun _ => norm_nonneg _)
      (LocalizedFrequencyComparison.trivial_bound G q W hqnat hW Ω)
      T (frequencyMass G D.weight.weight P φ (Nat.lcm q W)) (4*φ*C) P A
      (by positivity) hPpos (frequencyMass_nonneg G D.weight.weight P φ (Nat.lcm q W))
      (hmass P hP R φ hR hφ q hq hlcmP)
  refine ⟨fun q hq => (hb q hq).1,?_⟩
  have hqbound (q : ℕ) (hq : q ∈ moduli R) :
      ((Nat.lcm q W:ℝ)^10)⁻¹*(∑' v, LocalizedDyadicFrequencyError.term G W Ω D.weight.weight P φ q v) ≤
        ((Nat.lcm q W:ℝ)^10)⁻¹*(∑ v ∈ T,
          ‖localizedCompleteCubicSum G q W Ω v‖*frequencyMass G D.weight.weight P φ (Nat.lcm q W) v) +
          (4*K*C)*φ*P^(-(A : ℝ))*(q : ℝ) := by
    have hh := hb q hq
    have hqpos : (0:ℝ) < q := (zero_lt_one.trans_le hR).trans ((mem_moduli R q).mp hq).1
    have hqnat : 0 < q := by exact_mod_cast hqpos
    have hlcmpos : (0:ℝ) < Nat.lcm q W := by exact_mod_cast Nat.lcm_pos hqnat hW
    have hfinite : (∑ v ∈ T, ArithmeticFrequencyTail.term
        (fun v => ‖localizedCompleteCubicSum G q W Ω v‖)
        (frequencyMass G D.weight.weight P φ (Nat.lcm q W)) v) =
        ∑ v ∈ T, ‖localizedCompleteCubicSum G q W Ω v‖*
          frequencyMass G D.weight.weight P φ (Nat.lcm q W) v := by
      apply Finset.sum_congr rfl
      intro v hv
      exact if_neg ((mem_frequencies _ v).mp hv).1
    change ((Nat.lcm q W:ℝ)^10)⁻¹*(∑' v, ArithmeticFrequencyTail.term
      (fun v => ‖localizedCompleteCubicSum G q W Ω v‖)
      (frequencyMass G D.weight.weight P φ (Nat.lcm q W)) v) ≤ _
    rw [hh.2.2.1,hfinite,mul_add]
    apply add_le_add le_rfl
    calc
      _ ≤ ((Nat.lcm q W:ℝ)^10)⁻¹*(K*((q:ℝ)*(Nat.lcm q W:ℝ)^10)*(4*φ*C)*P^(-(A : ℝ))) :=
        mul_le_mul_of_nonneg_left hh.2.2.2 (by positivity)
      _ = _ := by field_simp
  calc
    LocalizedFrequencyComparison.error G W Ω D.weight.weight P R φ ≤ ∑ q ∈ moduli R,
        (((Nat.lcm q W:ℝ)^10)⁻¹*(∑ v ∈ T,
          ‖localizedCompleteCubicSum G q W Ω v‖*frequencyMass G D.weight.weight P φ (Nat.lcm q W) v) +
          (4*K*C)*φ*P^(-(A : ℝ))*(q : ℝ)) := Finset.sum_le_sum hqbound
    _ = _ := by simp only [Finset.sum_add_distrib,← Finset.mul_sum,
      LocalizedDyadicFrequencyError.truncatedError,T]

/-- Arbitrarily rapid truncation with the actual localized denominator,
including summability of every full nonzero-frequency series. -/
theorem exists_bound 
    (G : MvPolynomial (Fin 10) ℤ) (hG : G.IsHomogeneous 3)
    (D : Data (map (Int.castRingHom ℝ) G)) (W : ℕ) (hW : 0 < W)
    (Ω : Set (Fin 10 → ZMod W)) (η : ℝ) (hη : 0 < η) (A : ℕ) :
    ∃ C P₀ : ℝ, 1 ≤ C ∧ 1 ≤ P₀ ∧ ∀ P : ℝ, P₀ ≤ P →
      ∀ R φ : ℝ, 1 ≤ R → 0 < φ → φ ≤ 1 → 2*(W:ℝ)*R ≤ P^2 →
      (∀ q ∈ moduli R, Summable
        (LocalizedDyadicFrequencyError.term G W Ω D.weight.weight P φ q)) ∧
      LocalizedFrequencyComparison.error G W Ω D.weight.weight P R φ ≤
        LocalizedDyadicFrequencyError.truncatedError G W Ω D.weight.weight P R φ
          (P^η*V P R φ) + C*P^(-(A : ℝ)) := by
  obtain ⟨C,P₀,hC,hP₀,hb⟩ := exists_weighted_bound G hG D W hW Ω η hη (A+4)
  refine ⟨2*C,P₀,by linarith,hP₀,?_⟩
  intro P hP R φ hR hφ hφ1 hRP
  obtain ⟨hs,hbound⟩ := hb P hP R φ hR hφ hRP
  refine ⟨hs,hbound.trans ?_⟩
  apply add_le_add le_rfl
  have hP1 : 1 ≤ P := hP₀.trans hP
  have hPpos : 0 < P := zero_lt_one.trans_le hP1
  have hW1 : (1:ℝ) ≤ W := by exact_mod_cast hW
  have hRP' : 2*R ≤ P^2 := by
    have hh := mul_le_mul_of_nonneg_right hW1 (by positivity : 0 ≤ 2*R)
    nlinarith
  have hsum : (∑ q ∈ moduli R, (q : ℝ)) ≤ 2*P^4 := by
    apply (DyadicFrequencyTruncation.sum_moduli_le R (P^2) (sq_nonneg P) hRP').trans
    nlinarith [sq_nonneg (P^2-1)]
  have hcancel : P^(-((A+4 : ℕ) : ℝ))*P^4=P^(-(A : ℝ)) := by
    rw [← Real.rpow_natCast P 4,← Real.rpow_add hPpos]
    congr 1
    push_cast
    ring
  calc
    C*φ*P^(-((A+4 : ℕ) : ℝ))*(∑ q ∈ moduli R, (q : ℝ)) ≤
        C*1*P^(-((A+4 : ℕ) : ℝ))*(2*P^4) := by gcongr
    _ = (2*C)*(P^(-((A+4 : ℕ) : ℝ))*P^4) := by ring
    _ = _ := by rw [hcancel]

end CubicTenVariables.LocalizedFrequencyTruncation
