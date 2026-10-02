import CubicTenVariables.LocalizedFrequencyTruncation

/-! The actual q=1 nonzero-frequency error. Its oscillatory denominator is
W=lcm(1,W), and the reference radius in the analytic cutoff is exactly one.
No dyadic modulus set is modified and no arithmetic average is assumed. -/
set_option autoImplicit false
set_option maxHeartbeats 1500000
noncomputable section
namespace CubicTenVariables.SingletonFrequencyTruncation
open MvPolynomial MeasureTheory RealRegularGradientChart DyadicFrequencyError
open LocalSupremumNumerics LocalSupremumWindow
open scoped BigOperators

def error (G : MvPolynomial (Fin 10) ℤ) (W : ℕ)
    (Ω : Set (Fin 10 → ZMod W)) (w : (Fin 10 → ℝ) → ℝ) (P φ : ℝ) : ℝ :=
  ((W:ℝ)^10)⁻¹ * ∑' v : Fin 10 → ℤ,
    LocalizedDyadicFrequencyError.term G W Ω w P φ 1 v

def truncatedError (G : MvPolynomial (Fin 10) ℤ) (W : ℕ)
    (Ω : Set (Fin 10 → ZMod W)) (w : (Fin 10 → ℝ) → ℝ) (P φ B : ℝ) : ℝ :=
  ((W:ℝ)^10)⁻¹ * ∑ v ∈ frequencies 10 B,
    ‖localizedCompleteCubicSum G 1 W Ω v‖ * frequencyMass G w P φ W v

/-- The trivial q=1 coefficient bound has no arithmetic hypothesis. -/
theorem coefficient_le (G : MvPolynomial (Fin 10) ℤ) (W : ℕ) (hW : 0 < W)
    (Ω : Set (Fin 10 → ZMod W)) (v : Fin 10 → ℤ) :
    ‖localizedCompleteCubicSum G 1 W Ω v‖ ≤ (W:ℝ)^10 := by
  simpa only [Nat.lcm_one_left,Nat.cast_one,one_mul] using
    LocalizedFrequencyComparison.trivial_bound G 1 W zero_lt_one hW Ω v

theorem exists_frequencyMass_bound 
    (G : MvPolynomial (Fin 10) ℤ) (hG : G.IsHomogeneous 3)
    (D : Data (map (Int.castRingHom ℝ) G)) (W : ℕ) (hW : 0 < W)
    (η : ℝ) (hη : 0 < η) (A N : ℕ) :
    ∃ C P₀ : ℝ, 1 ≤ C ∧ 1 ≤ P₀ ∧ ∀ P : ℝ, P₀ ≤ P →
      ∀ φ : ℝ, 0 < φ → (W:ℝ) ≤ P^2 →
      ∀ v : Fin 10 → ℤ, v ≠ 0 → v ∉ frequencies 10 (P^η*V P 1 φ) →
      frequencyMass G D.weight.weight P φ W v ≤
        (4*φ*C)*P^(-(A:ℝ))*‖(fun i => (v i:ℝ))‖^(-(N:ℝ)) := by
  have hW1 : (1:ℝ) ≤ W := by exact_mod_cast hW
  obtain ⟨C,P₀,hC,hP₀,hb⟩ := LocalizedOscillatoryControl.exists_rapid_bound
    D (hG.map _) W hW1 η hη A N
  refine ⟨C,P₀,hC,hP₀,?_⟩
  intro P hP φ hφ hWP v hv hnot
  have hPpos : 0 < P := zero_lt_one.trans_le (hP₀.trans hP)
  have hWpos : (0:ℝ) < W := by exact_mod_cast hW
  have hcut : P^η*V P 1 φ ≤ ‖(fun i => (v i:ℝ))‖ := by
    by_contra! h
    apply hnot
    apply (mem_frequencies _ v).mpr
    refine ⟨hv,?_⟩
    intro i
    have hi : |(v i:ℝ)| ≤ ‖(fun i => (v i:ℝ))‖ := by
      simpa only [Real.norm_eq_abs] using norm_le_pi_norm (fun i => (v i:ℝ)) i
    exact hi.trans h.le
  have hm := frequencyMass_le G D.weight.weight D.weight.smooth.continuous
    D.weight.compact P φ hPpos.ne' hφ.le W v
    (C*P^(-(A:ℝ))*‖(fun i => (v i:ℝ))‖^(-(N:ℝ))) (by positivity)
    (fun θ hθ => hb P hP 1 φ W θ le_rfl hφ hWpos (by nlinarith)
      hWP hθ.2 _ hcut)
  convert hm using 1
  ring

/-- Genuine summability and arbitrary-power truncation for the singleton.
The factor W^10 cancels its exact covolume normalization. -/
theorem exists_bound 
    (G : MvPolynomial (Fin 10) ℤ) (hG : G.IsHomogeneous 3)
    (D : Data (map (Int.castRingHom ℝ) G)) (W : ℕ) (hW : 0 < W)
    (Ω : Set (Fin 10 → ZMod W)) (η : ℝ) (hη : 0 < η) (A : ℕ) :
    ∃ C P₀ : ℝ, 1 ≤ C ∧ 1 ≤ P₀ ∧ ∀ P : ℝ, P₀ ≤ P →
      ∀ φ : ℝ, 0 < φ → φ ≤ 1 → (W:ℝ) ≤ P^2 →
      Summable (LocalizedDyadicFrequencyError.term G W Ω D.weight.weight P φ 1) ∧
      error G W Ω D.weight.weight P φ ≤
        truncatedError G W Ω D.weight.weight P φ (P^η*V P 1 φ) + C*P^(-(A:ℝ)) := by
  obtain ⟨C,P₀,hC,hP₀,hmass⟩ := exists_frequencyMass_bound G hG D W hW η hη A 11
  obtain ⟨K,hK,htail⟩ := ArithmeticFrequencyTail.exists_bound 10 11 (by decide)
  refine ⟨4*K*C,P₀,by nlinarith,hP₀,?_⟩
  intro P hP φ hφ hφ1 hWP
  have hPpos : 0 < P := zero_lt_one.trans_le (hP₀.trans hP)
  have hWpos : (0:ℝ) < W := by exact_mod_cast hW
  let T := frequencies 10 (P^η*V P 1 φ)
  have hh := htail (fun v => ‖localizedCompleteCubicSum G 1 W Ω v‖)
    ((W:ℝ)^10) (fun _ => norm_nonneg _) (coefficient_le G W hW Ω)
    T (frequencyMass G D.weight.weight P φ W) (4*φ*C) P A
    (by positivity) hPpos (frequencyMass_nonneg G D.weight.weight P φ W)
    (hmass P hP φ hφ hWP)
  have he : LocalizedDyadicFrequencyError.term G W Ω D.weight.weight P φ 1 =
      ArithmeticFrequencyTail.term (fun v => ‖localizedCompleteCubicSum G 1 W Ω v‖)
        (frequencyMass G D.weight.weight P φ W) := by
    funext v
    simp only [LocalizedDyadicFrequencyError.term,ArithmeticFrequencyTail.term,Nat.lcm_one_left]
  refine ⟨he ▸ hh.1,?_⟩
  have hfinite : (∑ v ∈ T, ArithmeticFrequencyTail.term
      (fun v => ‖localizedCompleteCubicSum G 1 W Ω v‖)
      (frequencyMass G D.weight.weight P φ W) v) =
      ∑ v ∈ T, ‖localizedCompleteCubicSum G 1 W Ω v‖*
        frequencyMass G D.weight.weight P φ W v := by
    apply Finset.sum_congr rfl
    intro v hv
    exact if_neg ((mem_frequencies _ v).mp hv).1
  unfold error truncatedError
  rw [he,hh.2.2.1,hfinite,mul_add]
  apply add_le_add le_rfl
  calc
    _ ≤ ((W:ℝ)^10)⁻¹*(K*(W:ℝ)^10*(4*φ*C)*P^(-(A:ℝ))) :=
      mul_le_mul_of_nonneg_left hh.2.2.2 (by positivity)
    _ = (4*K*C)*φ*P^(-(A:ℝ)) := by field_simp
    _ ≤ (4*K*C)*1*P^(-(A:ℝ)) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hφ1 (by positivity)) (by positivity)
    _ = _ := by ring

end CubicTenVariables.SingletonFrequencyTruncation
