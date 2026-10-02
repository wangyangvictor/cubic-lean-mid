import CubicTenVariables.SingletonFrequencyTruncation
import CubicTenVariables.DyadicAveragedVolumeBound
import CubicTenVariables.FiniteFrequencyRemainder

/-! The singleton's finite localization bound uses only its trivial
coefficient estimate and the proved geometric local-maximum estimate.
The actual phase is Wθ throughout; |Wθ|≥φ on the shell suffices directly. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
namespace CubicTenVariables.SingletonWindowBound
open MvPolynomial MeasureTheory RealRegularGradientChart DyadicFrequencyError
open LocalSupremumNumerics GradientVolumeNumerics LocalSupremumWindow
open OscillatoryLocalization AveragedGradientVolume DyadicAveragedVolumeBound
open SingletonFrequencyTruncation
open scoped BigOperators

/-- Every shifted q=1 coefficient sum has its elementary cardinality bound. -/
theorem shifted_sum_le (G : MvPolynomial (Fin 10) ℤ) (W : ℕ) (hW : 0 < W)
    (Ω : Set (Fin 10 → ZMod W)) (L : ℕ) (v : Fin 10 → ℤ) :
    (∑ a ∈ ShiftedCompleteSumWindow.shiftedWindow L v,
      ‖localizedCompleteCubicSum G 1 W Ω a‖) ≤ (W:ℝ)^10*((2*L+1:ℕ):ℝ)^10 := by
  calc
    _ ≤ ∑ _a ∈ ShiftedCompleteSumWindow.shiftedWindow L v, (W:ℝ)^10 :=
      Finset.sum_le_sum (fun a _ => coefficient_le G W hW Ω a)
    _ ≤ ∑ _a ∈ shiftedBox v L, (W:ℝ)^10 :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun _ _ _ => by positivity)
    _ = _ := by simp [Nat.cast_pow,mul_comm]

/-- A window contains its own center, so the local-maximum lattice sum
dominates the original nonnegative finite sum. -/
theorem sum_le_sum_maximum {n : ℕ} (S : Finset (Fin n → ℤ))
    (g : (Fin n → ℤ) → ℝ) (hg : ∀ a ∈ S, 0 ≤ g a) (L : ℕ) :
    (∑ a ∈ S, g a) ≤ ∑' v : Fin n → ℤ, maximum S g v (L:ℝ) := by
  have hself (a : Fin n → ℤ) (ha : a ∈ S) : a ∈ window S a (L:ℝ) :=
    (mem_window S a a (L:ℝ)).mpr ⟨ha,by intro i; simp⟩
  have he : (∑' v : Fin n → ℤ, maximum S g v (L:ℝ)) =
      ∑ v ∈ centers S L, maximum S g v (L:ℝ) :=
    tsum_eq_sum (fun v hv => maximum_zero_of_not_mem_centers S g L v hv)
  rw [he]
  calc
    _ ≤ ∑ a ∈ S, maximum S g a (L:ℝ) :=
      Finset.sum_le_sum (fun a ha => le_maximum S g a a (L:ℝ) (hself a ha))
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg
      (fun a ha => (mem_centers S L a).mpr ⟨a,hself a ha⟩)
      (fun a _ _ => maximum_nonneg S g hg a (L:ℝ))

theorem truncated_le_unweighted (G : MvPolynomial (Fin 10) ℤ)
    (W : ℕ) (hW : 0 < W) (Ω : Set (Fin 10 → ZMod W))
    (w : (Fin 10 → ℝ) → ℝ) (P φ B : ℝ) :
    SingletonFrequencyTruncation.truncatedError G W Ω w P φ B ≤
      ∑ v ∈ frequencies 10 B, frequencyMass G w P φ W v := by
  have hWpos : (0:ℝ) < W := by exact_mod_cast hW
  calc
    _ ≤ ((W:ℝ)^10)⁻¹ * ∑ v ∈ frequencies 10 B,
        (W:ℝ)^10 * frequencyMass G w P φ W v := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact Finset.sum_le_sum (fun v _ =>
        mul_le_mul_of_nonneg_right (coefficient_le G W hW Ω v)
          (frequencyMass_nonneg G w P φ W v))
    _ = _ := by rw [← Finset.mul_sum]; field_simp

/-- Uniform finite-frequency localization, with no remaining window sum or
phase integral, for the actual q=1 localized coefficient. -/
theorem exists_truncated_bound 
    (G : MvPolynomial (Fin 10) ℤ) (hG : G.IsHomogeneous 3)
    (D : Data (map (Int.castRingHom ℝ) G)) (W : ℕ) (hW : 0 < W)
    (Ω : Set (Fin 10 → ZMod W)) (ε : ℝ) (hε : 0 < ε) (N : ℕ) :
    ∃ C P₀ : ℝ, 1 ≤ C ∧ 1 ≤ P₀ ∧ ∀ P : ℝ, P₀ ≤ P →
      ∀ φ : ℝ, 0 < φ →
      SingletonFrequencyTruncation.truncatedError G W Ω D.weight.weight P φ
        (P^(ε/17)*V P 1 φ) ≤
      C*φ*(P^(-(N:ℝ))*((frequencies 10 (P^(ε/17)*V P 1 φ)).card:ℝ) +
        volumeFactor ε P 1 φ 1) := by
  have hW1 : (1:ℝ) ≤ W := by exact_mod_cast hW
  have hWpos : (0:ℝ) < W := by exact_mod_cast hW
  obtain ⟨Cl,P₀,hCl,hP₀,hl⟩ := LocalizedOscillatoryControl.exists_localization_bound
    D (hG.map _) W hW1 (ε/17) (by positivity) N
  obtain ⟨Cv,hCv,hv⟩ := LocalSupremumVolumeEstimate.exists_bound
    (map (Int.castRingHom ℝ) G) (hG.map _) D 1 zero_lt_one
  refine ⟨4*Cl*Cv,P₀,by nlinarith,hP₀,?_⟩
  intro P hP φ hφ
  have hP1 : 1 ≤ P := hP₀.trans hP
  have hPpos : 0 < P := zero_lt_one.trans_le hP1
  let S := frequencies 10 (P^(ε/17)*V P 1 φ)
  let I (θ : ℝ) (v : Fin 10 → ℤ) :=
    ‖scaledIntegral (map (Int.castRingHom ℝ) G) D.weight.weight P θ
      ((W:ℝ)⁻¹ • (fun i => (v i:ℝ)))‖
  let M := Cl*(P^(-(N:ℝ))*(S.card:ℝ)+Cv*volumeFactor ε P 1 φ 1)
  have hvol : 0 ≤ volumeFactor ε P 1 φ 1 :=
    volumeFactor_nonneg ε P 1 φ 1 hPpos zero_lt_one zero_le_one
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hi (v : Fin 10 → ℤ) : IntegrableOn (fun θ => I θ v) (shell φ) :=
    frequency_integrable G D.weight.weight D.weight.smooth.continuous
      D.weight.compact P φ hPpos.ne' W v
  have hpoint (θ : ℝ) (hθ : θ ∈ shell φ) : (∑ v ∈ S, I θ v) ≤ M := by
    let g (a : Fin 10 → ℤ) := (volume (GradientWindowScaling.window
      (map (Int.castRingHom ℝ) G) D.box P ((W:ℝ)*θ)
      (fun i => (a i:ℝ)) (P^(ε/17)*Vzero P 1 φ))).toReal
    have hsum : (∑ a ∈ S, g a) ≤ volumeSum (map (Int.castRingHom ℝ) G)
        D.box P ((W:ℝ)*θ) (P^(ε/17)*V P 1 φ) (P^(ε/17)*Vzero P 1 φ) 1 := by
      simpa only [volumeSum,localMaximum,Nat.cast_one] using
        sum_le_sum_maximum S g (fun _ _ => ENNReal.toReal_nonneg) 1
    have hα : 1*(1*φ) ≤ |(W:ℝ)*θ| := by
      rw [one_mul,one_mul,abs_mul,abs_of_pos hWpos]
      exact hθ.1.le.trans (le_mul_of_one_le_left (abs_nonneg θ) hW1)
    have hgeom : volumeSum (map (Int.castRingHom ℝ) G) D.box P ((W:ℝ)*θ)
        (P^(ε/17)*V P 1 φ) (P^(ε/17)*Vzero P 1 φ) 1 ≤ Cv*volumeFactor ε P 1 φ 1 := by
      have hh := hv D.box (fun _ hx => hx) ε P 1 φ ((W:ℝ)*θ) 1
        hε hP1 le_rfl hφ zero_le_one hα
      convert hh using 1
      unfold volumeFactor
      split_ifs <;> ring
    calc
      _ ≤ ∑ a ∈ S, Cl*(P^(-(N:ℝ))+g a) := by
        apply Finset.sum_le_sum
        intro a _
        exact hl P hP 1 φ W θ le_rfl hφ hWpos (by nlinarith) hθ.2 _
      _ = Cl*(P^(-(N:ℝ))*(S.card:ℝ)+∑ a ∈ S, g a) := by
        simp only [mul_add,Finset.sum_add_distrib,Finset.sum_const,nsmul_eq_mul,
          ← Finset.mul_sum]
        ring
      _ ≤ M := mul_le_mul_of_nonneg_left
        (add_le_add le_rfl (hsum.trans hgeom)) (zero_le_one.trans hCl)
  have hmeasure : (volume (shell φ)).toReal ≤ 4*φ := by
    have hh := ENNReal.toReal_mono ENNReal.ofReal_ne_top (volume_shell_le φ)
    simpa only [ENNReal.toReal_ofReal (by positivity : 0 ≤ 4*φ)] using hh
  calc
    _ ≤ ∑ v ∈ S, frequencyMass G D.weight.weight P φ W v :=
      truncated_le_unweighted G W hW Ω D.weight.weight P φ _
    _ = ∫ θ in shell φ, ∑ v ∈ S, I θ v :=
      (integral_finset_sum S (fun v _ => hi v)).symm
    _ ≤ ∫ _θ in shell φ, M :=
      setIntegral_mono_on (integrable_finset_sum S (fun v _ => hi v))
        (integrableOn_const (volume_shell_ne_top φ)) (measurableSet_shell φ) hpoint
    _ = (volume (shell φ)).toReal*M := by simp [MeasureTheory.measureReal_def]
    _ ≤ 4*φ*M := mul_le_mul_of_nonneg_right hmeasure hM
    _ ≤ _ := by
      dsimp [M,S]
      have hrem : 0 ≤ P^(-(N:ℝ))*((frequencies 10 (P^(ε/17)*V P 1 φ)).card:ℝ) := by positivity
      nlinarith [mul_nonneg (show 0 ≤ 4*Cl*φ by positivity)
        (mul_nonneg (show 0 ≤ Cv-1 by linarith) hrem)]

end CubicTenVariables.SingletonWindowBound
