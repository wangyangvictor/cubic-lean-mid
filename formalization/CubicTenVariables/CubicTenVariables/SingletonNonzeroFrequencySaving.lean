import CubicTenVariables.SingletonWindowBound
import CubicTenVariables.NonzeroFrequencyPhaseNumerics
import CubicTenVariables.NonzeroFrequencyCoefficient

/-! The actual q=1 localized nonzero-frequency error has a power saving
without an arithmetic shifted-average hypothesis. Cubic localization
and all singleton coefficient bounds are proved internally. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
namespace CubicTenVariables.SingletonNonzeroFrequencySaving
open MvPolynomial RealRegularGradientChart DyadicFrequencyError
open LocalSupremumNumerics GradientVolumeNumerics LocalSupremumWindow
open SingletonFrequencyTruncation DyadicAveragedVolumeBound NonzeroFrequencyNumerics
open scoped BigOperators

/-- Integral removal for the singleton, with arbitrary rapid remainder. -/
theorem exists_integral_free_bound 
    (G : MvPolynomial (Fin 10) ℤ) (hG : G.IsHomogeneous 3)
    (D : Data (map (Int.castRingHom ℝ) G)) (W : ℕ) (hW : 0 < W)
    (Ω : Set (Fin 10 → ZMod W)) (ε : ℝ) (hε : 0 < ε) (hε17 : ε ≤ 17) (A : ℕ) :
    ∃ C P₀ : ℝ, 1 ≤ C ∧ 1 ≤ P₀ ∧ ∀ P : ℝ, P₀ ≤ P →
      ∀ φ : ℝ, 0 < φ → φ ≤ 1 → (W:ℝ) ≤ P^2 →
      Summable (LocalizedDyadicFrequencyError.term G W Ω D.weight.weight P φ 1) ∧
      SingletonFrequencyTruncation.error G W Ω D.weight.weight P φ ≤
        C*(P^(-(A:ℝ))+φ*volumeFactor ε P 1 φ 1) := by
  obtain ⟨Ct,Pt,hCt,hPt,ht⟩ := SingletonFrequencyTruncation.exists_bound
    G hG D W hW Ω (ε/17) (by positivity) A
  obtain ⟨Cv,Pv,hCv,hPv,hv⟩ := SingletonWindowBound.exists_truncated_bound
    G hG D W hW Ω ε hε (A+50)
  let C := Ct+Cv*((7:ℝ)^10+1)
  refine ⟨C,max Pt Pv,by dsimp [C]; nlinarith,
    hPt.trans (le_max_left _ _),?_⟩
  intro P hP φ hφ hφ1 hWP
  have hPtP : Pt ≤ P := (le_max_left _ _).trans hP
  have hPvP : Pv ≤ P := (le_max_right _ _).trans hP
  have hP1 : 1 ≤ P := hPt.trans hPtP
  have hPpos : 0 < P := zero_lt_one.trans_le hP1
  have hB0 : 0 ≤ P^(ε/17)*V P 1 φ := by
    have hh := V_pos P 1 φ hPpos zero_lt_one
    positivity
  have hB : P^(ε/17)*V P 1 φ ≤ P^5 :=
    FiniteFrequencyRemainder.cutoff_le_fifth_power P 1 φ (ε/17) hP1
      zero_le_one (one_le_pow₀ hP1) hφ1 (by linarith)
  have hcard := FiniteFrequencyRemainder.frequency_card_le P _ 5 hP1 hB0 hB
  have hcancel : P^(-((A+50:ℕ):ℝ))*P^50=P^(-(A:ℝ)) := by
    rw [← Real.rpow_natCast P 50,← Real.rpow_add hPpos]
    congr 1
    push_cast
    ring
  have hrem : P^(-((A+50:ℕ):ℝ))*
      ((frequencies 10 (P^(ε/17)*V P 1 φ)).card:ℝ) ≤ (7:ℝ)^10*P^(-(A:ℝ)) := by
    calc
      _ ≤ P^(-((A+50:ℕ):ℝ))*((7:ℝ)^10*P^50) :=
        mul_le_mul_of_nonneg_left hcard (by positivity)
      _ = _ := by rw [mul_left_comm,hcancel]
  obtain ⟨hs,he⟩ := ht P hPtP φ hφ hφ1 hWP
  have hvb := hv P hPvP φ hφ
  have hvol := volumeFactor_nonneg ε P 1 φ 1 hPpos zero_lt_one zero_le_one
  have hdec : 0 ≤ P^(-(A:ℝ)) := by positivity
  refine ⟨hs,he.trans ?_⟩
  apply (add_le_add hvb le_rfl).trans
  calc
    _ ≤ Cv*φ*((7:ℝ)^10*P^(-(A:ℝ))+volumeFactor ε P 1 φ 1)+Ct*P^(-(A:ℝ)) :=
      add_le_add (mul_le_mul_of_nonneg_left (add_le_add hrem le_rfl) (by positivity)) le_rfl
    _ ≤ Cv*((7:ℝ)^10*P^(-(A:ℝ))+φ*volumeFactor ε P 1 φ 1)+Ct*P^(-(A:ℝ)) := by
      have hh := mul_le_mul_of_nonneg_left hφ1 (show 0 ≤ Cv*(7:ℝ)^10*P^(-(A:ℝ)) by positivity)
      nlinarith only [hh]
    _ ≤ _ := by
      dsimp [C]
      nlinarith [mul_nonneg (show 0 ≤ Ct+Cv*(7:ℝ)^10 by positivity)
        (mul_nonneg hφ.le hvol),mul_nonneg (zero_le_one.trans hCv) hdec]

/-- Numerical optimization at the genuine reference radius R=1, b=0.
The small fixed losses leave at least an eighth-power saving. -/
theorem volume_factor_bound (P φ η : ℝ) (hP : 1 ≤ P) (hφ : 0 < φ)
    (hη : 0 ≤ η) (hηmax : η ≤ 1/1000)
    (hφmax : φ ≤ (P^((3:ℝ)/2))^(-1+η)) :
    φ*volumeFactor (1/1000) P 1 φ 1 ≤ (2:ℝ)^31*P^(7-(1:ℝ)/8) := by
  have hPpos : 0 < P := zero_lt_one.trans_le hP
  have hvol := volumeFactor_nonneg (1/1000) P 1 φ 1 hPpos zero_lt_one zero_le_one
  by_cases hcut : P^((1/1000:ℝ)/17)*V P 1 φ < 1
  · simp only [volumeFactor,if_pos hcut,mul_zero]
    positivity
  · have hnum := NonzeroFrequencyPhaseNumerics.optimized_bound
      P 1 φ 0 (1/1000) η ((1/1000)/17) hP le_rfl hφ hη (by norm_num)
      (by norm_num) (Real.one_le_rpow hP (by norm_num))
      (by simpa only [one_mul] using hφmax) (le_of_not_gt hcut)
    have hwidth : cubeRootWidth 1=1 := by norm_num [cubeRootWidth]
    have hsave : saving (20/3-0)=1/4 := by norm_num [saving]
    have hlarge : φ*volumeFactor (1/1000) P 1 φ 1 ≤
        φ*1^(0-10:ℝ)*P^(10+(1/1000:ℝ))*
          (1+1^((1:ℝ)/3)/(cubeRootWidth 1:ℝ))^10*
            (if 1 < φ*P^3 then
              (1+(cubeRootWidth 1:ℝ)/V P 1 φ)^7*
              (1+Vzero P 1 φ+(cubeRootWidth 1:ℝ))^3*(Vzero P 1 φ)^7
             else (V P 1 φ+(cubeRootWidth 1:ℝ))^10) := by
      have hh : φ*volumeFactor (1/1000) P 1 φ 1 ≤
          (2:ℝ)^10*(φ*volumeFactor (1/1000) P 1 φ 1) := by
        exact le_mul_of_one_le_left (mul_nonneg hφ.le hvol) (by norm_num)
      convert hh using 1 <;>
        simp only [hwidth,Nat.cast_one,Real.one_rpow,div_one,one_mul,
          volumeFactor,if_neg hcut] <;> ring
    apply (hlarge.trans hnum).trans
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply Real.rpow_le_rpow_of_exponent_le hP
    rw [hsave]
    linarith

/-- Uniform actual q=1 saving, including absolute frequency summability.
All constants precede the physical scale, shell width, and phase loss.
The arithmetic shifted-average hypothesis is not needed for this singleton. -/
theorem exists_power_saving 
    (G : MvPolynomial (Fin 10) ℤ) (hG : G.IsHomogeneous 3)
    (D : Data (map (Int.castRingHom ℝ) G)) (W : ℕ) (hW : 0 < W)
    (Ω : Set (Fin 10 → ZMod W)) :
    ∃ δ η₀ C P₀ : ℝ, 0 < δ ∧ 0 < η₀ ∧ η₀ ≤ 1 ∧ 1 ≤ C ∧ 4 ≤ P₀ ∧
      ∀ P φ η : ℝ, P₀ ≤ P → 0 < φ → 0 ≤ η → η ≤ η₀ →
        φ ≤ (P^((3:ℝ)/2))^(-1+η) →
        Summable (LocalizedDyadicFrequencyError.term G W Ω D.weight.weight P φ 1) ∧
        SingletonFrequencyTruncation.error G W Ω D.weight.weight P φ ≤ C*P^(7-δ) := by
  obtain ⟨C,P₀,hC,hP₀,hb⟩ := exists_integral_free_bound
    G hG D W hW Ω (1/1000) (by norm_num) (by norm_num) 0
  refine ⟨1/8,1/1000,C*(1+(2:ℝ)^31),max P₀ (max 4 (W:ℝ)),
    by norm_num,by norm_num,by norm_num,
    one_le_mul_of_one_le_of_one_le hC (by norm_num),
    (le_max_left _ _).trans (le_max_right _ _),?_⟩
  intro P φ η hP hφ hη hηmax hφmax
  have hP4 : 4 ≤ P := ((le_max_left _ _).trans (le_max_right _ _)).trans hP
  have hP1 : 1 ≤ P := by linarith
  have hPpos : 0 < P := by linarith
  have hWP : (W:ℝ) ≤ P^2 := by
    have hh : (W:ℝ) ≤ P := ((le_max_right _ _).trans (le_max_right _ _)).trans hP
    nlinarith only [hh,hP1]
  have hφ1 := NonzeroFrequencyCoefficient.phase_le_one P 1 φ η hP1 le_rfl
    (by linarith : η ≤ 1) (by simpa only [one_mul] using hφmax)
  obtain ⟨hs,he⟩ := hb P ((le_max_left _ _).trans hP) φ hφ hφ1 hWP
  simp only [Nat.cast_zero,neg_zero,Real.rpow_zero] at he
  have hvolume := volume_factor_bound P φ η hP1 hφ hη hηmax hφmax
  have hone : 1 ≤ P^(7-(1:ℝ)/8) := Real.one_le_rpow hP1 (by norm_num)
  refine ⟨hs,he.trans ?_⟩
  calc
    _ ≤ C*(1+(2:ℝ)^31*P^(7-(1:ℝ)/8)) :=
      mul_le_mul_of_nonneg_left (add_le_add le_rfl hvolume) (zero_le_one.trans hC)
    _ ≤ _ := by nlinarith only [hone,hC]

end CubicTenVariables.SingletonNonzeroFrequencySaving
