import CubicTenVariables.LocalizedNonzeroFrequencyIntegralRemoval
import CubicTenVariables.LocalizedCleanShiftedSpecialization
import CubicTenVariables.NonzeroFrequencyCoefficient
import CubicTenVariables.NonzeroFrequencyPhaseNumerics
import CubicTenVariables.NonzeroFrequencySaving
import CubicTenVariables.LocalizedNonzeroFrequencyNumerics

/-! The literal localized dyadic nonzero-frequency error satisfies the source power
saving, relative to the explicit shifted-average antecedent. The antecedent is not asserted to hold here. -/
set_option autoImplicit false
set_option maxHeartbeats 1500000
noncomputable section
namespace CubicTenVariables.LocalizedNonzeroFrequencySaving
open MvPolynomial RealRegularGradientChart DyadicFrequencyError
open LocalSupremumNumerics GradientVolumeNumerics LocalSupremumWindow
open LocalizedShiftedWindow NonzeroFrequencyNumerics DyadicAveragedVolumeBound

/-- Explicit epsilon/eta losses in the source n=10 nonzero-frequency
implication. The constants precede every physical scale and phase parameter,
and convergence of the actual infinite frequency sums is a conclusion. -/
theorem exists_bound 
    (G : MvPolynomial (Fin 10) ℤ) (hG : G.IsHomogeneous 3)
    (D : Data (map (Int.castRingHom ℝ) G)) (W : ℕ) (hW : 0 < W)
    (Ω : Set (Fin 10 → ZMod W)) (b : ℝ) (hb : b < 20/3)
    (hshift : CleanShiftedAverage G W Ω b) (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ C P₀ : ℝ, 1 ≤ C ∧ 4 ≤ P₀ ∧ ∀ P R φ η : ℝ,
      P₀ ≤ P → 1 ≤ R → R ≤ P^((3 : ℝ)/2) → 0 < φ →
      0 ≤ η → η ≤ 1 → φ ≤ (R*P^((3 : ℝ)/2))^(-1+η) →
      (∀ q ∈ moduli R, Summable (LocalizedDyadicFrequencyError.term G W Ω D.weight.weight P φ q)) ∧
      LocalizedFrequencyComparison.error G W Ω D.weight.weight P R φ ≤
        C*(1+P^(7+(18+(20/3-b))*(η+ε)-saving (20/3-b))) := by
  obtain ⟨Ce,Pe,hCe,hPe,he⟩ :=
    LocalizedNonzeroFrequencyIntegralRemoval.exists_bound G hG D W hW Ω ε hε (by linarith) 0
  obtain ⟨Ca,hCa,ha⟩ := LocalizedCleanShiftedSpecialization.exists_bound G W Ω b hshift ε hε
  let K : ℝ := Ca*(2:ℝ)^31
  have hK : 1 ≤ K := one_le_mul_of_one_le_of_one_le hCa (by norm_num)
  refine ⟨Ce*K,max Pe (max 4 ((2*(W:ℝ))^2)),one_le_mul_of_one_le_of_one_le hCe hK,
    (le_max_left _ _).trans (le_max_right _ _),?_⟩
  intro P R φ η hP hR hRP hφ hη hη1 hφmax
  have hPeP : Pe ≤ P := (le_max_left _ _).trans hP
  have hP4 : 4 ≤ P := ((le_max_left _ _).trans (le_max_right _ _)).trans hP
  have hPW : (2*(W:ℝ))^2 ≤ P := ((le_max_right _ _).trans (le_max_right _ _)).trans hP
  have hP1 : 1 ≤ P := by linarith
  have hP0 : 0 < P := by linarith
  have hR0 : 0 < R := zero_lt_one.trans_le hR
  have hφ1 := NonzeroFrequencyCoefficient.phase_le_one P R φ η hP1 hR hη1 hφmax
  have hRP2 := LocalizedNonzeroFrequencyNumerics.twice_weighted_radius_le_square
    P R (W:ℝ) (by exact_mod_cast hW) hPW hRP
  let L : ℕ := cubeRootWidth R
  let H : ℝ := Ca*P^(7*ε)*((L:ℝ)+R^((1:ℝ)/3))^10*R^b
  have hH : 0 ≤ H := by dsimp [H]; positivity
  have hshiftH : ∀ v ∈ centers (frequencies 10 (P^(ε/17)*V P R φ)) L,
      shiftedSum G W Ω R L v ≤ H := by
    intro v hv
    exact ha P R φ (ε/17) hP1 hR hRP hφ1 (by linarith) v hv
  obtain ⟨hs,herr⟩ := he P hPeP R φ H hR hφ hφ1 hRP2 hH L hshiftH
  simp only [Nat.cast_zero,neg_zero,Real.rpow_zero] at herr
  let E : ℝ := 7+(18+(20/3-b))*(η+ε)-saving (20/3-b)
  have hv : 0 < V P R φ := V_pos P R φ hP0 hR0
  have hz : 0 < Vzero P R φ := Vzero_pos P R φ hP0 hR0
  have hcoef : φ*(H/((2*L+1 : ℕ):ℝ)^10)*(R^10)⁻¹*
      volumeFactor ε P R φ (L:ℝ) ≤ K*P^E := by
    by_cases hcut : P^(ε/17)*V P R φ < 1
    · simp only [volumeFactor,if_pos hcut,mul_zero]
      positivity
    · have hgeom : 0 ≤ (if 1 < φ*P^3 then
          (1+(L:ℝ)/V P R φ)^7*(1+Vzero P R φ+(L:ℝ))^3*(Vzero P R φ)^7
          else (V P R φ+(L:ℝ))^10) := by split_ifs <;> positivity
      unfold volumeFactor
      rw [if_neg hcut]
      apply (NonzeroFrequencyCoefficient.cubeRoot_coefficient_le P R φ Ca ε b _
        hP1 hR hφ.le (zero_le_one.trans hCa) hgeom).trans
      have hp := NonzeroFrequencyPhaseNumerics.optimized_bound P R φ b ε η (ε/17)
        hP1 hR hφ hη (by positivity) hb hRP hφmax (le_of_not_gt hcut)
      calc
        _ ≤ Ca*P^(7*ε)*((2:ℝ)^31*
            P^(7+ε+18*η+((20/3-b)+5/2)*(ε/17)-saving (20/3-b))) :=
          mul_le_mul_of_nonneg_left hp (by positivity)
        _ = K*(P^(7*ε)*P^(7+ε+18*η+((20/3-b)+5/2)*(ε/17)-saving (20/3-b))) := by
          dsimp [K]; ring
        _ ≤ _ := mul_le_mul_of_nonneg_left
          (NonzeroFrequencyCoefficient.exponent_combine P (20/3-b) η ε
            hP1 (sub_pos.mpr hb) hη hε.le) (zero_le_one.trans hK)
  refine ⟨hs,herr.trans ?_⟩
  calc
    _ ≤ Ce*(1+K*P^E) :=
      mul_le_mul_of_nonneg_left (add_le_add le_rfl hcoef) (zero_le_one.trans hCe)
    _ ≤ Ce*K*(1+P^E) := by nlinarith only [hK, hCe]

/-- Choosing the two small losses gives a genuine positive power saving
below P^7, uniformly for all sufficiently small nonnegative phase losses. -/
theorem exists_power_saving 
    (G : MvPolynomial (Fin 10) ℤ) (hG : G.IsHomogeneous 3)
    (D : Data (map (Int.castRingHom ℝ) G)) (W : ℕ) (hW : 0 < W)
    (Ω : Set (Fin 10 → ZMod W)) (b : ℝ) (hb : b < 20/3)
    (hshift : CleanShiftedAverage G W Ω b) :
    ∃ δ η₀ C P₀ : ℝ, 0 < δ ∧ 0 < η₀ ∧ 1 ≤ C ∧ 4 ≤ P₀ ∧
      ∀ P R φ η : ℝ, P₀ ≤ P → 1 ≤ R → R ≤ P^((3 : ℝ)/2) →
        0 < φ → 0 ≤ η → η ≤ η₀ → φ ≤ (R*P^((3 : ℝ)/2))^(-1+η) →
        (∀ q ∈ moduli R, Summable (LocalizedDyadicFrequencyError.term G W Ω D.weight.weight P φ q)) ∧
        LocalizedFrequencyComparison.error G W Ω D.weight.weight P R φ ≤ C*P^(7-δ) := by
  let β : ℝ := 20/3-b
  let s : ℝ := saving β
  let c : ℝ := 18+β
  let ε : ℝ := s/(8*c)
  have hβ : 0 < β := sub_pos.mpr hb
  have hs : 0 < s := saving_pos β hβ
  have hsmax : s ≤ 1/4 := min_le_left _ _
  have hc : 0 < c := by dsimp [c]; linarith
  have hε : 0 < ε := div_pos hs (by positivity)
  have hε1 : ε ≤ 1 := by
    apply (div_le_iff₀ (by positivity : 0 < 8*c)).mpr
    dsimp [c]
    nlinarith only [hsmax,hβ]
  have hce : c*(ε+ε)=s/4 := by dsimp [ε]; field_simp; ring
  obtain ⟨C,P₀,hC,hP₀,hbound⟩ := exists_bound G hG D W hW Ω b hb hshift ε hε hε1
  refine ⟨s/2,ε,2*C,P₀,by positivity,hε,by linarith,hP₀,?_⟩
  intro P R φ η hP hR hRP hφ hη hηε hφmax
  have hP1 : 1 ≤ P := by linarith
  have hP0 : 0 < P := zero_lt_one.trans_le hP1
  obtain ⟨hsum,herr⟩ := hbound P R φ η hP hR hRP hφ hη (hηε.trans hε1) hφmax
  have hloss : c*(η+ε) ≤ s/4 := by
    rw [← hce]
    exact mul_le_mul_of_nonneg_left (add_le_add hηε le_rfl) hc.le
  have hexp : 7+(18+(20/3-b))*(η+ε)-saving (20/3-b) ≤ 7-s/2 := by
    change 7+c*(η+ε)-s ≤ 7-s/2
    linarith only [hloss,hs]
  have hp := Real.rpow_le_rpow_of_exponent_le hP1 hexp
  have hone : 1 ≤ P^(7-s/2) := Real.one_le_rpow hP1 (by linarith only [hsmax])
  refine ⟨hsum,herr.trans ?_⟩
  calc
    _ ≤ C*(1+P^(7-s/2)) :=
      mul_le_mul_of_nonneg_left (add_le_add le_rfl hp) (zero_le_one.trans hC)
    _ ≤ 2*C*P^(7-s/2) := by nlinarith only [hone,hC]

/-- Source-facing form: rational anisotropy supplies the fixed regular
weight, and the explicit shifted-average hypothesis gives the actual
nonzero-frequency power saving using proved cubic localization. -/
theorem exists_data_and_power_saving 
    (G : MvPolynomial (Fin 10) ℤ) (hG : G.IsHomogeneous 3)
    (hzero : ¬ HasIntegerZero G) (W : ℕ) (hW : 0 < W)
    (Ω : Set (Fin 10 → ZMod W)) (b : ℝ) (hb : b < 20/3)
    (hshift : CleanShiftedAverage G W Ω b) :
    ∃ D : Data (map (Int.castRingHom ℝ) G),
      ∃ δ η₀ C P₀ : ℝ, 0 < δ ∧ 0 < η₀ ∧ 1 ≤ C ∧ 4 ≤ P₀ ∧
        ∀ P R φ η : ℝ, P₀ ≤ P → 1 ≤ R → R ≤ P^((3 : ℝ)/2) →
          0 < φ → 0 ≤ η → η ≤ η₀ → φ ≤ (R*P^((3 : ℝ)/2))^(-1+η) →
          (∀ q ∈ moduli R, Summable (LocalizedDyadicFrequencyError.term G W Ω D.weight.weight P φ q)) ∧
          LocalizedFrequencyComparison.error G W Ω D.weight.weight P R φ ≤ C*P^(7-δ) := by
  obtain ⟨D⟩ := NonzeroFrequencySaving.exists_integer_data G hG hzero
  exact ⟨D,exists_power_saving G hG D W hW Ω b hb hshift⟩

end CubicTenVariables.LocalizedNonzeroFrequencySaving
