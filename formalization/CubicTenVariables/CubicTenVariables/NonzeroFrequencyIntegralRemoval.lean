import CubicTenVariables.DyadicFiniteLocalization
import CubicTenVariables.DyadicAveragedVolumeBound
import CubicTenVariables.FiniteFrequencyRemainder

/-! Actual nonzero-frequency error reduced to a finite localized expression,
then to the literal shifted complete-sum bound with no remaining integral.
Cubic oscillatory localization is proved internally. No shifted-average bound
is asserted: it remains the arithmetic antecedent required by the paper. -/
set_option autoImplicit false
set_option maxHeartbeats 1500000
noncomputable section
namespace CubicTenVariables.NonzeroFrequencyIntegralRemoval
open MvPolynomial MeasureTheory RealRegularGradientChart DyadicFrequencyError
open LocalSupremumNumerics GradientVolumeNumerics DyadicWindowIntegral
open LocalSupremumWindow ShiftedCompleteSumWindow DyadicAveragedVolumeBound

/-- The actual infinite error, whose frequency summability is part of the
conclusion, is bounded by the localized finite integral plus arbitrary decay. -/
theorem exists_localized_bound 
    (G : MvPolynomial (Fin 10) ℤ) (hG : G.IsHomogeneous 3)
    (D : Data (map (Int.castRingHom ℝ) G)) (η : ℝ) (hη : 0 < η) (hη1 : η ≤ 1) (A : ℕ) :
    ∃ C P₀ : ℝ, 1 ≤ C ∧ 1 ≤ P₀ ∧ ∀ P : ℝ, P₀ ≤ P →
      ∀ R φ : ℝ, 1 ≤ R → 0 < φ → φ ≤ 1 → 2*R ≤ P^2 →
      (∀ q ∈ moduli R, Summable (term G D.weight.weight P φ q)) ∧
      error G D.weight.weight P R φ ≤ C*(P^(-(A : ℝ))+
        localizedError G (map (Int.castRingHom ℝ) G) D P R φ
          (P^η*V P R φ) (P^η*Vzero P R φ)) := by
  obtain ⟨Ct,Pt,hCt,hPt,ht⟩ := DyadicFrequencyTruncation.exists_bound G hG D η hη A
  obtain ⟨Cl,Pl,hCl,hPl,hl⟩ := DyadicFiniteLocalization.exists_truncatedError_le_localized
    G hG D η hη (A+54)
  let K : ℝ := 8*7^10
  let C : ℝ := Ct+Cl*(K+1)
  have hK : 0 ≤ K := by norm_num [K]
  have hC : 1 ≤ C := by dsimp [C]; nlinarith
  refine ⟨C,max Pt Pl,hC,hPt.trans (le_max_left _ _),?_⟩
  intro P hP R φ hR hφ hφ1 hRP
  have hPtP : Pt ≤ P := (le_max_left _ _).trans hP
  have hPlP : Pl ≤ P := (le_max_right _ _).trans hP
  have hP1 : 1 ≤ P := hPt.trans hPtP
  have hP0 : 0 < P := zero_lt_one.trans_le hP1
  have hR0 : 0 ≤ R := zero_le_one.trans hR
  have hB0 : 0 ≤ P^η*V P R φ := by have hv := V_pos P R φ hP0 (zero_lt_one.trans_le hR); positivity
  have hB : P^η*V P R φ ≤ P^5 :=
    FiniteFrequencyRemainder.cutoff_le_fifth_power P R φ η hP1 hR0 (by linarith) hφ1 hη1
  have hrem := FiniteFrequencyRemainder.bound G P R φ (P^η*V P R φ) 5 A
    hP1 hR hφ.le hφ1 hRP hB0 hB
  rw [show A+10*5+4=A+54 by omega] at hrem
  obtain ⟨hs,hte⟩ := ht P hPtP R φ hR hφ hφ1 hRP
  have hle := hl P hPlP R φ (P^η*V P R φ) hR hφ
  have hloc0 : 0 ≤ localizedError G (map (Int.castRingHom ℝ) G) D P R φ
      (P^η*V P R φ) (P^η*Vzero P R φ) := by
    unfold localizedError
    exact mul_nonneg (by positivity) (integral_nonneg (integrand_nonneg _ _ _ _ _ _ _))
  have hpdec : 0 ≤ P^(-(A : ℝ)) := by positivity
  refine ⟨hs,hte.trans ?_⟩
  apply (add_le_add hle le_rfl).trans
  calc
    _ ≤ Cl*(K*P^(-(A : ℝ))+localizedError G (map (Int.castRingHom ℝ) G) D P R φ
        (P^η*V P R φ) (P^η*Vzero P R φ))+Ct*P^(-(A : ℝ)) := by
      apply add_le_add _ le_rfl
      exact mul_le_mul_of_nonneg_left (add_le_add hrem le_rfl) (zero_le_one.trans hCl)
    _ ≤ _ := by
      dsimp [C]
      nlinarith [mul_nonneg (show 0 ≤ Ct+Cl*K by positivity) hloc0,
        mul_nonneg (zero_le_one.trans hCl) hpdec]

/-- The actual E(P;R,phi), with no remaining integration or convergence
premise, from a uniform shifted arithmetic bound H on the required centers. -/
theorem exists_bound 
    (G : MvPolynomial (Fin 10) ℤ) (hG : G.IsHomogeneous 3)
    (D : Data (map (Int.castRingHom ℝ) G)) (ε : ℝ) (hε : 0 < ε) (hε17 : ε ≤ 17) (A : ℕ) :
    ∃ C P₀ : ℝ, 1 ≤ C ∧ 1 ≤ P₀ ∧ ∀ P : ℝ, P₀ ≤ P →
      ∀ R φ H : ℝ, 1 ≤ R → 0 < φ → φ ≤ 1 → 2*R ≤ P^2 → 0 ≤ H →
      ∀ L : ℕ,
      (∀ v ∈ centers (frequencies 10 (P^(ε/17)*V P R φ)) L, shiftedSum G R L v ≤ H) →
      (∀ q ∈ moduli R, Summable (term G D.weight.weight P φ q)) ∧
      error G D.weight.weight P R φ ≤ C*(P^(-(A : ℝ))+
        φ*(H/((2*L+1 : ℕ) : ℝ)^10)*(R^10)⁻¹*volumeFactor ε P R φ (L : ℝ)) := by
  obtain ⟨Ce,P₀,hCe,hP₀,he⟩ := exists_localized_bound G hG D (ε/17) (by positivity) (by linarith) A
  obtain ⟨Cv,hCv,hv⟩ := DyadicAveragedVolumeBound.exists_localizedError_bound
    (map (Int.castRingHom ℝ) G) (hG.map _) D
  refine ⟨Ce*Cv,P₀,one_le_mul_of_one_le_of_one_le hCe hCv,hP₀,?_⟩
  intro P hP R φ H hR hφ hφ1 hRP hH L hshift
  obtain ⟨hs,hebound⟩ := he P hP R φ hR hφ hφ1 hRP
  have hvbound := hv G ε P R φ H L hε (hP₀.trans hP) hR hφ hH hshift
  have hpdec : 0 ≤ P^(-(A : ℝ)) := by
    exact Real.rpow_nonneg (zero_le_one.trans (hP₀.trans hP)) _
  refine ⟨hs,hebound.trans ?_⟩
  calc
    _ ≤ Ce*(Cv*P^(-(A : ℝ))+
        Cv*φ*(H/((2*L+1 : ℕ) : ℝ)^10)*(R^10)⁻¹*volumeFactor ε P R φ (L : ℝ)) :=
      mul_le_mul_of_nonneg_left
        (add_le_add (le_mul_of_one_le_left hpdec hCv) hvbound) (zero_le_one.trans hCe)
    _ = _ := by ring

end CubicTenVariables.NonzeroFrequencyIntegralRemoval
