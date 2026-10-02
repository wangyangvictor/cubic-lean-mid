import CubicTenVariables.LocalizedGlobalNonzeroSaving
import CubicTenVariables.FlexibleCountingNumerics

/-! Actual localized count equals its exact zero-frequency contribution
with a global power-saving error. Delta kernels and cubic localization are
proved internally; Schwartz Poisson remains an explicit input of this wrapper.
The localized arithmetic shifted-average hypothesis remains explicit.
No positivity or asymptotic evaluation of the zero term is asserted. -/
set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.LocalizedCountPowerSaving
open MvPolynomial DeltaMethod RealRegularGradientChart LocalizedShiftedWindow
open LocalizedPoissonCount

/-- The kernel and positive fixed phase loss are selected before the
physical scales. Every original modulus and clipped arc is included.
The scale window also gives Q²/P³ ≤ P^(-η), needed by the main term. -/
theorem exists_bound 
    (poisson : Literature.SteinShakarchi2011Poisson)
    
    (G : MvPolynomial (Fin 10) ℤ) (hG : G.IsHomogeneous 3)
    (D : Data (map (Int.castRingHom ℝ) G)) (W : ℕ) (hW : 0 < W)
    (Ω : Set (Fin 10 → ZMod W)) (b : ℝ) (hb : b < 20/3)
    (hshift : CleanShiftedAverage G W Ω b) :
    ∃ p : ℕ → ℕ → ℝ → ℂ, KernelEstimates 1 p ∧
      ∃ η δ C P₀ : ℝ, 0 < η ∧ η ≤ 1/4 ∧ 0 < δ ∧ δ ≤ 1 ∧ 1 ≤ C ∧ 4 ≤ P₀ ∧
      ∀ P Q : ℕ, P₀ ≤ (P:ℝ) → 1 ≤ Q →
        (P:ℝ)^((3:ℝ)/2-η) ≤ (Q:ℝ) → (Q:ℝ) ≤ (P:ℝ)^((3:ℝ)/2-η/2) →
        ‖(localizedWeightedCount G D.weight.weight D.weight.boxRadius P W Ω:ℂ) -
          zeroTerm G D.weight.weight P Q W Ω η p‖ ≤ C*(P:ℝ)^(7-δ) := by
  have hweight (y : Fin 10 → ℝ) : |D.weight.weight y| ≤ 1 := by
    rw [abs_of_nonneg (D.weight.bounds y).1]
    exact (D.weight.bounds y).2
  obtain ⟨p,hp,hdelta⟩ := exists_count_decomposition poisson G D.weight.weight
    D.weight.boxRadius W D.weight.supported D.weight.zero_at_origin
    D.weight.smooth D.weight.compact hW 1 hweight Ω
  obtain ⟨δ,η₀,Cg,P₀,hδ,hδ1,hη₀,hη₀1,hCg,hP₀,hglobal⟩ :=
    LocalizedGlobalNonzeroSaving.exists_power_saving poisson G hG D W hW Ω b hb hshift p hp
  let η : ℝ := η₀/2
  have hη : 0 < η := half_pos hη₀
  have hηquarter : η ≤ 1/4 := by dsimp [η]; linarith
  have hηsum : η+η ≤ η₀ := by dsimp [η]; linarith
  obtain ⟨N,hN,horder⟩ := FlexibleCountingNumerics.exists_delta_order η 1 hη
  obtain ⟨Cd,hCd,happrox⟩ := hdelta η hη N hN
  refine ⟨p,hp,η,δ,Cd+Cg,P₀,hη,hηquarter,hδ,hδ1,by linarith,hP₀,?_⟩
  intro P Q hP hQ hQlo hQhi
  have hP1 : (1:ℝ) ≤ P := by linarith
  have hPn : 1 ≤ P := by exact_mod_cast hP1
  have ha := happrox P Q hPn hQ
  have hQbase : (Q:ℝ) ≤ (P:ℝ)^((3:ℝ)/2) := hQhi.trans
    (Real.rpow_le_rpow_of_exponent_le hP1 (by linarith only [hη]))
  have hPQ : (P:ℝ) ≤ (Q:ℝ) := calc
    (P:ℝ) = (P:ℝ)^(1:ℝ) := (Real.rpow_one _).symm
    _ ≤ (P:ℝ)^((3:ℝ)/2-η) :=
      Real.rpow_le_rpow_of_exponent_le hP1 (by linarith only [hηquarter])
    _ ≤ (Q:ℝ) := hQlo
  have hg := hglobal P Q hP hQ η hη.le hQlo hQbase η hη.le hηsum
  have hd := horder (P:ℝ) (Q:ℝ) hP1 hPQ
  have hminor : (P:ℝ)^(-1:ℝ) ≤ (P:ℝ)^(7-δ) :=
    Real.rpow_le_rpow_of_exponent_le hP1 (by linarith only [hδ1])
  let Ncount : ℂ := localizedWeightedCount G D.weight.weight D.weight.boxRadius P W Ω
  let Z : ℂ := zeroTerm G D.weight.weight P Q W Ω η p
  let E : ℂ := nonzeroTerm G D.weight.weight P Q W Ω η p
  change ‖Ncount-Z‖ ≤ _
  change ‖Ncount-(Z+E)‖ ≤ _ at ha
  change ‖E‖ ≤ _ at hg
  calc
    _ = ‖(Ncount-(Z+E))+E‖ := by congr 1; ring
    _ ≤ ‖Ncount-(Z+E)‖+‖E‖ := norm_add_le _ _
    _ ≤ Cd*(P:ℝ)^10*(Q:ℝ)^(-(N:ℝ)*η)+Cg*(P:ℝ)^(7-δ) := add_le_add ha hg
    _ = Cd*((P:ℝ)^10*(Q:ℝ)^(-(N:ℝ)*η))+Cg*(P:ℝ)^(7-δ) := by ring
    _ ≤ Cd*(P:ℝ)^(-1:ℝ)+Cg*(P:ℝ)^(7-δ) :=
      add_le_add (mul_le_mul_of_nonneg_left hd (zero_le_one.trans hCd)) le_rfl
    _ ≤ Cd*(P:ℝ)^(7-δ)+Cg*(P:ℝ)^(7-δ) :=
      add_le_add (mul_le_mul_of_nonneg_left hminor (zero_le_one.trans hCd)) le_rfl
    _ = _ := by ring

/-- Source-facing form with the actual regular weight constructed from
the absence of a nonzero integer zero, as in the circle-method reduction. -/
theorem exists_data_and_bound 
    (poisson : Literature.SteinShakarchi2011Poisson)
    
    (G : MvPolynomial (Fin 10) ℤ) (hG : G.IsHomogeneous 3)
    (hzero : ¬ HasIntegerZero G) (W : ℕ) (hW : 0 < W)
    (Ω : Set (Fin 10 → ZMod W)) (b : ℝ) (hb : b < 20/3)
    (hshift : CleanShiftedAverage G W Ω b) :
    ∃ D : Data (map (Int.castRingHom ℝ) G),
    ∃ p : ℕ → ℕ → ℝ → ℂ, KernelEstimates 1 p ∧
      ∃ η δ C P₀ : ℝ, 0 < η ∧ η ≤ 1/4 ∧ 0 < δ ∧ δ ≤ 1 ∧ 1 ≤ C ∧ 4 ≤ P₀ ∧
      ∀ P Q : ℕ, P₀ ≤ (P:ℝ) → 1 ≤ Q →
        (P:ℝ)^((3:ℝ)/2-η) ≤ (Q:ℝ) → (Q:ℝ) ≤ (P:ℝ)^((3:ℝ)/2-η/2) →
        ‖(localizedWeightedCount G D.weight.weight D.weight.boxRadius P W Ω:ℂ) -
          zeroTerm G D.weight.weight P Q W Ω η p‖ ≤ C*(P:ℝ)^(7-δ) := by
  obtain ⟨D⟩ := NonzeroFrequencySaving.exists_integer_data G hG hzero
  exact ⟨D,exists_bound poisson G hG D W hW Ω b hb hshift⟩

end CubicTenVariables.LocalizedCountPowerSaving
