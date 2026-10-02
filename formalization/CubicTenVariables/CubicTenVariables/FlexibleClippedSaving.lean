import CubicTenVariables.LocalizedClippedSaving
import CubicTenVariables.SingletonClippedSaving
import CubicTenVariables.CountingScaleRange

/-! Actual clipped block savings when the circle-method scale is slightly
smaller than P^(3/2). The original kernel and arcs retain their parameter η;
only the analytic saving is applied with the larger loss η+ν. Constants are
uniform in both losses and in every scale within the displayed window. -/
set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.FlexibleClippedSaving
open MvPolynomial DeltaMethod RealRegularGradientChart DyadicFrequencyError
open LocalizedShiftedWindow LocalizedClippedFrequency LocalizedFiniteBlockAssembly
open scoped BigOperators
attribute [local instance] Classical.propDecidable

/-- Inadmissible widths contribute empty clipped dyadic blocks also at the
smaller circle-method scale. -/
theorem block_eq_zero_of_not_le (G : MvPolynomial (Fin 10) ℤ)
    (w : (Fin 10 → ℝ) → ℝ) (P Q W : ℕ) (Ω : Set (Fin 10 → ZMod W))
    (R φ η ν : ℝ) (p : ℕ → ℕ → ℝ → ℂ)
    (hP : 1 ≤ (P:ℝ)) (hR : 1 ≤ R) (hν : 0 ≤ ν)
    (hη : 0 ≤ η) (hη1 : η ≤ 1)
    (hQlower : (P:ℝ)^((3:ℝ)/2-ν) ≤ (Q:ℝ))
    (hφ : ¬ φ ≤ (R*(P:ℝ)^((3:ℝ)/2))^(-1+(η+ν))) :
    block G w P Q W Ω R φ η p=0 := by
  apply Finset.sum_eq_zero
  intro q hq
  by_cases hqQ : q ≤ Q
  · simp only [if_pos hqQ]
    rw [CountingScaleRange.intersection_eq_empty_of_not_le
      (P:ℝ) R φ η ν Q q hP hR hν hη hη1 hQlower hq hφ]
    simp
  · simp only [if_neg hqQ]

/-- The singleton's empty-arc branch requires no artificial dyadic block. -/
theorem oneBlock_eq_zero_of_not_le (G : MvPolynomial (Fin 10) ℤ)
    (w : (Fin 10 → ℝ) → ℝ) (P Q W : ℕ) (Ω : Set (Fin 10 → ZMod W))
    (φ η ν : ℝ) (p : ℕ → ℕ → ℝ → ℂ)
    (hP : 1 ≤ (P:ℝ)) (hν : 0 ≤ ν) (hη : 0 ≤ η) (hη1 : η ≤ 1)
    (hQlower : (P:ℝ)^((3:ℝ)/2-ν) ≤ (Q:ℝ))
    (hφ : ¬ φ ≤ ((P:ℝ)^((3:ℝ)/2))^(-1+(η+ν))) :
    oneBlock G w P Q W Ω φ η p=0 := by
  have he := CountingScaleRange.one_intersection_eq_empty_of_not_le
    (P:ℝ) φ η ν Q hP hν hη hη1 hQlower hφ
  simp [oneBlock,he]

/-- Dyadic blocks throughout the flexible scale window retain a uniform
positive saving. The arithmetic shifted-average antecedent stays explicit. -/
theorem exists_block_power_saving 
    (G : MvPolynomial (Fin 10) ℤ) (hG : G.IsHomogeneous 3)
    (D : Data (map (Int.castRingHom ℝ) G)) (W : ℕ) (hW : 0 < W)
    (Ω : Set (Fin 10 → ZMod W)) (b : ℝ) (hb : b < 20/3)
    (hshift : CleanShiftedAverage G W Ω b)
    (p : ℕ → ℕ → ℝ → ℂ) (hp : KernelEstimates 1 p) :
    ∃ δ η₀ C P₀ : ℝ, 0 < δ ∧ 0 < η₀ ∧ η₀ ≤ 1/2 ∧ 1 ≤ C ∧ 4 ≤ P₀ ∧
      ∀ P Q : ℕ, P₀ ≤ (P:ℝ) → 1 ≤ Q →
      ∀ ν : ℝ, 0 ≤ ν → (P:ℝ)^((3:ℝ)/2-ν) ≤ (Q:ℝ) →
        (Q:ℝ) ≤ (P:ℝ)^((3:ℝ)/2) →
      ∀ R φ η : ℝ, 1 ≤ R → R ≤ (P:ℝ)^((3:ℝ)/2) → 0 < φ →
        0 ≤ η → η+ν ≤ η₀ →
        ‖block G D.weight.weight P Q W Ω R φ η p‖ ≤ C*(P:ℝ)^(7-δ) := by
  obtain ⟨δ,η₀,C,P₀,hδ,hη₀,hC,hP₀,hbound⟩ :=
    LocalizedNonzeroFrequencySaving.exists_power_saving G hG D W hW Ω b hb hshift
  obtain ⟨K,hK,hkernel⟩ := hp.bounded
  refine ⟨δ,min η₀ (1/2),K*C,P₀,hδ,lt_min hη₀ (by norm_num),min_le_right _ _,
    one_le_mul_of_one_le_of_one_le hK hC,hP₀,?_⟩
  intro P Q hP hQ ν hν hQlower _hQupper R φ η hR hRP hφ hη hην
  have hP1 : 1 ≤ (P:ℝ) := by linarith only [hP₀,hP]
  have hPpos : 0 < P := by exact_mod_cast (zero_lt_one.trans_le hP1)
  have hη1 : η ≤ 1 := by
    have hh := hην.trans (min_le_right η₀ (1/2))
    linarith only [hh,hν]
  by_cases hphase : φ ≤ (R*(P:ℝ)^((3:ℝ)/2))^(-1+(η+ν))
  · obtain ⟨hsum,he⟩ := hbound (P:ℝ) R φ (η+ν) hP hR hRP hφ (add_nonneg hη hν)
      (hην.trans (min_le_left _ _)) hphase
    have hqpos (q : ℕ) (hq : q ∈ moduli R) : 1 ≤ q := by
      have hqR := (mem_moduli R q).mp hq
      exact_mod_cast (le_of_lt (lt_of_le_of_lt hR hqR.1))
    have hc := block_bound G D.weight.weight D.weight.smooth.continuous D.weight.compact
      P Q W hPpos Ω R φ η p K (zero_le_one.trans hK)
      (fun q hq hqQ => (hp.smooth Q hQ q (hqpos q hq) hqQ).continuous.measurable)
      (fun q hq hqQ θ _ => hkernel Q hQ q (hqpos q hq) hqQ θ) hsum
    exact hc.trans (by simpa only [mul_assoc] using
      mul_le_mul_of_nonneg_left he (zero_le_one.trans hK))
  · rw [block_eq_zero_of_not_le G D.weight.weight P Q W Ω R φ η ν p
      hP1 hR hν hη hη1 hQlower hphase,norm_zero]
    exact mul_nonneg (by positivity) (Real.rpow_nonneg (Nat.cast_nonneg P) _)

/-- The actual singleton block satisfies the same flexible-window form,
without any arithmetic shifted-average antecedent. -/
theorem exists_one_power_saving 
    (G : MvPolynomial (Fin 10) ℤ) (hG : G.IsHomogeneous 3)
    (D : Data (map (Int.castRingHom ℝ) G)) (W : ℕ) (hW : 0 < W)
    (Ω : Set (Fin 10 → ZMod W))
    (p : ℕ → ℕ → ℝ → ℂ) (hp : KernelEstimates 1 p) :
    ∃ δ η₀ C P₀ : ℝ, 0 < δ ∧ 0 < η₀ ∧ η₀ ≤ 1/2 ∧ 1 ≤ C ∧ 4 ≤ P₀ ∧
      ∀ P Q : ℕ, P₀ ≤ (P:ℝ) → 1 ≤ Q →
      ∀ ν : ℝ, 0 ≤ ν → (P:ℝ)^((3:ℝ)/2-ν) ≤ (Q:ℝ) →
        (Q:ℝ) ≤ (P:ℝ)^((3:ℝ)/2) →
      ∀ φ η : ℝ, 0 < φ → 0 ≤ η → η+ν ≤ η₀ →
        ‖oneBlock G D.weight.weight P Q W Ω φ η p‖ ≤ C*(P:ℝ)^(7-δ) := by
  obtain ⟨δ,η₀,C,P₀,hδ,hη₀,_hη1,hC,hP₀,hbound⟩ :=
    SingletonNonzeroFrequencySaving.exists_power_saving G hG D W hW Ω
  obtain ⟨K,hK,hkernel⟩ := hp.bounded
  refine ⟨δ,min η₀ (1/2),K*C,P₀,hδ,lt_min hη₀ (by norm_num),min_le_right _ _,
    one_le_mul_of_one_le_of_one_le hK hC,hP₀,?_⟩
  intro P Q hP hQ ν hν hQlower _hQupper φ η hφ hη hην
  have hP1 : 1 ≤ (P:ℝ) := by linarith only [hP₀,hP]
  have hPpos : 0 < P := by exact_mod_cast (zero_lt_one.trans_le hP1)
  have hη1 : η ≤ 1 := by
    have hh := hην.trans (min_le_right η₀ (1/2))
    linarith only [hh,hν]
  by_cases hphase : φ ≤ ((P:ℝ)^((3:ℝ)/2))^(-1+(η+ν))
  · obtain ⟨hsum,he⟩ := hbound (P:ℝ) φ (η+ν) hP hφ (add_nonneg hη hν)
      (hην.trans (min_le_left _ _)) hphase
    have hc := SingletonClippedSaving.oneBlock_le_error
      G D.weight.weight D.weight.smooth.continuous D.weight.compact P Q W hPpos Ω φ η p
      (hp.smooth Q hQ 1 le_rfl hQ).continuous.measurable K (zero_le_one.trans hK)
      (fun θ _ => hkernel Q hQ 1 le_rfl hQ θ) hsum
    exact hc.trans (by simpa only [mul_assoc] using
      mul_le_mul_of_nonneg_left he (zero_le_one.trans hK))
  · rw [oneBlock_eq_zero_of_not_le G D.weight.weight P Q W Ω φ η ν p
      hP1 hν hη hη1 hQlower hphase,norm_zero]
    exact mul_nonneg (by positivity) (Real.rpow_nonneg (Nat.cast_nonneg P) _)

end CubicTenVariables.FlexibleClippedSaving
