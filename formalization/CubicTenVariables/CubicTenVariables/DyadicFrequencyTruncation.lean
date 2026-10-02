import CubicTenVariables.DyadicOscillatoryControl
import CubicTenVariables.CompleteSumFrequencyTail

/-! Absolute convergence and rapid truncation of the manuscript's literal
nonzero-frequency dyadic error, using proved cubic localization.
No arithmetic saving is assumed here. -/
set_option autoImplicit false
set_option maxHeartbeats 1500000
noncomputable section
namespace CubicTenVariables.DyadicFrequencyTruncation
open MvPolynomial MeasureTheory RealRegularGradientChart DyadicFrequencyError
open LocalSupremumNumerics LocalSupremumWindow
open scoped BigOperators

/-- Summing the actual convergent frequency tails over the dyadic moduli,
with their original q^-10 weights. -/
theorem exists_weighted_bound 
    (G : MvPolynomial (Fin 10) ℤ) (hG : G.IsHomogeneous 3)
    (D : Data (map (Int.castRingHom ℝ) G)) (η : ℝ) (hη : 0 < η) (A : ℕ) :
    ∃ C P₀ : ℝ, 1 ≤ C ∧ 1 ≤ P₀ ∧ ∀ P : ℝ, P₀ ≤ P →
      ∀ R φ : ℝ, 1 ≤ R → 0 < φ → 2*R ≤ P^2 →
      (∀ q ∈ moduli R, Summable (term G D.weight.weight P φ q)) ∧
      error G D.weight.weight P R φ ≤
        truncatedError G D.weight.weight P R φ (P^η*V P R φ) +
          C*φ*P^(-(A : ℝ))*(∑ q ∈ moduli R, (q : ℝ)) := by
  classical
  obtain ⟨C,P₀,hC,hP₀,hmass⟩ := DyadicOscillatoryControl.exists_frequencyMass_bound G hG D η hη A 11
  obtain ⟨K,hK,htail⟩ := CompleteSumFrequencyTail.exists_bound 10 11 (by decide)
  refine ⟨4*K*C,P₀,by nlinarith,hP₀,?_⟩
  intro P hP R φ hR hφ hRP
  have hPpos : 0 < P := zero_lt_one.trans_le (hP₀.trans hP)
  let T := frequencies 10 (P^η*V P R φ)
  have hb (q : ℕ) (hq : q ∈ moduli R) := by
    have hq1 : 1 ≤ q := by
      have hh := (mem_moduli R q).mp hq |>.1
      have hh' : (1:ℝ) ≤ q := hR.trans hh.le
      exact_mod_cast hh'
    have hqP : (q : ℝ) ≤ P^2 := ((mem_moduli R q).mp hq).2.trans hRP
    exact htail G q hq1 T (frequencyMass G D.weight.weight P φ q) (4*φ*C) P A
      (by positivity) hPpos (frequencyMass_nonneg G D.weight.weight P φ q)
      (hmass P hP R φ hR hφ q hq hqP)
  refine ⟨fun q hq => (hb q hq).1,?_⟩
  have hqbound (q : ℕ) (hq : q ∈ moduli R) :
      ((q : ℝ)^10)⁻¹*(∑' v, term G D.weight.weight P φ q v) ≤
        ((q : ℝ)^10)⁻¹*(∑ v ∈ T, ‖completeCubicSum G q v‖*frequencyMass G D.weight.weight P φ q v) +
          (4*K*C)*φ*P^(-(A : ℝ))*(q : ℝ) := by
    have hh := hb q hq
    have hqpos : (0:ℝ) < q := (zero_lt_one.trans_le hR).trans ((mem_moduli R q).mp hq).1
    have hfinite : (∑ v ∈ T, CompleteSumFrequencyTail.term G q (frequencyMass G D.weight.weight P φ q) v)=
        ∑ v ∈ T, ‖completeCubicSum G q v‖*frequencyMass G D.weight.weight P φ q v := by
      apply Finset.sum_congr rfl
      intro v hv
      exact if_neg ((mem_frequencies _ v).mp hv).1
    change ((q : ℝ)^10)⁻¹*(∑' v, CompleteSumFrequencyTail.term G q
      (frequencyMass G D.weight.weight P φ q) v) ≤ _
    rw [hh.2.2.1,hfinite,mul_add]
    apply add_le_add le_rfl
    calc
      _ ≤ ((q : ℝ)^10)⁻¹*(K*(4*φ*C)*P^(-(A : ℝ))*(q : ℝ)^(10+1)) :=
        mul_le_mul_of_nonneg_left hh.2.2.2 (by positivity)
      _ = _ := by field_simp
  calc
    error G D.weight.weight P R φ ≤ ∑ q ∈ moduli R,
        (((q : ℝ)^10)⁻¹*(∑ v ∈ T, ‖completeCubicSum G q v‖*frequencyMass G D.weight.weight P φ q v) +
          (4*K*C)*φ*P^(-(A : ℝ))*(q : ℝ)) := Finset.sum_le_sum hqbound
    _ = _ := by simp only [Finset.sum_add_distrib,← Finset.mul_sum,truncatedError,T]

theorem sum_moduli_le (R X : ℝ) (hX : 0 ≤ X) (hRX : 2*R ≤ X) :
    (∑ q ∈ moduli R, (q : ℝ)) ≤ (X+1)*X := by
  have hsub : moduli R ⊆ Finset.range (⌊X⌋₊+1) := by
    intro q hq
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.le_floor (((mem_moduli R q).mp hq).2.trans hRX)))
  have hc : ((moduli R).card : ℝ) ≤ X+1 := by
    have h := Finset.card_le_card hsub
    rw [Finset.card_range] at h
    have hr : ((moduli R).card : ℝ) ≤ (⌊X⌋₊ : ℝ)+1 := by exact_mod_cast h
    exact hr.trans (add_le_add (Nat.floor_le hX) le_rfl)
  calc
    _ ≤ ∑ _q ∈ moduli R, X := Finset.sum_le_sum fun q hq => ((mem_moduli R q).mp hq).2.trans hRX
    _ = ((moduli R).card : ℝ)*X := by simp [nsmul_eq_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right hc hX

/-- Arbitrarily rapid error after the actual finite cutoff, uniformly over
the source's dyadic blocks. The phi<=1 and 2R<=P² range contains the required
circle-method regime for large P. Summability is part of the conclusion. -/
theorem exists_bound 
    (G : MvPolynomial (Fin 10) ℤ) (hG : G.IsHomogeneous 3)
    (D : Data (map (Int.castRingHom ℝ) G)) (η : ℝ) (hη : 0 < η) (A : ℕ) :
    ∃ C P₀ : ℝ, 1 ≤ C ∧ 1 ≤ P₀ ∧ ∀ P : ℝ, P₀ ≤ P →
      ∀ R φ : ℝ, 1 ≤ R → 0 < φ → φ ≤ 1 → 2*R ≤ P^2 →
      (∀ q ∈ moduli R, Summable (term G D.weight.weight P φ q)) ∧
      error G D.weight.weight P R φ ≤
        truncatedError G D.weight.weight P R φ (P^η*V P R φ) + C*P^(-(A : ℝ)) := by
  obtain ⟨C,P₀,hC,hP₀,hb⟩ := exists_weighted_bound G hG D η hη (A+4)
  refine ⟨2*C,P₀,by linarith,hP₀,?_⟩
  intro P hP R φ hR hφ hφ1 hRP
  obtain ⟨hs,hbound⟩ := hb P hP R φ hR hφ hRP
  refine ⟨hs,hbound.trans ?_⟩
  apply add_le_add le_rfl
  have hP1 : 1 ≤ P := hP₀.trans hP
  have hPpos : 0 < P := zero_lt_one.trans_le hP1
  have hsum : (∑ q ∈ moduli R, (q : ℝ)) ≤ 2*P^4 := by
    apply (sum_moduli_le R (P^2) (sq_nonneg P) hRP).trans
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

end CubicTenVariables.DyadicFrequencyTruncation
