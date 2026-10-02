import CubicTenVariables.StratifiedModuli

/-! Real-power bookkeeping for the large-modulus branch of the stratified
sieve. The three epsilon losses combine into one; tail indices are kept
inside the original finite type by assigning scale 1 to inactive entries. -/
noncomputable section
namespace CubicTenVariables.StratifiedLargeRangeNumerics
open scoped BigOperators

/-- All three bases are bounded by the single source growth parameter. -/
theorem growth_absorb (L P A B U ε : ℝ) (hL : 1 ≤ L) (hP : 1 ≤ P)
    (hU : 0 ≤ U) (hA : 0 < A) (hAP : A ≤ P) (hB : 0 < B)
    (hBP : B ≤ P) (hε : 0 < ε) :
    (L+U)^(ε/3) * (L*A+U)^(ε/3) * B^(ε/3) ≤ (L*P+U)^ε := by
  have hL0 : 0 ≤ L := zero_le_one.trans hL
  have hP0 : 0 ≤ P := zero_le_one.trans hP
  have he : 0 ≤ ε/3 := by positivity
  have h₁ : L+U ≤ L*P+U := by nlinarith
  have h₂ : L*A+U ≤ L*P+U := add_le_add (mul_le_mul_of_nonneg_left hAP hL0) le_rfl
  have h₃ : B ≤ L*P+U := by nlinarith
  have hp₁ := Real.rpow_le_rpow (add_nonneg hL0 hU) h₁ he
  have hp₂ := Real.rpow_le_rpow (add_nonneg (mul_nonneg hL0 hA.le) hU) h₂ he
  have hp₃ := Real.rpow_le_rpow hB.le h₃ he
  calc
    _ ≤ (L*P+U)^(ε/3) * (L*P+U)^(ε/3) * (L*P+U)^(ε/3) :=
      mul_le_mul (mul_le_mul hp₁ hp₂ (by positivity) (by positivity))
        hp₃ (by positivity) (by positivity)
    _ = (L*P+U)^ε := by
      have hpos : 0 < L*P+U := by nlinarith
      rw [← Real.rpow_add hpos, ← Real.rpow_add hpos]
      congr 1
      ring

/-- The exponent gained by the dyadic count cancels the `+1` in the pivot
fiber exponent; inactive tail factors are exactly 1. -/
theorem tail_denominator {s : ℕ} (j : Fin s) (R : Fin s → ℝ) (d : Fin s → ℕ) :
    (∏ i, (StratifiedModuli.tailScales j R i) ^
      (((d j : ℝ)+1)-(d i : ℝ)-1)) =
      ∏ i, if j < i then (R i)^((d j : ℝ)-(d i : ℝ)) else 1 := by
  have hexp (i : Fin s) : ((d j : ℝ)+1)-(d i : ℝ)-1 = (d j : ℝ)-(d i : ℝ) := by ring
  simp only [hexp]
  exact StratifiedModuli.tailScales_rpow_product j R (fun i => (d j : ℝ)-(d i : ℝ))

end CubicTenVariables.StratifiedLargeRangeNumerics
