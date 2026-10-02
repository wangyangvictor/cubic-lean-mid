import CubicTenVariables.NumericalConductor
import CubicTenVariables.MicrolocalConductorDepth
import CubicTenVariables.MicrolocalDepthWeightSum

/-! Actual numerical depths at integer frequencies are dominated by the
proved geometric residue weights. Only the majorant is a residue function:
no residue invariance of the prime-square numerical depth is asserted. -/

set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.NumericalDepthWeightDomination
open MvPolynomial
open scoped BigOperators Classical

variable {t N d : ℕ} {F : MvPolynomial (Fin 10) ℤ}
  {f : Fin t → BihomogeneousIncidenceFamily.Polynomial 10 10}
  {T : ∀ i : Fin 4, MicrolocalPromotionTable.Table F f (i.val+1)}
  {C : ℝ} {h : NumericalPrimeDepth.CoarseBounds F C}

/-- At depth at least two the actual prime weight contributes one of the
five origin-adjoined geometric summands, at that very numerical depth. -/
theorem prime_domination (hc : MicrolocalConductorDepth.Conclusion F f T N C d h)
    (p : ℕ) [Fact p.Prime] (hpN : ¬ p ∣ N) (v : Fin 10 → ℤ)
    (hd : 2 ≤ NumericalConductor.primeDepth h p v) :
    (NumericalConductor.primeWeight h p v)^((3 : ℝ)/2) ≤
      MicrolocalDepthWeightSum.primeWeight f p (fun i => (v i : ZMod p)) := by
  have hmax : NumericalConductor.primeDepth h p v ≤ 6 := by
    simpa using NumericalPrimeDepth.primeDepth_le_six h p v
  let j : Fin 5 := ⟨NumericalConductor.primeDepth h p v-2,by omega⟩
  have he : j.val+2 = NumericalConductor.primeDepth h p v := by dsimp [j]; omega
  have hs : MicrolocalDepthWeightSum.support f p j (fun i => (v i : ZMod p)) := by
    have hg := hc.geometric_support p hpN v (NumericalConductor.primeDepth h p v)
      (by omega) (Or.inl (by simp))
    simpa only [MicrolocalDepthWeightSum.support,he] using hg
  have hw : (NumericalConductor.primeWeight h p v)^((3 : ℝ)/2) =
      (p : ℝ)^(MicrolocalDepthWeightSum.primeExponent j) := by
    rw [NumericalConductor.primeWeight,if_pos hd,← Real.rpow_mul (Nat.cast_nonneg p)]
    dsimp only [MicrolocalDepthWeightSum.primeExponent]
    rw [he]
    congr 1
    ring
  rw [hw]
  have hb := Finset.single_le_sum (s := Finset.univ)
    (f := fun i : Fin 5 => if MicrolocalDepthWeightSum.support f p i
      (fun a => (v a : ZMod p)) then (p : ℝ)^(MicrolocalDepthWeightSum.primeExponent i) else 0)
    (fun i _ => by dsimp only; split_ifs <;> positivity) (Finset.mem_univ j)
  simpa only [if_pos hs] using hb

/-- The square weight remains evaluated at the original integer frequency.
Its dominating summand depends only on the reduction of that frequency. -/
theorem square_domination (hc : MicrolocalConductorDepth.Conclusion F f T N C d h)
    (p : ℕ) [Fact p.Prime] (hpN : ¬ p ∣ N) (v : Fin 10 → ℤ)
    (hd : 2 ≤ NumericalConductor.squareDepth h p v) :
    (NumericalConductor.squareWeight h p v)^((3 : ℝ)/2) ≤
      MicrolocalDepthWeightSum.squareWeight f p (fun i => (v i : ZMod p)) := by
  have hmax : NumericalConductor.squareDepth h p v ≤ 6 := by
    simpa using NumericalPrimeDepth.squareDepth_le_six h p v
  let j : Fin 5 := ⟨NumericalConductor.squareDepth h p v-2,by omega⟩
  have he : j.val+2 = NumericalConductor.squareDepth h p v := by dsimp [j]; omega
  have hs : MicrolocalDepthWeightSum.support f p j (fun i => (v i : ZMod p)) := by
    have hg := hc.geometric_support p hpN v (NumericalConductor.squareDepth h p v)
      (by omega) (Or.inr (by simp))
    simpa only [MicrolocalDepthWeightSum.support,he] using hg
  have hw : (NumericalConductor.squareWeight h p v)^((3 : ℝ)/2) =
      (p : ℝ)^(MicrolocalDepthWeightSum.squareExponent j) := by
    rw [NumericalConductor.squareWeight,if_pos hd,← Real.rpow_mul (Nat.cast_nonneg p)]
    dsimp only [MicrolocalDepthWeightSum.squareExponent]
    rw [he]
    congr 1
    ring
  rw [hw]
  have hb := Finset.single_le_sum (s := Finset.univ)
    (f := fun i : Fin 5 => if MicrolocalDepthWeightSum.support f p i
      (fun a => (v a : ZMod p)) then (p : ℝ)^(MicrolocalDepthWeightSum.squareExponent i) else 0)
    (fun i _ => by dsimp only; split_ifs <;> positivity) (Finset.mem_univ j)
  simpa only [if_pos hs] using hb

/-- A local majorant valid at every actual integer frequency, including
the numerical depths zero and one. -/
theorem prime_domination_all (hc : MicrolocalConductorDepth.Conclusion F f T N C d h)
    (p : ℕ) [Fact p.Prime] (hpN : ¬ p ∣ N) (v : Fin 10 → ℤ) :
    (NumericalConductor.primeWeight h p v)^((3 : ℝ)/2) ≤
      1+MicrolocalDepthWeightSum.primeWeight f p (fun i => (v i : ZMod p)) := by
  by_cases hd : 2 ≤ NumericalConductor.primeDepth h p v
  · exact (prime_domination hc p hpN v hd).trans (le_add_of_nonneg_left zero_le_one)
  · rw [NumericalConductor.primeWeight,if_neg hd,Real.one_rpow]
    have hw : 0 ≤ MicrolocalDepthWeightSum.primeWeight f p (fun i => (v i : ZMod p)) :=
      Finset.sum_nonneg (fun _ _ => by split_ifs <;> positivity)
    linarith

theorem square_domination_all (hc : MicrolocalConductorDepth.Conclusion F f T N C d h)
    (p : ℕ) [Fact p.Prime] (hpN : ¬ p ∣ N) (v : Fin 10 → ℤ) :
    (NumericalConductor.squareWeight h p v)^((3 : ℝ)/2) ≤
      1+MicrolocalDepthWeightSum.squareWeight f p (fun i => (v i : ZMod p)) := by
  by_cases hd : 2 ≤ NumericalConductor.squareDepth h p v
  · exact (square_domination hc p hpN v hd).trans (le_add_of_nonneg_left zero_le_one)
  · rw [NumericalConductor.squareWeight,if_neg hd,Real.one_rpow]
    have hw : 0 ≤ MicrolocalDepthWeightSum.squareWeight f p (fun i => (v i : ZMod p)) :=
      Finset.sum_nonneg (fun _ _ => by split_ifs <;> positivity)
    linarith

end CubicTenVariables.NumericalDepthWeightDomination
