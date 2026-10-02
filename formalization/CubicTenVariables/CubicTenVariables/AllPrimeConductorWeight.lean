import CubicTenVariables.NumericalDepthWeightDomination

/-! Residue majorants at every prime. Excluded primes use the explicit
constant weights p^3 and p^6, as permitted by the actual depth bound six.
Their full residue sums are absorbed using p ≤ D for p dividing the fixed
positive exceptional integer D. Numerical depths remain integer-frequency
quantities throughout. -/

set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.AllPrimeConductorWeight
open MvPolynomial HessianTheorem11 ProjectiveMicrolocalData
open scoped BigOperators Classical

def primeResidueWeight {t : ℕ}
    (f : Fin t → BihomogeneousIncidenceFamily.Polynomial 10 10)
    (D p : ℕ) [Fact p.Prime] (v : Fin 10 → ZMod p) : ℝ :=
  if p ∣ D then (p : ℝ)^3 else MicrolocalDepthWeightSum.primeWeight f p v

def squareResidueWeight {t : ℕ}
    (f : Fin t → BihomogeneousIncidenceFamily.Polynomial 10 10)
    (D p : ℕ) [Fact p.Prime] (v : Fin 10 → ZMod p) : ℝ :=
  if p ∣ D then (p : ℝ)^6 else MicrolocalDepthWeightSum.squareWeight f p v

variable {t N d : ℕ} {F : MvPolynomial (Fin 10) ℤ}
  {f : Fin t → BihomogeneousIncidenceFamily.Polynomial 10 10}
  {T : ∀ i : Fin 4, MicrolocalPromotionTable.Table F f (i.val+1)}
  {C : ℝ} {h : NumericalPrimeDepth.CoarseBounds F C}

private theorem prime_weight_le (p : ℕ) [hp : Fact p.Prime] (v : Fin 10 → ℤ)
    (hd : 2 ≤ NumericalConductor.primeDepth h p v) :
    (NumericalConductor.primeWeight h p v)^((3 : ℝ)/2) ≤ (p : ℝ)^3 := by
  have hmax : NumericalConductor.primeDepth h p v ≤ 6 := by
    simpa using NumericalPrimeDepth.primeDepth_le_six h p v
  have hmaxR : (NumericalConductor.primeDepth h p v : ℝ) ≤ 6 := by exact_mod_cast hmax
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.out.one_lt.le
  rw [NumericalConductor.primeWeight,if_pos hd,← Real.rpow_mul (Nat.cast_nonneg p),
    ← Real.rpow_natCast]
  apply Real.rpow_le_rpow_of_exponent_le hp1
  push_cast
  linarith

private theorem square_weight_le (p : ℕ) [hp : Fact p.Prime] (v : Fin 10 → ℤ)
    (hd : 2 ≤ NumericalConductor.squareDepth h p v) :
    (NumericalConductor.squareWeight h p v)^((3 : ℝ)/2) ≤ (p : ℝ)^6 := by
  have hmax : NumericalConductor.squareDepth h p v ≤ 6 := by
    simpa using NumericalPrimeDepth.squareDepth_le_six h p v
  have hmaxR : (NumericalConductor.squareDepth h p v : ℝ) ≤ 6 := by exact_mod_cast hmax
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.out.one_lt.le
  rw [NumericalConductor.squareWeight,if_pos hd,← Real.rpow_mul (Nat.cast_nonneg p),
    ← Real.rpow_natCast]
  apply Real.rpow_le_rpow_of_exponent_le hp1
  push_cast
  linarith

/-- The all-prime residue majorant bounds the actual integer-frequency
prime weight at every active numerical depth. -/
theorem prime_domination (hc : MicrolocalConductorDepth.Conclusion F f T N C d h)
    (D : ℕ) (hND : N ∣ D) (p : ℕ) [Fact p.Prime] (v : Fin 10 → ℤ)
    (hd : 2 ≤ NumericalConductor.primeDepth h p v) :
    (NumericalConductor.primeWeight h p v)^((3 : ℝ)/2) ≤
      primeResidueWeight f D p (fun i => (v i : ZMod p)) := by
  unfold primeResidueWeight
  split_ifs with hpD
  · exact prime_weight_le p v hd
  · exact NumericalDepthWeightDomination.prime_domination hc p
      (fun hpN => hpD (hpN.trans hND)) v hd

/-- No periodicity of the square numerical depth is required. -/
theorem square_domination (hc : MicrolocalConductorDepth.Conclusion F f T N C d h)
    (D : ℕ) (hND : N ∣ D) (p : ℕ) [Fact p.Prime] (v : Fin 10 → ℤ)
    (hd : 2 ≤ NumericalConductor.squareDepth h p v) :
    (NumericalConductor.squareWeight h p v)^((3 : ℝ)/2) ≤
      squareResidueWeight f D p (fun i => (v i : ZMod p)) := by
  unfold squareResidueWeight
  split_ifs with hpD
  · exact square_weight_le p v hd
  · exact NumericalDepthWeightDomination.square_domination hc p
      (fun hpN => hpD (hpN.trans hND)) v hd

/-- One exceptional integer and one common constant precede every prime,
every residue vector, and every actual integer frequency. Both residue-sum
estimates are unconditional in the prime after these choices. -/
theorem exists_bound (lit : FixedFamilyPrimeFieldPointCount.Uniform)
    {B : ℕ} (hgeo : Geometry F f) (hhom : F.IsHomogeneous 3)
    (hAn : Anisotropic (map (Int.castRingHom ℚ) F))
    (hData : TenMicrolocalIncidence.Conclusion F f N B) (hN : 1 ≤ N)
    (hc : MicrolocalConductorDepth.Conclusion F f T N C d h) :
    ∃ (D : ℕ) (A : ℝ), 1 ≤ D ∧ N ∣ D ∧ 1 ≤ A ∧
      ∀ (p : ℕ) [Fact p.Prime],
        (∑ v : Fin 10 → ZMod p, primeResidueWeight f D p v) ≤ A*(p : ℝ)^8 ∧
        (∑ v : Fin 10 → ZMod p, squareResidueWeight f D p v) ≤ A*(p : ℝ)^9 ∧
        (∀ v : Fin 10 → ℤ, 2 ≤ NumericalConductor.primeDepth h p v →
          (NumericalConductor.primeWeight h p v)^((3 : ℝ)/2) ≤
            primeResidueWeight f D p (fun i => (v i : ZMod p))) ∧
        (∀ v : Fin 10 → ℤ, 2 ≤ NumericalConductor.squareDepth h p v →
          (NumericalConductor.squareWeight h p v)^((3 : ℝ)/2) ≤
            squareResidueWeight f D p (fun i => (v i : ZMod p))) := by
  obtain ⟨D,A₀,hD,hND,hA₀,hgood⟩ :=
    MicrolocalDepthWeightSum.exists_uniform_bound lit hgeo hhom hAn hData hN
  let A : ℝ := A₀+(D : ℝ)^5+(D : ℝ)^7
  have hDA : 0 ≤ (D : ℝ) := Nat.cast_nonneg D
  have hA : 1 ≤ A := by dsimp [A]; linarith [pow_nonneg hDA 5,pow_nonneg hDA 7]
  have hA₀A : A₀ ≤ A := by dsimp [A]; linarith [pow_nonneg hDA 5,pow_nonneg hDA 7]
  have hD5A : (D : ℝ)^5 ≤ A := by dsimp [A]; linarith [pow_nonneg hDA 7]
  have hD7A : (D : ℝ)^7 ≤ A := by dsimp [A]; linarith [pow_nonneg hDA 5]
  refine ⟨D,A,hD,hND,hA,?_⟩
  intro p hp
  have hdomp := prime_domination hc D hND p
  have hdoms := square_domination hc D hND p
  refine ⟨?_,?_,hdomp,hdoms⟩
  · by_cases hpD : p ∣ D
    · have hpD' : (p : ℝ) ≤ D := by exact_mod_cast Nat.le_of_dvd hD hpD
      have hcard : (Fintype.card (Fin 10 → ZMod p) : ℝ) = (p : ℝ)^10 := by
        simp
      calc
        _ = (p : ℝ)^10*(p : ℝ)^3 := by
          simp only [primeResidueWeight,if_pos hpD,Finset.sum_const,nsmul_eq_mul,
            Finset.card_univ,hcard]
        _ = (p : ℝ)^5*(p : ℝ)^8 := by ring
        _ ≤ (D : ℝ)^5*(p : ℝ)^8 :=
          mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (Nat.cast_nonneg p) hpD' 5)
            (by positivity)
        _ ≤ _ := mul_le_mul_of_nonneg_right hD5A (by positivity)
    · simpa only [primeResidueWeight,if_neg hpD] using
        ((hgood p hpD).1.trans (mul_le_mul_of_nonneg_right hA₀A (by positivity)))
  · by_cases hpD : p ∣ D
    · have hpD' : (p : ℝ) ≤ D := by exact_mod_cast Nat.le_of_dvd hD hpD
      have hcard : (Fintype.card (Fin 10 → ZMod p) : ℝ) = (p : ℝ)^10 := by
        simp
      calc
        _ = (p : ℝ)^10*(p : ℝ)^6 := by
          simp only [squareResidueWeight,if_pos hpD,Finset.sum_const,nsmul_eq_mul,
            Finset.card_univ,hcard]
        _ = (p : ℝ)^7*(p : ℝ)^9 := by ring
        _ ≤ (D : ℝ)^7*(p : ℝ)^9 :=
          mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (Nat.cast_nonneg p) hpD' 7)
            (by positivity)
        _ ≤ _ := mul_le_mul_of_nonneg_right hD7A (by positivity)
    · simpa only [squareResidueWeight,if_neg hpD] using
        ((hgood p hpD).2.trans (mul_le_mul_of_nonneg_right hA₀A (by positivity)))

end CubicTenVariables.AllPrimeConductorWeight
