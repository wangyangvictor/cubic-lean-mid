import CubicTenVariables.PlanAlphaBenchmarkReduced
import CubicTenVariables.PlanAlphaBoxExtension
import CubicTenVariables.LocalizedShiftedWindow
import CubicTenVariables.MicrolocalConductorDepthReduced

/-! The actual shifted-average endpoint. The Smith loss and prime cutoff
are selected before localization and before the arbitrary epsilon loss. -/
set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.PlanAlphaCleanShiftedReduced
open MvPolynomial HessianTheorem11 NumericalPrimeDepth
open LocalizedShiftedWindow PrimeLocalizationSeries
open scoped BigOperators

variable {t N Betti : ℕ} {F : MvPolynomial (Fin 10) ℤ}
  {f : Fin t → BihomogeneousIncidenceFamily.Polynomial 10 10}
  {tables : ∀ k : Fin 4, MicrolocalPromotionTable.Table F f (k.val+1)}
  {C₀ : ℝ} {d₀ : ℕ} {h : CoarseBounds F C₀}

/-- For every permitted saving, a fixed prime cutoff suffices for the
literal localized shifted sum, uniformly for every positive epsilon.
All majorants, mass bounds, block sums and box coverings are proved. -/
theorem of_data
    (integrality : CubicPrincipalOpenUniform.Uniform)
    (cubicWeil : Literature.SmoothCubicWeil)
    (isolated : CubicSurfacePointCountReduced.IsolatedConjugateCubicSurfacePointCount)
    (pointcount : FixedFamilyPrimeFieldPointCount.Uniform)
    (hP : MicrolocalRationalPartition.Conclusion F f N Betti tables)
    (hhom : F.IsHomogeneous 3) (hAn : Anisotropic (map (Int.castRingHom ℚ) F))
    (hc : MicrolocalConductorDepth.Conclusion F f tables N C₀ d₀ h)
    
    (γ : ℝ) (hγ : 0 < γ) (hγmax : γ < (1 : ℝ)/96) :
    ∃ p₀ : ℕ, 3 ≤ p₀ ∧ ∀ (s : Finset ℕ) (hprimes : ∀ p ∈ s, p.Prime)
      (Dlocal : ∀ (p : ℕ) (hp : p ∈ s), @PrimeLocalizationData p ⟨hprimes p hp⟩ F),
      N.primeFactors ⊆ s → (∀ p : ℕ, p.Prime → p < p₀ → p ∈ s) →
      CleanShiftedAverage F (modulus s hprimes Dlocal)
        (restriction s hprimes Dlocal) ((20 : ℝ)/3-γ) := by
  classical
  let η := ((1 : ℝ)/96-γ)/2
  have hη : 0 < η := by dsimp [η]; linarith
  have hηle : η ≤ (1 : ℝ)/96-γ := by dsimp [η]; linarith
  obtain ⟨p₀,hp₀,hbase⟩ := PlanAlphaBenchmarkReduced.of_data
    integrality cubicWeil isolated pointcount hP hhom hAn hc  η hη
  refine ⟨p₀,hp₀,?_⟩
  intro s hprimes Dlocal hsN hsmall ε hε
  have ht : 0 < ε/8 := by positivity
  obtain ⟨K,hK,hbound⟩ := hbase s hprimes Dlocal hsN hsmall (ε/8) ht
  refine ⟨K*7^10*3^(ε/2),one_le_mul_of_one_le_of_one_le
    (one_le_mul_of_one_le_of_one_le hK (by norm_num))
    (Real.one_le_rpow (by norm_num) (by positivity)),?_⟩
  intro B Q hB hQ L hL v hu
  let W := modulus s hprimes Dlocal
  let Ω := restriction s hprimes Dlocal
  let a := fun x : Fin 10 → ℤ => ∑ q ∈ DyadicFrequencyError.moduli Q,
    ‖localizedCompleteCubicSum F q W Ω x‖
  have hQ0 : 0 < Q := zero_lt_one.trans_le hQ
  have hU : ∀ q ∈ DyadicFrequencyError.moduli Q,
      0 < q ∧ Q ≤ (q : ℝ) ∧ (q : ℝ) ≤ 2*Q := by
    intro q hq
    have hh := (DyadicFrequencyError.mem_moduli Q q).mp hq
    exact ⟨by exact_mod_cast hQ0.trans hh.1,hh.1.le,hh.2⟩
  have hbench : ∀ (u : Fin 10 → ℝ) (B' : ℝ), 1 ≤ B' → ‖u‖ ≤ B' →
      ∀ V : Finset (Fin 10 → ℤ),
      (∀ x ∈ V, x ≠ 0 ∧ ∀ i, |(x i : ℝ)-u i| ≤ Q^((1 : ℝ)/3)) →
      (∑ x ∈ V, a x) ≤ K*(B'*Q)^(ε/2)*Q^(((20 : ℝ)/3-γ)+(10 : ℝ)/3) := by
    intro u B' hB' hu' V hV
    have hb := hbound Q B' hQ hB' u hu' V hV (DyadicFrequencyError.moduli Q) hU
    have hB'0 : 0 < B' := zero_lt_one.trans_le hB'
    have hprod : 0 < B'*Q := mul_pos hB'0 hQ0
    have hQprod : Q ≤ B'*Q := by
      simpa using mul_le_mul_of_nonneg_right hB' hQ0.le
    have hqpow : Q^(2*(ε/8)) ≤ (B'*Q)^(2*(ε/8)) :=
      Real.rpow_le_rpow hQ0.le hQprod (by positivity)
    have hexp : Q^((10 : ℝ)-1/96+η) ≤ Q^(10-γ) :=
      Real.rpow_le_rpow_of_exponent_le hQ (by linarith)
    have hid : (B'*Q)^(2*(ε/8))*(B'*Q)^(2*(ε/8)) = (B'*Q)^(ε/2) := by
      rw [← Real.rpow_add hprod]
      congr 1
      ring
    calc
      _ = ∑ q ∈ DyadicFrequencyError.moduli Q,
          ∑ x ∈ V, ‖localizedCompleteCubicSum F q W Ω x‖ := by
        dsimp [a]
        rw [Finset.sum_comm]
      _ ≤ K*(B'*Q)^(2*(ε/8))*Q^((10 : ℝ)-1/96+η+2*(ε/8)) := hb
      _ = K*(B'*Q)^(2*(ε/8))*(Q^((10 : ℝ)-1/96+η)*Q^(2*(ε/8))) := by
        rw [Real.rpow_add hQ0]
      _ ≤ K*(B'*Q)^(2*(ε/8))*(Q^(10-γ)*(B'*Q)^(2*(ε/8))) := by
        apply mul_le_mul_of_nonneg_left
          (mul_le_mul hexp hqpow (Real.rpow_nonneg hQ0.le _)
            (Real.rpow_nonneg hQ0.le _))
          (mul_nonneg (zero_le_one.trans hK) (Real.rpow_nonneg hprod.le _))
      _ = K*((B'*Q)^(2*(ε/8))*(B'*Q)^(2*(ε/8)))*Q^(10-γ) := by ring
      _ = _ := by rw [hid]; congr 2 <;> ring
  have hh := PlanAlphaBoxExtension.of_benchmark a Q ((20 : ℝ)/3-γ)
    (ε/2) K hQ (by positivity) (zero_le_one.trans hK) hbench
    (fun i => (v i : ℝ)) B (L : ℝ) hB (by exact_mod_cast hL) hu
    (ShiftedCompleteSumWindow.shiftedWindow L v)
    (fun x hx => (ShiftedCompleteSumWindow.mem_shiftedWindow L v x).mp hx)
  have hsum : shiftedSum F W Ω Q L v =
      ∑ x ∈ ShiftedCompleteSumWindow.shiftedWindow L v, a x := by
    dsimp [shiftedSum,a]
    rw [Finset.sum_comm]
  rw [hsum]
  convert hh using 1 <;> congr 3 <;> ring

/-- Construct the microlocal data from the listed geometric hypotheses and
proved prime-field count interface. The only supplied application data are
local p-adic data at the chosen finite set; their construction is separate. -/
theorem from_literature
    (microlocal : Literature.ProjectiveMicrolocalCertificate)
    (degreeSpan : TranslatedDepthSeven.StandardAG.ProjectiveDegreeSpanInequality ℚ)
    (smooth : Literature.SmoothInfinityGeometricIntegrality)
    (spread : CubicGenericIntegralityUniform.Uniform)
    (weil : Literature.AffinePlaneCubicWeil)
    (dichotomy : Literature.ProperHyperplaneWeightDichotomy)
    (salberger : TranslatedDepthSeven.Published.Salberger2023Theorem04)
    (integrality : CubicPrincipalOpenUniform.Uniform)
    (cubicWeil : Literature.SmoothCubicWeil)
    (isolated : CubicSurfacePointCountReduced.IsolatedConjugateCubicSurfacePointCount)
    (pointcount : FixedFamilyPrimeFieldPointCount.Uniform)
    
    (F : MvPolynomial (Fin 10) ℤ) (hhom : F.IsHomogeneous 3)
    (hAn : Anisotropic (map (Int.castRingHom ℚ) F))
    (γ : ℝ) (hγ : 0 < γ) (hγmax : γ < (1 : ℝ)/96) :
    ∃ N : ℕ, 1 ≤ N ∧ ∃ p₀ : ℕ, 3 ≤ p₀ ∧
      ∀ (s : Finset ℕ) (hprimes : ∀ p ∈ s, p.Prime)
        (Dlocal : ∀ (p : ℕ) (hp : p ∈ s), @PrimeLocalizationData p ⟨hprimes p hp⟩ F),
        N.primeFactors ⊆ s → (∀ p : ℕ, p.Prime → p < p₀ → p ∈ s) →
        CleanShiftedAverage F (modulus s hprimes Dlocal)
          (restriction s hprimes Dlocal) ((20 : ℝ)/3-γ) := by
  obtain ⟨t,f,N,B,tables,hP,hQ,C,d₀,h,hc⟩ := MicrolocalConductorDepthReduced.exists_data
    microlocal degreeSpan smooth spread weil dichotomy salberger
    integrality cubicWeil isolated pointcount F hhom hAn
  exact ⟨N,hP.modulus_pos,of_data integrality cubicWeil isolated pointcount hP hhom hAn hc
     γ hγ hγmax⟩

end CubicTenVariables.PlanAlphaCleanShiftedReduced
