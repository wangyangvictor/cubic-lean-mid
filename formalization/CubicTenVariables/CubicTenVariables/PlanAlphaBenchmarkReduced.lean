import CubicTenVariables.PlanAlphaArithmeticBlockReduced
import CubicTenVariables.PlanAlphaFactorEligibility
import CubicTenVariables.PlanAlphaBlockReindex

/-! The actual localized modulus-frequency benchmark sum. Every positive
modulus is split canonically, its block conditions are proved, the finite
samples are reindexed exactly, and the occupied blocks are counted.
The assembly uses the supplied microlocal and localization data, the proved
prime-field count interface and the proved Smith/root estimates; no majorant or arithmetic
bound is assumed. -/
set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
namespace CubicTenVariables.PlanAlphaBenchmarkReduced
open MvPolynomial HessianTheorem11 NumericalPrimeDepth
open PlanAlphaModulusDecomposition PlanAlphaBlockIndices PlanAlphaBlockReindex
open CubeFullSmithParameters (CubeFull)
open ComplementCubeFreePiece (Sample)
open scoped BigOperators Classical

private theorem factor_windows (s : Finset ℕ) (q : ℕ) (b : ℕ × ℕ × ℕ)
    (hb : blockIndex s q = b) :
    d s q ∈ CubeFreeNonzeroAverage.window ((2 : ℝ)^b.2.1) ∧
      (2 : ℝ)^b.2.2 ≤ (r s q : ℝ) ∧ (r s q : ℝ) < 2*(2 : ℝ)^b.2.2 := by
  have hd := ComplementDyadicScales.canonical_scale_bounds (d s q) (d_pos s q)
  have hr := ComplementDyadicScales.canonical_scale_bounds (r s q) (r_pos s q)
  have hdi : Nat.log 2 (d s q) = b.2.1 := by
    simpa only [blockIndex,Nat.log2_eq_log_two] using congrArg (fun x => x.2.1) hb
  have hri : Nat.log 2 (r s q) = b.2.2 := by
    simpa only [blockIndex,Nat.log2_eq_log_two] using congrArg (fun x => x.2.2) hb
  rw [hdi] at hd
  rw [hri] at hr
  exact ⟨(CubeFreeNonzeroAverage.mem_window _ _).mpr ⟨d_cubeFree s q,hd.2⟩,hr.2⟩

variable {t N Betti : ℕ} {F : MvPolynomial (Fin 10) ℤ}
  {f : Fin t → BihomogeneousIncidenceFamily.Polynomial 10 10}
  {tables : ∀ k : Fin 4, MicrolocalPromotionTable.Table F f (k.val+1)}
  {C₀ : ℝ} {d₀ : ℕ} {h : CoarseBounds F C₀}

/-- The cutoff is fixed before the localization data and epsilon; the
bound constant is fixed before the scale, center and both finite sets.
The additional epsilon in the Q exponent is exactly the block-count loss. -/
theorem of_data
    (integrality : CubicPrincipalOpenUniform.Uniform)
    (cubicWeil : Literature.SmoothCubicWeil)
    (isolated : CubicSurfacePointCountReduced.IsolatedConjugateCubicSurfacePointCount)
    (pointcount : FixedFamilyPrimeFieldPointCount.Uniform)
    (hP : MicrolocalRationalPartition.Conclusion F f N Betti tables)
    (hhom : F.IsHomogeneous 3) (hAn : Anisotropic (map (Int.castRingHom ℚ) F))
    (hc : MicrolocalConductorDepth.Conclusion F f tables N C₀ d₀ h)
     (η : ℝ) (hη : 0 < η) :
    ∃ p₀ : ℕ, 3 ≤ p₀ ∧ ∀ (s : Finset ℕ) (hprimes : ∀ p ∈ s, p.Prime)
      (Dlocal : ∀ (p : ℕ) (hp : p ∈ s), @PrimeLocalizationData p ⟨hprimes p hp⟩ F),
      N.primeFactors ⊆ s → (∀ p : ℕ, p.Prime → p < p₀ → p ∈ s) →
      ∀ ε : ℝ, 0 < ε → ∃ K : ℝ, 1 ≤ K ∧
      ∀ Q B : ℝ, 1 ≤ Q → 1 ≤ B → ∀ u : Fin 10 → ℝ, ‖u‖ ≤ B →
      ∀ V : Finset (Fin 10 → ℤ),
      (∀ v ∈ V, v ≠ 0 ∧ ∀ k, |(v k : ℝ)-u k| ≤ Q^((1 : ℝ)/3)) →
      ∀ U : Finset ℕ, (∀ q ∈ U, 0 < q ∧ Q ≤ (q : ℝ) ∧ (q : ℝ) ≤ 2*Q) →
      (∑ q ∈ U, ∑ v ∈ V, ‖localizedCompleteCubicSum F q
        (PrimeLocalizationSeries.modulus s hprimes Dlocal)
        (PrimeLocalizationSeries.restriction s hprimes Dlocal) v‖) ≤
          K*(B*Q)^(2*ε)*Q^((10 : ℝ)-1/96+η+2*ε) := by
  obtain ⟨p₀,hp₀,hblock⟩ := PlanAlphaArithmeticBlockReduced.of_data
    integrality cubicWeil isolated pointcount hP hhom hAn hc  η hη
  refine ⟨p₀,hp₀,?_⟩
  intro s hprimes Dlocal hsN hsmall ε hε
  obtain ⟨Ka,hKa,ha⟩ := hblock s hprimes Dlocal ε hε
  obtain ⟨Kb,hKb,hcount⟩ := PlanAlphaBlockIndices.exists_count_bound s hprimes ε hε
  refine ⟨Ka*Kb,one_le_mul_of_one_le_of_one_le hKa hKb,?_⟩
  intro Q B hQ hB u hu V hV U hU
  let W := PrimeLocalizationSeries.modulus s hprimes Dlocal
  let Ω := PrimeLocalizationSeries.restriction s hprimes Dlocal
  let Z : Finset Sample := U ×ˢ V
  let I : Finset (ℕ × ℕ × ℕ) := Z.image (fun x => blockIndex s x.1)
  let bound : ℝ := Ka*(B*Q)^(2*ε)*Q^((10 : ℝ)-1/96+η+ε)
  have hZ (x : Sample) (hx : x ∈ Z) : x.1 ∈ U ∧ x.2 ∈ V := Finset.mem_product.mp hx
  have hZpos (x : Sample) (hx : x ∈ Z) : 0 < x.1 := (hU x.1 (hZ x hx).1).1
  have hI : I ⊆ U.image (blockIndex s) := by
    intro b hb
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hb
    exact Finset.mem_image_of_mem (blockIndex s) (hZ x hx).1
  have hcard : (I.card : ℝ) ≤ Kb*Q^ε := by
    have hh : (I.card : ℝ) ≤ ((U.image (blockIndex s)).card : ℝ) :=
      by exact_mod_cast Finset.card_le_card hI
    exact hh.trans (hcount Q hQ U (fun q hq => ⟨(hU q hq).1,(hU q hq).2.2⟩))
  have hblock_bound (b : ℕ × ℕ × ℕ) (hb : b ∈ I) :
      (∑ c ∈ factors s Z b, ∑ y ∈ samples s Z b c,
        ‖localizedCompleteCubicSum F (b.1*y.1*c) W Ω y.2‖) ≤ bound := by
    obtain ⟨x,hx,hxb⟩ := Finset.mem_image.mp hb
    have hxq := hU x.1 (hZ x hx).1
    have hxg : g s x.1 = b.1 := congrArg Prod.fst hxb
    have hbg : 0 < b.1 := by rw [←hxg]; exact g_pos s x.1
    have hbgs : b.1.primeFactors ⊆ s := by rw [←hxg]; exact g_supported s x.1
    have hsc := PlanAlphaBlockIndices.dyadic_bounds s x.1 Q hxq.1 hQ hxq.2.1 hxq.2.2
    change 1 ≤ (2 : ℝ)^(blockIndex s x.1).2.1 ∧
      1 ≤ (2 : ℝ)^(blockIndex s x.1).2.2 ∧
      (g s x.1 : ℝ)*(2 : ℝ)^(blockIndex s x.1).2.1*(2 : ℝ)^(blockIndex s x.1).2.2 ≤ 2*Q ∧
      Q ≤ 8*(g s x.1 : ℝ)*(2 : ℝ)^(blockIndex s x.1).2.1*(2 : ℝ)^(blockIndex s x.1).2.2 ∧ _ at hsc
    rw [hxb,hxg] at hsc
    have hR : ∀ c ∈ factors s Z b, 0 < c ∧ CubeFull c ∧
        (2 : ℝ)^b.2.2 ≤ (c : ℝ) ∧ (c : ℝ) ≤ 2*(2 : ℝ)^b.2.2 ∧
        ∀ p ∈ c.primeFactors, p₀ ≤ p := by
      intro c hc
      obtain ⟨z,hz,hzb,hzc⟩ := (mem_factors_iff s Z b c).mp hc
      have hw := factor_windows s z.1 b hzb
      rw [hzc] at hw
      refine ⟨?_,?_,hw.2.1,hw.2.2.le,?_⟩
      · rw [←hzc]; exact r_pos s z.1
      · rw [←hzc]; exact r_cubeFull s z.1
      · rw [←hzc]; exact PlanAlphaFactorEligibility.r_prime_cutoff s z.1 p₀ hsmall
    have hcop (c : factors s Z b) : (b.1*W).Coprime c.val := by
      obtain ⟨z,hz,hzb,hzc⟩ := (mem_factors_iff s Z b c.val).mp c.property
      have hzg : g s z.1 = b.1 := congrArg Prod.fst hzb
      have hh := PlanAlphaFactorEligibility.gW_coprime_r s hprimes Dlocal z.1
      simpa only [hzg,hzc] using hh
    have hsamples (c : factors s Z b) (y : Sample) (hy : y ∈ samples s Z b c.val) :
        y.1 ∈ CubeFreeNonzeroAverage.window ((2 : ℝ)^b.2.1) ∧ y.2 ∈ V ∧
        ((b.1*c.val)*W).Coprime y.1 ∧ y.1.Coprime N := by
      obtain ⟨z,hz,hzb,hzc,hzd,hzv⟩ := (mem_samples_iff s Z b c.val y).mp hy
      have hzg : g s z.1 = b.1 := congrArg Prod.fst hzb
      have hw := (factor_windows s z.1 b hzb).1
      rw [hzd] at hw
      refine ⟨hw,by rw [←hzv]; exact (hZ z hz).2,?_,?_⟩
      · have hh := PlanAlphaFactorEligibility.grW_coprime_d s hprimes Dlocal z.1
        simpa only [hzg,hzc,hzd] using hh
      · rw [←hzd]
        exact PlanAlphaFactorEligibility.d_coprime_supported s z.1 N hP.modulus_pos hsN
    have hh := ha b.1 hbg hbgs Q ((2 : ℝ)^b.2.1) ((2 : ℝ)^b.2.2)
      hQ hsc.1 hsc.2.1 hsc.2.2.1 hsc.2.2.2.1 u B hB hu V hV
      (factors s Z b) hR hcop (fun c => samples s Z b c.val) hsamples
    change (∑ c : factors s Z b, ∑ y ∈ samples s Z b c.val,
      ‖localizedCompleteCubicSum F (b.1*y.1*c.val) W Ω y.2‖) ≤ bound at hh
    rwa [Finset.sum_coe_sort (factors s Z b)
      (fun c : ℕ => ∑ y ∈ samples s Z b c, ‖localizedCompleteCubicSum F (b.1*y.1*c) W Ω y.2‖)] at hh
  have hbound0 : 0 ≤ bound := by dsimp [bound]; positivity
  calc
    _ = ∑ x ∈ Z, ‖localizedCompleteCubicSum F x.1 W Ω x.2‖ := by
      change _ = ∑ x ∈ U ×ˢ V, ‖localizedCompleteCubicSum F x.1 W Ω x.2‖
      rw [Finset.sum_product]
    _ = ∑ b ∈ I, ∑ c ∈ factors s Z b, ∑ y ∈ samples s Z b c,
        ‖localizedCompleteCubicSum F (b.1*y.1*c) W Ω y.2‖ :=
      sum_eq_blocks s Z hZpos (fun q v => ‖localizedCompleteCubicSum F q W Ω v‖)
    _ ≤ ∑ _b ∈ I, bound := Finset.sum_le_sum hblock_bound
    _ = (I.card : ℝ)*bound := by simp
    _ ≤ (Kb*Q^ε)*bound := mul_le_mul_of_nonneg_right hcard hbound0
    _ = (Ka*Kb)*(B*Q)^(2*ε)*Q^((10 : ℝ)-1/96+η+2*ε) := by
      have hpow : Q^ε*Q^((10 : ℝ)-1/96+η+ε) = Q^((10 : ℝ)-1/96+η+2*ε) := by
        rw [←Real.rpow_add (zero_lt_one.trans_le hQ)]
        congr 1
        ring
      dsimp [bound]
      calc
        _ = (Ka*Kb)*(B*Q)^(2*ε)*(Q^ε*Q^((10 : ℝ)-1/96+η+ε)) := by ring
        _ = _ := by rw [hpow]

end CubicTenVariables.PlanAlphaBenchmarkReduced
