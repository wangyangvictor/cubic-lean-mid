import TranslatedDepthSeven.FixedSurfacePacketPrimeRangeAuxiliary
import TranslatedDepthSeven.SurfaceMixedDegreeChoice

/-!
# A quantitative fixed-surface auxiliary from the actual prime range

This file combines the exact packet-plus-mixed determinant theorem with the
height-dependent degree choice.  The block degree and the prime cutoff are
chosen internally and are equal.  The resulting auxiliary degree has the
required dependence on the packet modulus.
-/

namespace TranslatedDepthSeven
noncomputable section
open MvPolynomial Published
open scoped BigOperators
attribute [local instance] MvPolynomial.gradedAlgebra

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000

private theorem packet_modulus_le_height
    {H q m Dex Aex : ℕ} (hDex : 0 < Dex) (hheight : Dex ≤ H ^ Aex)
    (hmq : m * q ∣ Dex) (hm : m ≠ 0) : q ≤ H ^ Aex := by
  have hmpos : 0 < m := Nat.pos_of_ne_zero hm
  have hmqle : m * q ≤ Dex := Nat.le_of_dvd hDex hmq
  have hqle : q ≤ m * q := by
    nlinarith [Nat.one_le_iff_ne_zero.mpr hm]
  exact hqle.trans (hmqle.trans hheight)

private theorem layer_weight_pos_of_block
    {d k t s : ℕ} (hd : 0 < d) (hk : 0 < k)
    (hcount : d * affinePlaneMonomialCount k =
      affinePlaneMonomialCount t + s) :
    0 < affinePlaneMonomialWeight t + (t + 1) * s := by
  have hkcount : 2 ≤ affinePlaneMonomialCount k := by
    have hc := two_mul_affinePlaneMonomialCount k
    nlinarith
  have hn : 2 ≤ d * affinePlaneMonomialCount k := by
    calc
      2 = 1 * 2 := by omega
      _ ≤ d * affinePlaneMonomialCount k :=
        Nat.mul_le_mul (Nat.one_le_iff_ne_zero.mpr hd.ne') hkcount
  by_cases ht : t = 0
  · subst t
    rw [hcount] at hn
    simp [affinePlaneMonomialCount] at hn
    simp [affinePlaneMonomialWeight]
    omega
  · have htpos : 0 < t := Nat.pos_of_ne_zero ht
    have hw := three_mul_affinePlaneMonomialWeight t
    have hrhs : 0 < t * (t + 1) * (t + 2) := by positivity
    have hweight : 0 < affinePlaneMonomialWeight t := by omega
    omega

/-- The fixed-surface packet theorem with both the mixed-prime cutoff and
the auxiliary degree selected internally.  The exceptional-height exponent
is fixed before the final height threshold.  Point counts are requested only
at primes outside the displayed exceptional integer `Dex`.

The degree bound is the literal determinant-method scale
`2 * H^η * (1 + B^a/q)`.  The exponent `a` may be chosen arbitrarily close
to `sqrt K / sqrt d`; thus a leading-one surface estimate permits the usual
`1 / sqrt d + σ` exponent. -/
theorem exists_fixedSurface_quantitative_auxiliaryFamily_of_packetPrimeRange
    {d : ℕ} (hd : 0 < d)
    (I : Ideal (MvPolynomial (Fin 4) ℚ))
    (hprime : I.IsPrime)
    (hhom : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule _ ℚ))
    (hX : MvPolynomial.X 0 ∉ I)
    (hdegree : HasProjectiveDimensionDegree I 2 d)
    (F : MvPolynomial (Fin 4) ℤ)
    (K : ℝ) (hK : 1 ≤ K) (Aex : ℕ)
    (η a : ℝ) (hη : 0 < η)
    (ha : Real.sqrt K / Real.sqrt (d : ℝ) < a) :
    ∃ b D A H₀ : ℕ, ∃ C : ℝ,
      1 ≤ D ∧ 2 ≤ A ∧ 2 ≤ H₀ ∧ 0 ≤ C ∧
      ∀ (H B q : ℕ), H₀ ≤ H → 1 ≤ B → 1 ≤ q →
      (q : ℝ) ≤ (H : ℝ) ^ (Aex : ℝ) →
      ∃ k : ℕ, 0 < k ∧
        (k : ℝ) ≤ 2 * (H : ℝ) ^ η *
          (1 + (B : ℝ) ^ a / (q : ℝ)) ∧
      ∀ (m S Dex : ℕ) (u : Fin 3 → ℤ) (y : Fin S → Fin 3 → ℤ),
      0 < Dex → Dex ≤ H ^ Aex → m * q ∣ Dex →
      m ≠ 0 → 0 < q → Squarefree q →
      (∀ p, p.Prime → ¬ p ∣ Dex →
        (Nat.card (SurfaceReductionZeroPoint p
          (surfaceHypersurfaceFirstChartDehomogenize F)) : ℝ) ≤
            K * (p : ℝ) ^ 2) →
      (∀ j i, (progressionHomogeneousPoint u m (y j) i).natAbs ≤ H) →
      (∀ j i, (y j i).natAbs ≤ B) →
      (∀ j, MvPolynomial.eval (progressionHomogeneousPoint u m (y j)) F = 0) →
      (∀ j, ∃ v, MvPolynomial.eval (fun i => u i + (m : ℤ) * y j i)
        (MvPolynomial.pderiv v
          (surfaceHypersurfaceFirstChartDehomogenize F)) ≠ 0) →
      (∀ p, p.Prime → p ∣ q → ¬ p ∣ m ∧
        ∃ (z : Fin 3 → ℤ) (v : Fin 3),
          (∀ j i, (p : ℤ) ∣ y j i - z i) ∧
          (MvPolynomial.eval (fun i => u i + (m : ℤ) * z i)
            (MvPolynomial.pderiv v
              (surfaceHypersurfaceFirstChartDehomogenize F)) : ZMod p) ≠ 0) →
      ∃ Q : MvPolynomial (Fin 4) ℚ,
        Q.IsHomogeneous (b + k) ∧ Q ∉ I ∧
        ∀ j, MvPolynomial.eval
          (fun i => (progressionHomogeneousPoint u m (y j) i : ℚ)) Q = 0 := by
  classical
  obtain ⟨b, D, A, Haux, C, hD, hA, hHaux, hC, haux⟩ :=
    exists_fixedSurface_auxiliary_of_packetPrimeRange hd I hprime hhom hX
      hdegree F K (by linarith)
  obtain ⟨Hdegree, hHdegree, hchoice⟩ :=
    SurfaceMixedDegreeChoice.exists_packet_mixed_log_threshold
      d b D hd hD K (A : ℝ) (Aex : ℝ) C η a hK hη ha
  let H₀ : ℕ := max Haux ⌈Hdegree⌉₊
  refine ⟨b, D, A, H₀, C, hD, hA, ?_, hC, ?_⟩
  · exact hHaux.trans (Nat.le_max_left _ _)
  intro H B q hH hB hq hqheight
  have hHaux' : Haux ≤ H := (Nat.le_max_left _ _).trans hH
  have hHdegree' : Hdegree ≤ (H : ℝ) := by
    exact (Nat.le_ceil Hdegree).trans (by
      exact_mod_cast (Nat.le_max_right Haux ⌈Hdegree⌉₊).trans hH)
  obtain ⟨k, hk, hkbound, hlogH, hcutoff, hthreshold⟩ :=
    hchoice H B q hHdegree' hB hq hqheight
  refine ⟨k, hk, hkbound, ?_⟩
  intro m S Dex u y hDex hDexHeight hmqdvd hm hqpos hsq
    hpoints hsource hdisplacement hyF hgrad hlocal
  let n := d * affinePlaneMonomialCount k
  have hn : 0 < n := by
    dsimp [n]
    exact Nat.mul_pos hd (by
      have hc := two_mul_affinePlaneMonomialCount k
      nlinarith)
  obtain ⟨t, s, hts, _hs, hweight⟩ :=
    exists_smoothSurfaceJetExponent_layer n hn
  have hcard : Fintype.card (Fin d × AffinePlaneMonomialIndex k) =
      affinePlaneMonomialCount t + s := by
    simpa only [Fintype.card_prod, Fintype.card_fin,
      card_affinePlaneMonomialIndex, n] using hts
  have hweightpos : 0 < affinePlaneMonomialWeight t + (t + 1) * s :=
    layer_weight_pos_of_block hd hk (by simpa only [n] using hts)
  have hlargePoints : ∀ p ∈ PrimeWeightedRange.largePrimesAvoiding H k Dex,
      (Nat.card (SurfaceReductionZeroPoint p
        (surfaceHypersurfaceFirstChartDehomogenize F)) : ℝ) ≤
          K * (p : ℝ) ^ 2 := by
    intro p hp
    exact hpoints p
      (PrimeWeightedRange.mem_largePrimesAvoiding.mp hp).2.2.1
      (PrimeWeightedRange.mem_largePrimesAvoiding.mp hp).2.2.2
  obtain ⟨Q, hQhom, hQI, hQzero⟩ :=
    haux k t s H B q m S k Aex Dex u y hHaux' hlogH hcutoff
      hDex hDexHeight hmqdvd hm hqpos hsq hcard hweightpos hlargePoints
      hsource hdisplacement hyF hgrad hlocal (by
        rw [← hweight]
        convert hthreshold using 1
        all_goals ring)
  exact ⟨Q, hQhom, hQI, hQzero⟩

/-- Pointwise form of the preceding uniform-degree theorem.  The packet
divisibility certificate itself implies the height bound for `q`. -/
theorem exists_fixedSurface_quantitative_auxiliary_of_packetPrimeRange
    {d : ℕ} (hd : 0 < d)
    (I : Ideal (MvPolynomial (Fin 4) ℚ))
    (hprime : I.IsPrime)
    (hhom : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule _ ℚ))
    (hX : MvPolynomial.X 0 ∉ I)
    (hdegree : HasProjectiveDimensionDegree I 2 d)
    (F : MvPolynomial (Fin 4) ℤ)
    (K : ℝ) (hK : 1 ≤ K) (Aex : ℕ)
    (η a : ℝ) (hη : 0 < η)
    (ha : Real.sqrt K / Real.sqrt (d : ℝ) < a) :
    ∃ b D A H₀ : ℕ, ∃ C : ℝ,
      1 ≤ D ∧ 2 ≤ A ∧ 2 ≤ H₀ ∧ 0 ≤ C ∧
      ∀ (H B q m S Dex : ℕ)
        (u : Fin 3 → ℤ) (y : Fin S → Fin 3 → ℤ),
      H₀ ≤ H → 1 ≤ B →
      0 < Dex → Dex ≤ H ^ Aex → m * q ∣ Dex →
      m ≠ 0 → 0 < q → Squarefree q →
      (∀ p, p.Prime → ¬ p ∣ Dex →
        (Nat.card (SurfaceReductionZeroPoint p
          (surfaceHypersurfaceFirstChartDehomogenize F)) : ℝ) ≤
            K * (p : ℝ) ^ 2) →
      (∀ j i, (progressionHomogeneousPoint u m (y j) i).natAbs ≤ H) →
      (∀ j i, (y j i).natAbs ≤ B) →
      (∀ j, MvPolynomial.eval (progressionHomogeneousPoint u m (y j)) F = 0) →
      (∀ j, ∃ v, MvPolynomial.eval (fun i => u i + (m : ℤ) * y j i)
        (MvPolynomial.pderiv v
          (surfaceHypersurfaceFirstChartDehomogenize F)) ≠ 0) →
      (∀ p, p.Prime → p ∣ q → ¬ p ∣ m ∧
        ∃ (z : Fin 3 → ℤ) (v : Fin 3),
          (∀ j i, (p : ℤ) ∣ y j i - z i) ∧
          (MvPolynomial.eval (fun i => u i + (m : ℤ) * z i)
            (MvPolynomial.pderiv v
              (surfaceHypersurfaceFirstChartDehomogenize F)) : ZMod p) ≠ 0) →
      ∃ k : ℕ, ∃ Q : MvPolynomial (Fin 4) ℚ,
        0 < k ∧
        (k : ℝ) ≤ 2 * (H : ℝ) ^ η *
          (1 + (B : ℝ) ^ a / (q : ℝ)) ∧
        Q.IsHomogeneous (b + k) ∧ Q ∉ I ∧
        ∀ j, MvPolynomial.eval
          (fun i => (progressionHomogeneousPoint u m (y j) i : ℚ)) Q = 0 := by
  obtain ⟨b, D, A, H₀, C, hD, hA, hH₀, hC, hfamily⟩ :=
    exists_fixedSurface_quantitative_auxiliaryFamily_of_packetPrimeRange
      hd I hprime hhom hX hdegree F K hK Aex η a hη ha
  refine ⟨b, D, A, H₀, C, hD, hA, hH₀, hC, ?_⟩
  intro H B q m S Dex u y hH hB hDex hDexHeight hmqdvd hm hq hsq
    hpoints hsource hdisplacement hyF hgrad hlocal
  have hqheightNat : q ≤ H ^ Aex :=
    packet_modulus_le_height hDex hDexHeight hmqdvd hm
  have hqheight : (q : ℝ) ≤ (H : ℝ) ^ (Aex : ℝ) := by
    rw [Real.rpow_natCast]
    exact_mod_cast hqheightNat
  obtain ⟨k, hk, hkbound, haux⟩ :=
    hfamily H B q hH hB (Nat.one_le_iff_ne_zero.mpr hq.ne') hqheight
  obtain ⟨Q, hQhom, hQI, hQzero⟩ :=
    haux m S Dex u y hDex hDexHeight hmqdvd hm hq hsq hpoints
      hsource hdisplacement hyF hgrad hlocal
  exact ⟨k, Q, hk, hkbound, hQhom, hQI, hQzero⟩

end
end TranslatedDepthSeven
