import CubicTenVariables.FixedLeadingSurfacePacketAuxiliary
import TranslatedDepthSeven.PrimeWeightedRange
import TranslatedDepthSeven.SurfaceMixedLogDegreeChoice

/-!
# Fixed-leading surfaces with a logarithmic auxiliary degree

This is the original-Salberger-scale sibling of
`FixedLeadingSurfaceQuantitativeAuxiliary`.  It uses the same packet,
mixed-prime, and properness machinery, but chooses

`k = O(log H * (1 + B ^ a / q))`.

The fixed implied constant and height threshold precede the surface, points,
box, and packet modulus.  This file constructs the actual rational auxiliary;
an integral representative with an explicit coefficient-height bound is a
separate interface.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 300000
noncomputable section

namespace CubicTenVariables.FixedLeadingSurfaceLogarithmicAuxiliary

open MvPolynomial TranslatedDepthSeven
open FixedLeadingSurfacePacketAuxiliary
open scoped BigOperators

private theorem layer_weight_pos_of_block
    {d k t s : ℕ} (hd : 0 < d) (hk : 0 < k)
    (hcount : d * affinePlaneMonomialCount k = affinePlaneMonomialCount t + s) :
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

private theorem log_fixedCoordinate_bound_le
    (d k H B : ℕ) (hH : 0 < H) (hB : 0 < B) :
    Real.log (((d * affinePlaneMonomialCount k).factorial *
      (H ^ (d - 1)) ^ (d * affinePlaneMonomialCount k) *
        B ^ (d * affinePlaneMonomialWeight k) : ℕ) : ℝ) ≤
    Real.log (((d * affinePlaneMonomialCount k).factorial *
      (1 * H ^ (d - 1)) ^ (d * affinePlaneMonomialCount k) *
        (((d + 1) ^ 3) * B) ^ (d * affinePlaneMonomialWeight k) : ℕ) : ℝ) := by
  have hscale : B ≤ (d + 1) ^ 3 * B := by
    calc
      B = 1 * B := by omega
      _ ≤ (d + 1) ^ 3 * B := Nat.mul_le_mul_right B
        (Nat.one_le_iff_ne_zero.mpr (pow_ne_zero 3 (by omega)))
  have hnat := Nat.mul_le_mul_left
    ((d * affinePlaneMonomialCount k).factorial *
      (H ^ (d - 1)) ^ (d * affinePlaneMonomialCount k))
    (Nat.pow_le_pow_left hscale (d * affinePlaneMonomialWeight k))
  apply Real.log_le_log (by positivity)
  simpa only [one_mul] using (show
    (((d * affinePlaneMonomialCount k).factorial *
      (H ^ (d - 1)) ^ (d * affinePlaneMonomialCount k) *
        B ^ (d * affinePlaneMonomialWeight k) : ℕ) : ℝ) ≤
    (((d * affinePlaneMonomialCount k).factorial *
      (H ^ (d - 1)) ^ (d * affinePlaneMonomialCount k) *
        (((d + 1) ^ 3) * B) ^ (d * affinePlaneMonomialWeight k) : ℕ) : ℝ) by
      exact_mod_cast hnat)

/-- The logarithmic block degree and its implied constant are uniform in the
lower coefficients and in all point data. -/
theorem exists_uniform_logarithmic_auxiliaryFamily
    {d e : ℕ} (hd : 0 < d)
    (K : ℝ) (hK : 1 ≤ K) (Aex : ℕ)
    (a : ℝ) (ha : Real.sqrt K / Real.sqrt (d : ℝ) < a) :
    ∃ L : ℝ, ∃ H₀ : ℕ, 1 ≤ L ∧ 2 ≤ H₀ ∧
      ∀ (H B q : ℕ), H₀ ≤ H → 1 ≤ B → 1 ≤ q →
      (q : ℝ) ≤ (H : ℝ) ^ (Aex : ℝ) →
      ∃ k : ℕ, 0 < k ∧
        (k : ℝ) ≤ 2 * L * Real.log (H : ℝ) *
          (1 + (B : ℝ) ^ a / (q : ℝ)) ∧
      ∀ (F : MvPolynomial (Fin 4) ℤ),
      (map (Int.castRingHom ℚ) F).degreeOf 3 = d →
      (surfaceHypersurfaceFirstChartDehomogenize F).totalDegree ≤ d →
      mvPolynomialCoefficientNatAbsMax
        (surfaceHypersurfaceFirstChartDehomogenize F) ≤ H ^ e →
      ∀ (m S Dex : ℕ) (u : Fin 3 → ℤ) (y : Fin S → Fin 3 → ℤ),
      0 < Dex → Dex ≤ H ^ Aex → m * q ∣ Dex →
      m ≠ 0 → 0 < q → Squarefree q →
      (∀ p, p.Prime → ¬ p ∣ Dex →
        (Nat.card (SurfaceReductionZeroPoint p
          (surfaceHypersurfaceFirstChartDehomogenize F)) : ℝ) ≤ K * (p : ℝ) ^ 2) →
      (∀ j i, (progressionHomogeneousPoint u m (y j) i).natAbs ≤ H) →
      (∀ j i, (y j i).natAbs ≤ B) →
      (∀ j, eval (progressionHomogeneousPoint u m (y j)) F = 0) →
      (∀ j, ∃ v, eval (fun i => u i + (m : ℤ) * y j i)
        (pderiv v (surfaceHypersurfaceFirstChartDehomogenize F)) ≠ 0) →
      (∀ p, p.Prime → p ∣ q → ¬ p ∣ m ∧
        ∃ (z : Fin 3 → ℤ) (v : Fin 3),
          (∀ j i, (p : ℤ) ∣ y j i - z i) ∧
          (eval (fun i => u i + (m : ℤ) * z i)
            (pderiv v (surfaceHypersurfaceFirstChartDehomogenize F)) : ZMod p) ≠ 0) →
      ∃ Q : MvPolynomial (Fin 4) ℚ,
        Q.IsHomogeneous (d - 1 + k) ∧
        Q ∉ Ideal.span {map (Int.castRingHom ℚ) F} ∧
        ∀ j, eval (fun i => (progressionHomogeneousPoint u m (y j) i : ℚ)) Q = 0 := by
  classical
  obtain ⟨C, _hC, hrange⟩ := PrimeWeightedRange.exists_largePrimeRange_estimates
  obtain ⟨L, Hdegree, hL, _hHdegree, hchoice⟩ :=
    SurfaceMixedLogDegreeChoice.exists_packet_mixed_logarithmic_threshold
      d (d - 1) 1 hd (by omega) K ((e + d + 2 : ℕ) : ℝ)
        (Aex : ℝ) C a hK ha
  let Haux : ℕ := max 2 ((d + 1) ^ 3 * d)
  let H₀ : ℕ := max Haux ⌈Hdegree⌉₊
  refine ⟨L, H₀, hL, (Nat.le_max_left 2 _).trans (Nat.le_max_left _ _), ?_⟩
  intro H B q hH hB hq hqheight
  have hHaux : Haux ≤ H := (Nat.le_max_left _ _).trans hH
  have hHdegree : Hdegree ≤ (H : ℝ) := by
    exact (Nat.le_ceil Hdegree).trans (by
      exact_mod_cast (Nat.le_max_right Haux ⌈Hdegree⌉₊).trans hH)
  obtain ⟨k, hk, hkbound, hlogH, hcutoff, hthreshold⟩ :=
    hchoice H B q hHdegree hB hq hqheight
  refine ⟨k, hk, hkbound, ?_⟩
  intro F hvariable hchartDegree hcoeff m S Dex u y hDex hDexHeight hmqdvd
    hm hqpos hsq hpoints hsource hdisplacement hyF hgrad hlocal
  let P := PrimeWeightedRange.largePrimesAvoiding H k Dex
  have hP : ∀ p ∈ P, p.Prime := fun p hp =>
    (PrimeWeightedRange.prime_and_lower_bound_of_mem hp).1
  have hPlarge : ∀ p ∈ P, Real.log (H : ℝ) ≤ (p : ℝ) := fun p hp =>
    (PrimeWeightedRange.prime_and_lower_bound_of_mem hp).2
  have hPm : ∀ p ∈ P, ¬ p ∣ m := by
    intro p hp
    exact PrimeWeightedRange.not_dvd_factor_of_mem hp
      ((Nat.dvd_mul_right m q).trans hmqdvd)
  have hPq : ∀ p ∈ P, ¬ p ∣ q := by
    intro p hp
    exact PrimeWeightedRange.not_dvd_factor_of_mem hp
      ((Nat.dvd_mul_left q m).trans hmqdvd)
  have hcount : ∀ p ∈ P,
      (Nat.card (SurfaceReductionZeroPoint p
        (surfaceHypersurfaceFirstChartDehomogenize F)) : ℝ) ≤ K * (p : ℝ) ^ 2 := by
    intro p hp
    exact hpoints p (PrimeWeightedRange.mem_largePrimesAvoiding.mp hp).2.2.1
      (PrimeWeightedRange.mem_largePrimesAvoiding.mp hp).2.2.2
  obtain ⟨hweighted, hunweighted⟩ :=
    hrange H k Aex Dex hlogH hcutoff hDex hDexHeight
  let n := d * affinePlaneMonomialCount k
  have hn : 0 < n := by
    dsimp [n]
    exact Nat.mul_pos hd (by
      have hc := two_mul_affinePlaneMonomialCount k
      nlinarith)
  obtain ⟨t, s, hts, _hs, hweight⟩ := exists_smoothSurfaceJetExponent_layer n hn
  have hcard : Fintype.card (Fin d × AffinePlaneMonomialIndex k) =
      affinePlaneMonomialCount t + s := by
    simpa only [Fintype.card_prod, Fintype.card_fin,
      card_affinePlaneMonomialIndex, n] using hts
  have hweightpos : 0 < affinePlaneMonomialWeight t + (t + 1) * s :=
    layer_weight_pos_of_block hd hk (by simpa only [n] using hts)
  apply exists_fixedCoordinate_auxiliary_of_packetMixedPrimeSum hd F hvariable hchartDegree
    K (by linarith) k t s H B q m S u y P hHaux hcoeff hm hqpos hsq hcard hweightpos
    hP hPm hPq hPlarge hcount hsource hdisplacement hyF hgrad hlocal
  have hHpos : 0 < H := (by positivity : 0 < Haux).trans_le hHaux
  have harch := log_fixedCoordinate_bound_le d k H B hHpos (by omega)
  apply (harch.trans_lt hthreshold).trans_le
  rw [← hweight]
  have hcoeffPos : 0 ≤ (2 * Real.sqrt 2 / 3) / Real.sqrt K *
      ((d * affinePlaneMonomialCount k : ℕ) : ℝ) ^ (3 / 2 : ℝ) := by positivity
  have hweighted' := mul_le_mul_of_nonneg_left hweighted hcoeffPos
  have hunweighted' := mul_le_mul_of_nonneg_left hunweighted
    (show 0 ≤ (2 : ℝ) * (d * affinePlaneMonomialCount k : ℕ) by positivity)
  dsimp only [P, n]
  linarith

/-- Pointwise packaging; divisibility into the exceptional integer supplies
the packet-modulus height bound. -/
theorem exists_uniform_logarithmic_auxiliary
    {d e : ℕ} (hd : 0 < d)
    (K : ℝ) (hK : 1 ≤ K) (Aex : ℕ)
    (a : ℝ) (ha : Real.sqrt K / Real.sqrt (d : ℝ) < a) :
    ∃ L : ℝ, ∃ H₀ : ℕ, 1 ≤ L ∧ 2 ≤ H₀ ∧
      ∀ (F : MvPolynomial (Fin 4) ℤ) (H B q m S Dex : ℕ)
        (u : Fin 3 → ℤ) (y : Fin S → Fin 3 → ℤ),
      H₀ ≤ H → 1 ≤ B →
      (map (Int.castRingHom ℚ) F).degreeOf 3 = d →
      (surfaceHypersurfaceFirstChartDehomogenize F).totalDegree ≤ d →
      mvPolynomialCoefficientNatAbsMax
        (surfaceHypersurfaceFirstChartDehomogenize F) ≤ H ^ e →
      0 < Dex → Dex ≤ H ^ Aex → m * q ∣ Dex →
      m ≠ 0 → 0 < q → Squarefree q →
      (∀ p, p.Prime → ¬ p ∣ Dex →
        (Nat.card (SurfaceReductionZeroPoint p
          (surfaceHypersurfaceFirstChartDehomogenize F)) : ℝ) ≤ K * (p : ℝ) ^ 2) →
      (∀ j i, (progressionHomogeneousPoint u m (y j) i).natAbs ≤ H) →
      (∀ j i, (y j i).natAbs ≤ B) →
      (∀ j, eval (progressionHomogeneousPoint u m (y j)) F = 0) →
      (∀ j, ∃ v, eval (fun i => u i + (m : ℤ) * y j i)
        (pderiv v (surfaceHypersurfaceFirstChartDehomogenize F)) ≠ 0) →
      (∀ p, p.Prime → p ∣ q → ¬ p ∣ m ∧
        ∃ (z : Fin 3 → ℤ) (v : Fin 3),
          (∀ j i, (p : ℤ) ∣ y j i - z i) ∧
          (eval (fun i => u i + (m : ℤ) * z i)
            (pderiv v (surfaceHypersurfaceFirstChartDehomogenize F)) : ZMod p) ≠ 0) →
      ∃ k : ℕ, 0 < k ∧
        (k : ℝ) ≤ 2 * L * Real.log (H : ℝ) *
          (1 + (B : ℝ) ^ a / (q : ℝ)) ∧
      ∃ Q : MvPolynomial (Fin 4) ℚ,
        Q.IsHomogeneous (d - 1 + k) ∧
        Q ∉ Ideal.span {map (Int.castRingHom ℚ) F} ∧
        ∀ j, eval (fun i => (progressionHomogeneousPoint u m (y j) i : ℚ)) Q = 0 := by
  obtain ⟨L, H₀, hL, hH₀, hfamily⟩ :=
    exists_uniform_logarithmic_auxiliaryFamily (e := e) hd K hK Aex a ha
  refine ⟨L, H₀, hL, hH₀, ?_⟩
  intro F H B q m S Dex u y hH hB hvariable hdegree hcoeff
    hDex hDexHeight hmqdvd hm hq hsq hpoints hsource hdisplacement hyF hgrad hlocal
  have hqle : q ≤ Dex := by
    calc
      q = 1 * q := by simp
      _ ≤ m * q := Nat.mul_le_mul_right q (Nat.one_le_iff_ne_zero.mpr hm)
      _ ≤ Dex := Nat.le_of_dvd hDex hmqdvd
  have hqheight : (q : ℝ) ≤ (H : ℝ) ^ (Aex : ℝ) := by
    rw [Real.rpow_natCast]
    exact_mod_cast hqle.trans hDexHeight
  obtain ⟨k, hk, hkbound, haux⟩ :=
    hfamily H B q hH hB (Nat.one_le_iff_ne_zero.mpr hq.ne') hqheight
  obtain ⟨Q, hhom, hnontrivial, hvanish⟩ :=
    haux F hvariable hdegree hcoeff m S Dex u y hDex hDexHeight hmqdvd hm hq hsq
      hpoints hsource hdisplacement hyF hgrad hlocal
  exact ⟨k, hk, hkbound, Q, hhom, hnontrivial, hvanish⟩

end CubicTenVariables.FixedLeadingSurfaceLogarithmicAuxiliary
