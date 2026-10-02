import CubicTenVariables.HeathBrownTernaryPrimitiveCountInternal
import CubicTenVariables.FixedLeadingSurfaceLogarithmicActualRootDegreeSplitInternal
import CubicTenVariables.FixedLeadingSurfaceLogarithmicRootLineLedger
import CubicTenVariables.FixedLeadingSurfaceRootDegreeSplitNumerics
import CubicTenVariables.FixedLeadingSurfaceProjectedCurveHighDegreeBridge
import CubicTenVariables.FixedLeadingSurfaceLogarithmicPersistentDegree
import CubicTenVariables.FixedLeadingSurfaceNormalizedBoxNumerics
import CubicTenVariables.FixedLeadingSurfaceReservoirCapNumerics
import CubicTenVariables.FixedLeadingSurfaceNormalizedCountReduction
import CubicTenVariables.HomogeneousHypersurfaceIntegralityOpenProved
import TranslatedDepthSeven.ProjectiveConjugateHilbertInternal

/-!
# Normalized fixed-leading surfaces by internal projected-curve counting

The high-degree and bounded-degree nonlinear curve branches are proved by
bounded projection, local determinants and prime avoidance. Primitive line
directions are counted by the internal fixed-form projective curve estimate.
The survivor family is the already proved rational logarithmic family. The
only external argument is the finite-field plane-curve Weil bound; no Pila,
Heath-Brown, Salberger curve-count or auxiliary-cover premise is supplied.
-/

set_option autoImplicit false
set_option maxHeartbeats 18000000
set_option synthInstance.maxHeartbeats 1000000

noncomputable section

namespace CubicTenVariables.FixedLeadingSurfaceNormalizedRegularCountInternalCurves

open MvPolynomial TranslatedDepthSeven Published Filter
open FixedLeadingSurfaceCoordinateChoice FixedLeadingSurfaceCoordinateTransport
open FixedLeadingSurfaceNormalizedPrimeCount FixedLeadingSurfacePrimeReservoir
open FixedLeadingSurfaceLogarithmicActualSurvivorPackets
open FixedLeadingSurfaceLogarithmicActualRootDegreeSplitInternal
open FixedLeadingSurfaceLogarithmicRootLineLedger
open FixedLeadingSurfaceRootDegreeSplitNumerics
open FixedLeadingSurfaceLogarithmicNumerics
open FixedLeadingSurfaceProjectedCurveHighDegreeBridge
open FixedLeadingSurfaceLogarithmicPersistentDegree
open FixedLeadingSurfaceNormalizedBoxNumerics
open FixedLeadingSurfaceReservoirCapNumerics
open FixedLeadingSurfaceNormalizedCountReduction
open FixedLeadingSurfaceHeightAlternativeChart
open FixedLeadingSurfacePersistentRootDegreeSplit
open scoped BigOperators Topology

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The normalized regular-point estimate with the high-degree curve branch
proved by the internal projected-plane determinant method. -/
theorem normalized_regular_polynomial_height_count
    (curveWeil : Literature.AffinePlaneCurveWeil)
    {d : ℕ} (hd : 4 ≤ d) (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    NormalizedRegularPolynomialHeightCount d epsilon := by
  classical
  intro k hk hirr
  let e := heightExponent d
  obtain ⟨K, alpha, eta, delta, pilaEpsilon, highEpsilon,
      hK, halpha, halphaOne, heta, hdelta, hpilaEpsilon,
      hhighEpsilon, hrange, hedgeExponent, hlowExponent,
      hhighExponent, hmassExponent⟩ :=
    exists_originalSalberger_exponent_parameters hd epsilon hepsilon
  let theta := min pilaEpsilon highEpsilon
  have htheta : 0 < theta := lt_min hpilaEpsilon hhighEpsilon
  have hthetaPila : theta ≤ pilaEpsilon := min_le_left _ _
  have hthetaHigh : theta ≤ highEpsilon := min_le_right _ _
  have hlowExponent' :
      (alpha + eta) + ((1 / 2 : ℝ) + theta) ≤ 1 + epsilon := by
    linarith
  have hhighExponent' :
      (alpha + eta) + (3 * theta / 2 + 3 * eta) ≤ 1 + epsilon := by
    linarith
  obtain ⟨a, b, L, Hpacket, hdet, hL, hHpacket, hpackets⟩ :=
    exists_normalized_logarithmic_actual_survivor_packets
      HomogeneousHypersurfaceIntegralityOpenProved.proved curveWeil
      (by omega : 2 ≤ d) k hk hirr K eta alpha delta
        hK heta halpha halphaOne hdelta hrange
  let Cd : ℝ := (d : ℝ) * (((d - 1 : ℕ) : ℝ) + 1 + 4 * L)
  have hCd : 0 ≤ Cd := by
    dsimp only [Cd]
    have hLnonneg : 0 ≤ L := by linarith
    positivity
  obtain ⟨cutoff, hhighEvent⟩ :=
    exists_eventually_internal_rootCallback Cd theta hCd htheta
  obtain ⟨Vhigh, hVhigh⟩ := eventually_atTop.1 hhighEvent
  let Hhigh : ℕ := ⌈max 0 Vhigh⌉₊
  obtain ⟨Cpila, hCpila, hrootSplit⟩ :=
    exists_uniform_actual_rootDegreeSplit_bound 
      qbarConjugatePreservesProjectiveDimensionDegree cutoff theta htheta
  let Chigh : ℝ := 1
  have hChigh : 0 < Chigh := by simp only [Chigh]; positivity
  obtain ⟨Aline, hAline, hline⟩ :=
    exists_uniform_normalized_rootLine_contribution
      qbarConjugatePreservesProjectiveDimensionDegree HeathBrownTernaryPrimitiveCountInternal.proved
        (by omega : 2 ≤ d) k hk hirr a b epsilon hepsilon
  let M := manuscriptPoolDepthCoefficient (e + 1 + d + 2 : ℕ) alpha
  let Cint := manuscriptPrimeIntervalCoefficient (e + 1 + d + 2 : ℕ) alpha
  let Cq := (4 * Cint * (delta / 3)⁻¹) * 2
  let Cr := 2 * Cint / delta
  obtain ⟨hM, hCint, hCq, hCr⟩ :=
    actual_reservoir_coefficients_nonneg d e alpha delta halpha hdelta
  obtain ⟨Aedge, Hedge, hAedge, hHedge, hedge⟩ :=
    exists_uniform_box_edge_constant d (d - 1) M (Cq + 1) Cr eta alpha
      delta epsilon hM
      (by change 0 ≤ Cq at hCq; linarith)
      hCr heta.le hdelta hedgeExponent
  let rho := alpha + eta
  let sigma := (1 / 2 : ℝ) + theta
  let tau := 3 * theta / 2 + 3 * eta
  let Aroot := (d : ℝ) * (((d - 1 : ℕ) : ℝ) + 5)
  let Alow := (cutoff : ℝ) ^ 2 + Cpila * 2 ^ sigma
  let Ahigh := Chigh * (1 + 3 * eta⁻¹) ^ (3 : ℕ) * 2 ^ tau
  let Aerror := Aroot * Alow + Aroot * Ahigh + Aroot ^ 2
  let AlineTotal := Aroot ^ 2 + Aline + Aroot
  let H₀ := max Hpacket (max Hedge Hhigh)
  let Atotal := 1 + (Aedge + AlineTotal + Aerror) * 2 ^ (1 + epsilon)
  refine ⟨a, b, Atotal, H₀, ?_, ?_⟩
  · dsimp only [Atotal, AlineTotal, Aerror, Aroot, Alow, Ahigh, sigma, tau]
    positivity
  intro g c hc hdegree htop H hH hheight X hzero hgrad hbox
  have hHp : Hpacket ≤ H :=
    (Nat.le_max_left _ _).trans ((Nat.le_max_left _ _).trans hH)
  have hHe : Hedge ≤ H :=
    (Nat.le_max_left _ _).trans
      ((Nat.le_max_right _ _).trans ((Nat.le_max_left _ _).trans hH))
  have hHhigh : Hhigh ≤ H :=
    (Nat.le_max_right _ _).trans
      ((Nat.le_max_right _ _).trans ((Nat.le_max_left _ _).trans hH))
  have hHone : 1 ≤ H := (Nat.le_max_right _ _).trans hH
  by_cases hX : X.Nonempty
  swap
  · have hz : X = ∅ := Finset.not_nonempty_iff_eq_empty.mp hX
    simp only [hz, Finset.card_empty, Nat.cast_zero]
    positivity
  let P := ordinaryPrimePool d e alpha H
  let depth := ordinaryDepth d e alpha H
  let F := projectiveEquiv a b (homogenize d g)
  let Qcap := ⌈Cq * (H : ℝ) ^ alpha * (H : ℝ) ^ delta⌉₊
  let Rcap := ⌊2 * (Cint * Real.log (H : ℝ))⌋₊
  let Lroot := d - 1 + quantitativePrefixUniformBlockDegree H H eta alpha
  obtain ⟨hP, hPm, hdepth, hcard, hinterval, _hmoduli, hterminal,
    blockDegree, hblock, hrootSharp, hterminalSharp, hfamily⟩ :=
      hpackets H hHp
  have hchartZero : ∀ z ∈ X,
      eval z (surfaceHypersurfaceFirstChartDehomogenize F) = 0 := by
    intro z hz
    have hv := hzero z hz
    rw [ordinaryPoint_eq, ← eval_standardDehomogenizationHom] at hv
    exact hv
  obtain ⟨hroom, auxiliary, haux⟩ :=
    hfamily g c hc hdegree htop hheight X hbox hchartZero hgrad
  have hterminalCaps : ∀ v : PrimeSubsetPrefix.Vertex P depth,
      v.1.card = depth →
        (H : ℝ) ^ alpha ≤ (PrimeSubsetPrefix.modulus v : ℝ) ∧
          PrimeSubsetPrefix.modulus v ≤ Qcap := by
    intro v hv
    obtain ⟨_hsq, hlo, hup⟩ := hterminal (PrimeSubsetPrefix.modulus v)
      (terminalPrefix_modulus_mem_modulusReservoir v hv)
    refine ⟨?_, ?_⟩
    · have hpow : 0 ≤ (H : ℝ) ^ alpha := by positivity
      linarith
    · have hround := Nat.le_ceil
        (Cq * (H : ℝ) ^ alpha * (H : ℝ) ^ delta)
      exact_mod_cast hup.trans hround
  have hprimeCap : ∀ p ∈ P, p ≤ Rcap := fun p hp => (hinterval p hp).2
  have hrootCap : d - 1 + blockDegree (PrimeSubsetPrefix.root P depth) ≤
      Lroot := by
    exact FixedLeadingSurfaceSurvivorNumerics.root_degree_cap hP blockDegree
      (fun v => (hblock v).2.2)
  have hzeroProjective : ∀ z ∈ X,
      eval (progressionHomogeneousPoint 0 1 z) F = 0 := by
    intro z hz
    rw [ordinaryPoint_eq, ← eval_standardDehomogenizationHom]
    exact hchartZero z hz
  obtain ⟨z₀, hz₀, degree, hrootData, hrootMass, hactiveCard, hcount⟩ :=
    hrootSplit Chigh (by omega : 2 ≤ d) hHone k g c hirr hc hdegree htop
      a b eta alpha heta.le P depth hP hPm hterminalCaps hprimeCap X hX
      hbox hzeroProjective hroom blockDegree (fun v => (hblock v).2.2)
      auxiliary haux hrootCap
  let sourceEquations : Finset (MvPolynomial (Fin 4) ℚ) :=
    {map (Int.castRingHom ℚ) F}
  let root := PrimeSubsetPrefix.root P depth
  let G₀ := auxiliary root (integralResidueVector z₀)
  let cell := quantitativePrefixPersistentCell sourceEquations auxiliary
    0 1 X (smoothAllowedPrimes P F)
  let active := activeQbarPersistentRootComponentOptions
    sourceEquations G₀ cell
  have hG₀data := haux z₀ hz₀ root
    (PrimeSubsetPrefix.root_mem_surviving P (smoothAllowedPrimes P F z₀) depth)
  have hrootEquation : ∀ z ∈ X,
      quantitativePrefixCutEquations sourceEquations auxiliary z root =
        qbarSurfaceCutEquationFamily sourceEquations G₀ := by
    intro z _hz
    have hresidue :
        (integralResidueVector z :
          Fin 3 → ZMod (PrimeSubsetPrefix.modulus root)) =
            integralResidueVector z₀ := by
      rw [show PrimeSubsetPrefix.modulus root = 1 by
        exact PrimeSubsetPrefix.modulus_root P depth]
      exact Subsingleton.elim _ _
    simp only [quantitativePrefixCutEquations, G₀]
    rw [hresidue]
  have hselected : ∀ o ∈ active, ∀ z ∈ cell o,
      selectedFiniteEquationComponent
        (qbarSurfaceCutEquationFamily sourceEquations G₀)
        (fun i ↦ (progressionHomogeneousPoint 0 1 z i : Qbar)) = o := by
    intro o _ho z hz
    have hzData := (Finset.mem_filter.mp hz).2
    have hlabel := hzData.2 root
      (PrimeSubsetPrefix.root_mem_surviving P (smoothAllowedPrimes P F z) depth)
    rw [hrootEquation z (Finset.filter_subset _ _ hz)] at hlabel
    exact hlabel
  obtain ⟨_hFne, _hFhom, _hFprimeQ, hFdegree⟩ :=
    FixedLeadingSurfaceSingularCount.normalized_surface_certificate
      (by omega : 0 < d) a b g hdegree
      (FixedLeadingSurfaceSingularCount.irreducible_actual_top
        k g c hirr hc htop)
  have hcellZero : ∀ QbarIdeal,
      some QbarIdeal ∈ active → ∀ z ∈ cell (some QbarIdeal),
        (fun i ↦ ((integralAffineChartVector z i : ℤ) : Qbar)) ∈
          affineIdealZeroLocus QbarIdeal := by
    intro QbarIdeal hQ z hz
    have hcomponent := (selectedFiniteEquationComponent_spec
      (qbarSurfaceCutEquationFamily sourceEquations G₀)
      (fun i ↦ (progressionHomogeneousPoint 0 1 z i : Qbar))
      (hselected (some QbarIdeal) hQ z hz)).2
    simpa [progressionHomogeneousPoint, integralAffineChartVector] using hcomponent
  let side : ℝ := 2 * (H : ℝ) + 2
  have hside : 2 ≤ side := by
    dsimp only [side]
    have hHnonneg : (0 : ℝ) ≤ H := by positivity
    linarith
  let volume : ℝ := side ^ (3 : ℕ)
  have hHvolume : (H : ℝ) ≤ volume := by
    have hHside : (H : ℝ) ≤ side := by
      dsimp only [side]
      have hHnonneg : (0 : ℝ) ≤ H := by positivity
      linarith
    have hsideOne : 1 ≤ side := one_le_two.trans hside
    have hsidePower : side ≤ side ^ (3 : ℕ) := by
      simpa only [pow_one] using
        (pow_le_pow_right₀ hsideOne (by omega : 1 ≤ 3))
    exact hHside.trans hsidePower
  have hVhighThreshold : Vhigh ≤ volume := by
    have hVceil : Vhigh ≤ (Hhigh : ℝ) := by
      calc
        Vhigh ≤ max 0 Vhigh := le_max_right _ _
        _ ≤ (Hhigh : ℝ) := by
          exact Nat.le_ceil (max 0 Vhigh)
    have hceilH : (Hhigh : ℝ) ≤ (H : ℝ) := by
      exact_mod_cast hHhigh
    exact hVceil.trans (hceilH.trans hHvolume)
  have hI : finiteEquationIdeal sourceEquations =
      Ideal.span {map (Int.castRingHom ℚ) F} := by
    simp [sourceEquations, finiteEquationIdeal]
  have hgeometricPrime : ((finiteEquationIdeal sourceEquations).map
      (MvPolynomial.map (algebraMap ℚ Qbar))).IsPrime := by
    rw [hI]
    exact FixedLeadingSurfaceGeometricPrime.geometrically_prime_normalized_surface
      k g c hirr hc hdegree htop a b
  have hallowed : ∀ z ∈ X, smoothAllowedPrimes P F z ⊆ P :=
    fun z _ ↦ smoothAllowedPrimes_subset P F z
  have hauxData : ∀ z ∈ X, ∀ v ∈
      PrimeSubsetPrefix.survivingVertices P (smoothAllowedPrimes P F z) depth,
      (auxiliary v (integralResidueVector z)).IsHomogeneous
          (d - 1 + blockDegree v) ∧
        auxiliary v (integralResidueVector z) ∉
          finiteEquationIdeal sourceEquations := by
    intro z hz v hv
    rw [hI]
    exact ⟨(haux z hz v hv).1, (haux z hz v hv).2.1⟩
  have hdegreeLog : ∀ QbarIdeal, some QbarIdeal ∈ active →
      (degree QbarIdeal : ℝ) ≤ Cd * (1 + Real.log volume) := by
    intro QbarIdeal hQactive
    have hnonempty : (cell (some QbarIdeal)).Nonempty :=
      (mem_activeQbarPersistentRootComponentOptions_iff
        sourceEquations G₀ cell (some QbarIdeal)).mp hQactive |>.2
    have hoption :=
      ((mem_activeQbarPersistentRootComponentOptions_iff
        sourceEquations G₀ cell (some QbarIdeal)).mp hQactive).1
    obtain ⟨Q, hQ, hsome⟩ :=
      (mem_finiteEquationComponentOptions_iff
        (qbarSurfaceCutEquationFamily sourceEquations G₀)
        (some QbarIdeal)).mp hoption
    have hQQ : Q = QbarIdeal := Option.some_injective _ hsome
    have hQfamily : QbarIdeal ∈ finiteEquationMinimalPrimes
        (qbarSurfaceCutEquationFamily sourceEquations G₀) := by
      simpa only [hQQ] using hQ
    have hQdata := hrootData QbarIdeal hQfamily
    have hraw := quantitativePrefixPersistent_degree_le_log_volume
      (d := d) (b := d - 1) (H := H) (L := L) (V := volume)
      (by linarith : 0 ≤ L) hHone hHvolume sourceEquations
      hgeometricPrime (by simpa only [hI] using hFdegree)
      (P := P) (depth := depth) 0 1 X (smoothAllowedPrimes P F)
      blockDegree auxiliary hallowed hroom hauxData hterminalSharp
      QbarIdeal (degree QbarIdeal)
      hQdata.1 hQdata.2.1 hQdata.2.2.2 hnonempty
    simpa only [Cd, volume, Nat.cast_sub (by omega : 1 ≤ d)] using hraw
  have hHigh : Salberger2023Theorem316PersistentRootCallback
      sourceEquations G₀ cell degree cutoff Chigh theta
        ((2 * (H : ℝ) + 2) ^ (3 : ℕ)) := by
    have hcallback := hVhigh volume hVhighThreshold H hHvolume
      sourceEquations G₀ cell degree
      (fun QbarIdeal hQ ↦
        ⟨(hrootData QbarIdeal hQ).2.1,
          (hrootData QbarIdeal hQ).2.2.2⟩)
      hdegreeLog
      (fun QbarIdeal hQ z hz f hf ↦ hcellZero QbarIdeal hQ z hz f hf)
      (fun _Q _hQ z hz i ↦ hbox z (Finset.filter_subset _ _ hz) i)
    simpa only [Chigh, volume, side] using hcallback
  have hcountBound := hcount hHigh
  have hlineBox : ∀ o ∈ active, ∀ z ∈ cell o, ∀ i,
      |integralAffineMap 0 z 1 i| ≤ (H : ℤ) := by
    intro o _ho z hz i
    simp only [integralAffineMap, Pi.zero_apply, Nat.cast_one, one_mul, zero_add]
    have hi : ((z i).natAbs : ℤ) ≤ (H : ℤ) := by
      exact_mod_cast hbox z (Finset.filter_subset _ _ hz) i
    simpa only [Int.natCast_natAbs] using hi
  have hlineBound := hline g c hc hdegree htop G₀
    (d - 1 + blockDegree root) Lroot hG₀data.1 hG₀data.2.1 hrootCap
    degree
    (fun QbarIdeal hQ ↦
      ⟨(hrootData QbarIdeal hQ).1,
        (hrootData QbarIdeal hQ).2.1,
        (hrootData QbarIdeal hQ).2.2.2⟩)
    cell hactiveCard hselected H hHone hlineBox
  let degreeMass := d * Lroot
  have hactiveMass :
      (∑ o ∈ active, rootOptionDegree degree o) ≤ degreeMass := by
    calc
      (∑ o ∈ active, rootOptionDegree degree o) ≤
          ∑ QbarIdeal ∈ finiteEquationMinimalPrimes
            (qbarSurfaceCutEquationFamily sourceEquations G₀),
              degree QbarIdeal :=
        sum_rootOptionDegree_active_le_minimalPrimeDegreeMass
          sourceEquations G₀ cell degree
      _ ≤ d * (d - 1 + blockDegree root) := by
        simpa only [sourceEquations, G₀, root, F] using hrootMass
      _ ≤ degreeMass := by
        dsimp only [degreeMass]
        exact Nat.mul_le_mul_left d hrootCap
  let Xbase : ℝ := (H : ℝ) + 1
  have hXbase : 1 ≤ Xbase := by dsimp only [Xbase]; norm_num
  have hdegreeMassScale : (degreeMass : ℝ) ≤
      Aroot * Xbase ^ rho := by
    have hscale := quantitativePrefixRootDegreeMass_le_commonHeight
      d (d - 1) H H H eta alpha heta.le halpha.le
      (by linarith) (by linarith)
    rw [show eta + alpha = rho by dsimp only [rho]; ring] at hscale
    simpa only [degreeMass, Lroot, Aroot, Xbase, rho] using hscale
  have hactiveScale : (active.card : ℝ) ≤ Aroot * Xbase ^ rho := by
    have hactiveDegree : active.card ≤ degreeMass := by
      simpa only [active, sourceEquations, G₀, cell, degreeMass, Lroot, F]
        using hactiveCard
    exact (by exact_mod_cast hactiveDegree : (active.card : ℝ) ≤ degreeMass).trans
      hdegreeMassScale
  let lowError : ℝ := (cutoff : ℝ) ^ 2 +
    Cpila * (2 * (H : ℝ) + 2) ^ sigma
  have hlowNonneg : 0 ≤ lowError := by
    dsimp only [lowError]
    positivity
  have hlowScale : lowError ≤ Alow * Xbase ^ sigma := by
    have hsigma : 0 ≤ sigma := by dsimp only [sigma]; linarith
    have hXsigma : 1 ≤ Xbase ^ sigma :=
      Real.one_le_rpow hXbase hsigma
    have hsideEq : 2 * (H : ℝ) + 2 = 2 * Xbase := by
      dsimp only [Xbase]
      ring
    have hsidePower : (2 * (H : ℝ) + 2) ^ sigma =
        2 ^ sigma * Xbase ^ sigma := by
      rw [hsideEq, Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2)
        (by positivity : 0 ≤ Xbase)]
    dsimp only [lowError, Alow]
    rw [hsidePower]
    calc
      (cutoff : ℝ) ^ 2 + Cpila * (2 ^ sigma * Xbase ^ sigma) ≤
          (cutoff : ℝ) ^ 2 * Xbase ^ sigma +
            (Cpila * 2 ^ sigma) * Xbase ^ sigma := by
        apply add_le_add
        · simpa only [mul_one] using
            mul_le_mul_of_nonneg_left hXsigma (sq_nonneg (cutoff : ℝ))
        · exact le_of_eq (by ring)
      _ = ((cutoff : ℝ) ^ 2 + Cpila * 2 ^ sigma) *
          Xbase ^ sigma := by ring
  have hhighNonneg : 0 ≤ salberger2023Theorem316CurveError Chigh theta
      ((2 * (H : ℝ) + 2) ^ (3 : ℕ)) := by
    have hsideOne : 1 ≤ side := one_le_two.trans hside
    have hvolumeOne : 1 ≤ side ^ (3 : ℕ) := one_le_pow₀ hsideOne
    have hlog : 0 ≤ Real.log (side ^ (3 : ℕ)) := Real.log_nonneg hvolumeOne
    have hh : 0 ≤ salberger2023Theorem316CurveError Chigh theta
        (side ^ (3 : ℕ)) := by
      unfold salberger2023Theorem316CurveError
      positivity
    simpa only [side] using hh
  have hhighScale : salberger2023Theorem316CurveError Chigh theta
      ((2 * (H : ℝ) + 2) ^ (3 : ℕ)) ≤ Ahigh * Xbase ^ tau := by
    have hsideOne : 1 ≤ side := one_le_two.trans hside
    have hraw := salberger2023Theorem316CurveError_cube_le_power
      Chigh theta side eta hChigh.le htheta.le hsideOne heta
    have hsideEq : side = 2 * Xbase := by
      dsimp only [side, Xbase]
      ring
    have hsidePower : side ^ tau = 2 ^ tau * Xbase ^ tau := by
      rw [hsideEq, Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2)
        (by positivity : 0 ≤ Xbase)]
    dsimp only [tau, Ahigh]
    rw [hsidePower] at hraw
    simpa only [side] using hraw.trans_eq (by ring)
  have herrorBound :
      (∑ o ∈ active,
        persistentRootUniformDegreeSplitError degree cutoff lowError
          Chigh theta ((2 * (H : ℝ) + 2) ^ (3 : ℕ)) o) ≤
        Aerror * Xbase ^ (1 + epsilon) := by
    have hbound := sum_persistentRootUniformDegreeSplitError_le_power_of_scales
      degree active cutoff degreeMass lowError Chigh theta
      ((2 * (H : ℝ) + 2) ^ (3 : ℕ)) Xbase Aroot Alow Ahigh
      rho sigma tau (1 + epsilon) hactiveMass hXbase
      (by dsimp only [Aroot]; positivity)
      (by dsimp only [Alow]; positivity)
      (by dsimp only [Ahigh]; positivity)
      hlowNonneg hhighNonneg hactiveScale hdegreeMassScale hlowScale
      hhighScale
      (by simpa only [rho, sigma] using hlowExponent')
      (by simpa only [rho, tau] using hhighExponent')
      (by simpa only [rho] using hmassExponent)
    simpa only [Aerror] using hbound
  have hrho : 0 ≤ rho := by dsimp only [rho]; linarith
  have htarget : 0 ≤ 1 + epsilon := by linarith
  have hrhoTarget : rho ≤ 1 + epsilon := by
    dsimp only [rho]
    linarith
  have hXtarget : 0 ≤ Xbase ^ (1 + epsilon) := by positivity
  have hdegreeMassSquare : (degreeMass : ℝ) ^ 2 ≤
      Aroot ^ 2 * Xbase ^ (1 + epsilon) := by
    calc
      (degreeMass : ℝ) ^ 2 ≤ (Aroot * Xbase ^ rho) ^ 2 := by
        gcongr
      _ = Aroot ^ 2 * Xbase ^ (2 * rho) := by
        rw [mul_pow]
        congr 1
        calc
          (Xbase ^ rho) ^ (2 : ℕ) =
              Xbase ^ rho * Xbase ^ rho := by ring
          _ = Xbase ^ (rho + rho) :=
            (Real.rpow_add (zero_lt_one.trans_le hXbase) rho rho).symm
          _ = Xbase ^ (2 * rho) := by ring_nf
      _ ≤ Aroot ^ 2 * Xbase ^ (1 + epsilon) := by
        exact mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_exponent_le hXbase hmassExponent)
          (sq_nonneg Aroot)
  have hdegreeMassLinear : (degreeMass : ℝ) ≤
      Aroot * Xbase ^ (1 + epsilon) := by
    exact hdegreeMassScale.trans
      (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hXbase hrhoTarget)
        (by dsimp only [Aroot]; positivity))
  have hHpow : (H : ℝ) ^ (1 + epsilon) ≤
      Xbase ^ (1 + epsilon) := by
    exact Real.rpow_le_rpow (by positivity)
      (by dsimp only [Xbase]; linarith) htarget
  have hlineBound' :
      ((persistentRootLinePointUnion degree active cell).card : ℝ) ≤
        (degreeMass : ℝ) ^ 2 + Aline * (H : ℝ) ^ (1 + epsilon) +
          (degreeMass : ℝ) := by
    simpa only [active, sourceEquations, G₀, cell, F, degreeMass, Lroot]
      using hlineBound
  have hlineScale :
      ((persistentRootLinePointUnion degree active cell).card : ℝ) ≤
        AlineTotal * Xbase ^ (1 + epsilon) := by
    calc
      ((persistentRootLinePointUnion degree active cell).card : ℝ) ≤
          (degreeMass : ℝ) ^ 2 +
            Aline * (H : ℝ) ^ (1 + epsilon) +
              (degreeMass : ℝ) := hlineBound'
      _ ≤ Aroot ^ 2 * Xbase ^ (1 + epsilon) +
            Aline * Xbase ^ (1 + epsilon) +
              Aroot * Xbase ^ (1 + epsilon) := by
        gcongr
      _ = AlineTotal * Xbase ^ (1 + epsilon) := by
        dsimp only [AlineTotal]
        ring
  have hchartDegree :
      (surfaceHypersurfaceFirstChartDehomogenize F).totalDegree ≤ d := by
    rw [firstChart_transformed_homogenize a b g hdegree]
    exact (totalDegree_integral_coordinateEquiv_le a b g).trans hdegree
  have hQcap : (Qcap : ℝ) ≤
      (Cq + 1) * (H : ℝ) ^ delta * (H : ℝ) ^ alpha :=
    ceil_terminal_cap_le H Cq alpha delta hHone hCq halpha.le hdelta.le
  have hRcap : (Rcap : ℝ) ≤ Cr * (H : ℝ) ^ delta :=
    floor_prime_cap_le H Cint delta hHone hCint hdelta
  have hedgeBound := hedge H hHe P depth
    (surfaceHypersurfaceFirstChartDehomogenize F).totalDegree Qcap Rcap
    hchartDegree hcard (hdepth.trans hcard) hQcap hRcap
  have hedgeScale :
      ((PrimeSubsetPrefix.directedEdges P depth).card : ℝ) *
        quantitativePrefixModulusSensitiveEdgeMajorant
          (surfaceHypersurfaceFirstChartDehomogenize F).totalDegree
          depth d (d - 1) H H Qcap Rcap eta alpha ≤
        Aedge * Xbase ^ (1 + epsilon) :=
    hedgeBound.trans (mul_le_mul_of_nonneg_left hHpow hAedge.le)
  have hcountBound' : (X.card : ℝ) ≤
      ((PrimeSubsetPrefix.directedEdges P depth).card : ℝ) *
        quantitativePrefixModulusSensitiveEdgeMajorant
          (surfaceHypersurfaceFirstChartDehomogenize F).totalDegree
          depth d (d - 1) H H Qcap Rcap eta alpha +
      ((persistentRootLinePointUnion degree active cell).card : ℝ) +
      ∑ o ∈ active,
        persistentRootUniformDegreeSplitError degree cutoff lowError
          Chigh theta ((2 * (H : ℝ) + 2) ^ (3 : ℕ)) o := by
    simpa only [active, sourceEquations, G₀, cell, F, lowError, sigma]
      using hcountBound
  have hcombined : (X.card : ℝ) ≤
      (Aedge + AlineTotal + Aerror) * Xbase ^ (1 + epsilon) := by
    calc
      (X.card : ℝ) ≤
          ((PrimeSubsetPrefix.directedEdges P depth).card : ℝ) *
              quantitativePrefixModulusSensitiveEdgeMajorant
                (surfaceHypersurfaceFirstChartDehomogenize F).totalDegree
                depth d (d - 1) H H Qcap Rcap eta alpha +
            ((persistentRootLinePointUnion degree active cell).card : ℝ) +
            ∑ o ∈ active,
              persistentRootUniformDegreeSplitError degree cutoff lowError
                Chigh theta ((2 * (H : ℝ) + 2) ^ (3 : ℕ)) o := hcountBound'
      _ ≤ Aedge * Xbase ^ (1 + epsilon) +
          AlineTotal * Xbase ^ (1 + epsilon) +
          Aerror * Xbase ^ (1 + epsilon) := by gcongr
      _ = (Aedge + AlineTotal + Aerror) *
          Xbase ^ (1 + epsilon) := by ring
  have hXtwo : Xbase ≤ 2 * (H : ℝ) := by
    dsimp only [Xbase]
    have hHreal : (1 : ℝ) ≤ H := by exact_mod_cast hHone
    linarith
  have hXpower : Xbase ^ (1 + epsilon) ≤
      2 ^ (1 + epsilon) * (H : ℝ) ^ (1 + epsilon) := by
    calc
      Xbase ^ (1 + epsilon) ≤ (2 * (H : ℝ)) ^ (1 + epsilon) :=
        Real.rpow_le_rpow (by positivity) hXtwo htarget
      _ = 2 ^ (1 + epsilon) * (H : ℝ) ^ (1 + epsilon) :=
        Real.mul_rpow (by norm_num) (by positivity)
  have hcoefficient : 0 ≤ Aedge + AlineTotal + Aerror := by
    dsimp only [AlineTotal, Aerror, Aroot, Alow, Ahigh]
    positivity
  have hfinal := hcombined.trans
    (mul_le_mul_of_nonneg_left hXpower hcoefficient)
  change (X.card : ℝ) ≤ Atotal * (H : ℝ) ^ (1 + epsilon)
  calc
    (X.card : ℝ) ≤
        ((Aedge + AlineTotal + Aerror) * 2 ^ (1 + epsilon)) *
          (H : ℝ) ^ (1 + epsilon) := by
      simpa only [mul_assoc] using hfinal
    _ ≤ (1 + (Aedge + AlineTotal + Aerror) * 2 ^ (1 + epsilon)) *
          (H : ℝ) ^ (1 + epsilon) := by
      exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    _ = Atotal * (H : ℝ) ^ (1 + epsilon) := by rfl

/-- The proved coordinate, singular-point, and coefficient reductions turn
the internal projected-curve estimate into the literal fixed-leading surface
bound used by the dimension induction. -/
theorem fixed_integral_leading_surface_bounds
    (curveWeil : Literature.AffinePlaneCurveWeil)
    {d : ℕ} (hd : 4 ≤ d) (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    FixedLeadingFormGoodSurfaceCountReduction.FixedIntegralLeadingSurfaceBounds
      d epsilon := by
  exact fixedIntegralLeadingSurfaceBounds_of_normalized_regular_polynomial_height_count
    (by omega : 0 < d) epsilon hepsilon.le
    (normalized_regular_polynomial_height_count curveWeil hd epsilon hepsilon)

end CubicTenVariables.FixedLeadingSurfaceNormalizedRegularCountInternalCurves
