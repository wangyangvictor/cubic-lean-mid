import TranslatedDepthSeven.RankSevenResidueMultiplicityOne
import TranslatedDepthSeven.ResiduePacketPilaDimensionZeroOrCurve
import TranslatedDepthSeven.NormalizedReservoirQuotientSide
import TranslatedDepthSeven.ProjectiveSurfaceAffineHypersurfaceBezout

/-!
# Salberger followed by Pila on the divided rank-seven packet

The Salberger determinant step is applied in the original normalized
coordinates, so its height parameter is `B`.  Once its auxiliary form has
cut a source surface into curves, each literal residue packet is divided by
its square-free modulus before Pila is applied.  The latter therefore sees
the smaller side `U`, not `B`.  If Salberger chooses an auxiliary degree
`k ≤ K`, projective Bezout supplies total component-degree mass `d * k`,
and hence the coefficient-uniform Pila bound is invoked only up to the
honest degree bound `d * K`.
-/

namespace TranslatedDepthSeven

noncomputable section

open MvPolynomial Published

attribute [local instance] MvPolynomial.gradedAlgebra

set_option maxHeartbeats 2000000

/-- The normalized surface reservoir is already large enough for
Salberger's prime-product condition on every degree-at-least-eight surface.
The deliberately generous fixed reservoir constant lets us take the fixed
auxiliary epsilon `1/2`; no asymptotic prime-product comparison remains. -/
theorem normalizedSurfaceReservoir_salbergerProduct
    (p : Parameters) (P : Finset ℕ)
    (hlower : manuscriptReservoirTarget normalizedSurfaceReservoirConstant
      p.T (5 / 7) ≤ primeProduct P)
    {d : ℕ} (hd : 8 ≤ d) :
    (((2 * surfaceTangentNaturalSide p : ℕ) : ℝ) ^
        (1 + (1 / 2 : ℝ))) ≤
      (primeProduct P : ℝ) ^
        (((d : ℝ) / (1 : ℝ)) ^ ((2 : ℝ)⁻¹)) := by
  have hT : (1 : ℝ) ≤ p.T := p.one_le_T
  have hTnonneg : 0 ≤ p.T := hT.trans' zero_le_one
  have hB : ((2 * surfaceTangentNaturalSide p : ℕ) : ℝ) ≤
      6 * p.T := by
    have hside := surfaceTangentNaturalSide_cast_le_three_mul p
    change (surfaceTangentNaturalSide p : ℝ) ≤ 3 * p.T at hside
    norm_num only [Nat.cast_mul, Nat.cast_ofNat]
    linarith
  have hconstant : (6 : ℝ) ≤ normalizedSurfaceReservoirConstant := by
    norm_num [normalizedSurfaceReservoirConstant, tangentReservoirConstant,
      tangentCoordinateConstant, Nat.factorial]
  have hqtarget : normalizedSurfaceReservoirConstant * p.T ^ (5 / 7 : ℝ) ≤
      (primeProduct P : ℝ) := by
    calc
      normalizedSurfaceReservoirConstant * p.T ^ (5 / 7 : ℝ) ≤
          manuscriptReservoirTarget normalizedSurfaceReservoirConstant
            p.T (5 / 7) :=
        manuscriptReservoirTarget_cast_lower _ _ _
      _ ≤ (primeProduct P : ℝ) := by exact_mod_cast hlower
  have hqLower : 6 * p.T ^ (5 / 7 : ℝ) ≤
      (primeProduct P : ℝ) := by
    exact (mul_le_mul_of_nonneg_right hconstant
      (Real.rpow_nonneg hTnonneg _)).trans hqtarget
  have hqOne : (1 : ℝ) ≤ primeProduct P := by
    have hscale : 1 ≤ p.T ^ (5 / 7 : ℝ) :=
      Real.one_le_rpow hT (by norm_num)
    have : (1 : ℝ) ≤ 6 * p.T ^ (5 / 7 : ℝ) := by nlinarith
    exact this.trans hqLower
  have hbasePower :
      (6 * p.T : ℝ) ^ (3 / 2 : ℝ) ≤
        (6 * p.T ^ (5 / 7 : ℝ)) ^ (5 / 2 : ℝ) := by
    rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 6) hTnonneg,
      Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 6)
        (Real.rpow_nonneg hTnonneg _), ← Real.rpow_mul hTnonneg]
    have hsix : (6 : ℝ) ^ (3 / 2 : ℝ) ≤
        6 ^ (5 / 2 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
    have hTPower : p.T ^ (3 / 2 : ℝ) ≤
        p.T ^ ((5 / 7 : ℝ) * (5 / 2 : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le hT (by norm_num)
    exact mul_le_mul hsix hTPower (Real.rpow_nonneg hTnonneg _)
      (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 6) _)
  have hBPower :
      (((2 * surfaceTangentNaturalSide p : ℕ) : ℝ) ^
          (3 / 2 : ℝ)) ≤
        (primeProduct P : ℝ) ^ (5 / 2 : ℝ) := by
    calc
      (((2 * surfaceTangentNaturalSide p : ℕ) : ℝ) ^
          (3 / 2 : ℝ)) ≤
          (6 * p.T : ℝ) ^ (3 / 2 : ℝ) :=
        Real.rpow_le_rpow (by positivity) hB (by norm_num)
      _ ≤ (6 * p.T ^ (5 / 7 : ℝ)) ^ (5 / 2 : ℝ) := hbasePower
      _ ≤ (primeProduct P : ℝ) ^ (5 / 2 : ℝ) :=
        Real.rpow_le_rpow (by positivity) hqLower (by norm_num)
  have hdegree : (5 / 2 : ℝ) ≤ Real.sqrt (d : ℝ) := by
    apply Real.le_sqrt_of_sq_le
    have hdreal : (8 : ℝ) ≤ d := by exact_mod_cast hd
    norm_num
    linarith
  have hqDegree : (primeProduct P : ℝ) ^ (5 / 2 : ℝ) ≤
      (primeProduct P : ℝ) ^ Real.sqrt (d : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hqOne hdegree
  simpa only [show (1 + (1 / 2 : ℝ)) = 3 / 2 by norm_num,
    div_one, inv_eq_one_div, Real.sqrt_eq_rpow] using
      hBPower.trans hqDegree

/-- A useful nonsmooth numerical variant.  If every actual local
multiplicity is at most half the projective degree, the same reservoir
satisfies Salberger's product condition with the fixed epsilon `1/100`.
The rational lower approximation `707/500 < sqrt 2` leaves exactly the
identity `(5/7)(707/500)=101/100` in the power of `T`. -/
theorem normalizedSurfaceReservoir_salbergerProduct_of_twice_mu_le_degree
    (p : Parameters) (P : Finset ℕ)
    (hprime : ∀ s ∈ P, s.Prime)
    (hlower : manuscriptReservoirTarget normalizedSurfaceReservoirConstant
      p.T (5 / 7) ≤ primeProduct P)
    {d : ℕ} (mu : {s // s ∈ P} → ℕ)
    (hmu : ∀ s, 0 < mu s) (hmuDegree : ∀ s, 2 * mu s ≤ d) :
    (((2 * surfaceTangentNaturalSide p : ℕ) : ℝ) ^
        (1 + (1 / 100 : ℝ))) ≤
      ∏ s : {s // s ∈ P}, (s.1 : ℝ) ^
        (((d : ℝ) / (mu s : ℝ)) ^ ((2 : ℝ)⁻¹)) := by
  have hT : (1 : ℝ) ≤ p.T := p.one_le_T
  have hTnonneg : 0 ≤ p.T := hT.trans' zero_le_one
  have hB : ((2 * surfaceTangentNaturalSide p : ℕ) : ℝ) ≤
      6 * p.T := by
    have hside := surfaceTangentNaturalSide_cast_le_three_mul p
    change (surfaceTangentNaturalSide p : ℝ) ≤ 3 * p.T at hside
    norm_num only [Nat.cast_mul, Nat.cast_ofNat]
    linarith
  have hconstant : (6 : ℝ) ≤ normalizedSurfaceReservoirConstant := by
    norm_num [normalizedSurfaceReservoirConstant, tangentReservoirConstant,
      tangentCoordinateConstant, Nat.factorial]
  have hqtarget : normalizedSurfaceReservoirConstant * p.T ^ (5 / 7 : ℝ) ≤
      (primeProduct P : ℝ) := by
    calc
      normalizedSurfaceReservoirConstant * p.T ^ (5 / 7 : ℝ) ≤
          manuscriptReservoirTarget normalizedSurfaceReservoirConstant
            p.T (5 / 7) := manuscriptReservoirTarget_cast_lower _ _ _
      _ ≤ (primeProduct P : ℝ) := by exact_mod_cast hlower
  have hqLower : 6 * p.T ^ (5 / 7 : ℝ) ≤
      (primeProduct P : ℝ) :=
    (mul_le_mul_of_nonneg_right hconstant
      (Real.rpow_nonneg hTnonneg _)).trans hqtarget
  have hscalePower :
      (6 * p.T : ℝ) ^ (101 / 100 : ℝ) ≤
        (6 * p.T ^ (5 / 7 : ℝ)) ^ (707 / 500 : ℝ) := by
    rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 6) hTnonneg,
      Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 6)
        (Real.rpow_nonneg hTnonneg _), ← Real.rpow_mul hTnonneg]
    have hsix : (6 : ℝ) ^ (101 / 100 : ℝ) ≤
        6 ^ (707 / 500 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
    have hpowEq : (5 / 7 : ℝ) * (707 / 500 : ℝ) = 101 / 100 := by
      norm_num
    rw [hpowEq]
    exact mul_le_mul_of_nonneg_right hsix
      (Real.rpow_nonneg hTnonneg _)
  have hBq :
      (((2 * surfaceTangentNaturalSide p : ℕ) : ℝ) ^
          (101 / 100 : ℝ)) ≤
        (primeProduct P : ℝ) ^ (707 / 500 : ℝ) := by
    calc
      (((2 * surfaceTangentNaturalSide p : ℕ) : ℝ) ^
          (101 / 100 : ℝ)) ≤
          (6 * p.T : ℝ) ^ (101 / 100 : ℝ) :=
        Real.rpow_le_rpow (by positivity) hB (by norm_num)
      _ ≤ (6 * p.T ^ (5 / 7 : ℝ)) ^ (707 / 500 : ℝ) :=
        hscalePower
      _ ≤ (primeProduct P : ℝ) ^ (707 / 500 : ℝ) :=
        Real.rpow_le_rpow (by positivity) hqLower (by norm_num)
  have hsqrtTwo : (707 / 500 : ℝ) ≤ Real.sqrt 2 := by
    apply Real.le_sqrt_of_sq_le
    norm_num
  have hterm : ∀ s : {s // s ∈ P},
      (s.1 : ℝ) ^ (707 / 500 : ℝ) ≤
        (s.1 : ℝ) ^
          (((d : ℝ) / (mu s : ℝ)) ^ ((2 : ℝ)⁻¹)) := by
    intro s
    have hmuReal : (0 : ℝ) < mu s := by exact_mod_cast hmu s
    have hratio : (2 : ℝ) ≤ (d : ℝ) / mu s := by
      rw [le_div_iff₀ hmuReal]
      exact_mod_cast hmuDegree s
    have hsqrtRatio : Real.sqrt 2 ≤ Real.sqrt ((d : ℝ) / mu s) :=
      Real.sqrt_le_sqrt hratio
    have hsOne : (1 : ℝ) ≤ s.1 := by
      exact_mod_cast (hprime s.1 s.2).one_le
    apply Real.rpow_le_rpow_of_exponent_le hsOne
    simpa only [inv_eq_one_div, Real.sqrt_eq_rpow] using
      hsqrtTwo.trans hsqrtRatio
  have hproducts :
      (primeProduct P : ℝ) ^ (707 / 500 : ℝ) ≤
        ∏ s : {s // s ∈ P}, (s.1 : ℝ) ^
          (((d : ℝ) / (mu s : ℝ)) ^ ((2 : ℝ)⁻¹)) := by
    rw [← primeSubtype_prod_natCast_rpow_eq_primeProduct]
    apply Finset.prod_le_prod
    · intro s _hs
      exact Real.rpow_nonneg (by positivity) _
    · intro s _hs
      exact hterm s
  simpa only [show (1 + (1 / 100 : ℝ)) = 101 / 100 by norm_num] using
    hBq.trans hproducts

/-- Multiplicity-one specialization valid for every nonlinear surface.

The earlier numerical endpoint used the stronger hypothesis `8 ≤ d` and
the auxiliary Salberger exponent `1/2`.  For a surface component through the
translated join vertex one only knows `2 ≤ d`.  Taking the fixed exponent
`1/100` and using `2 * 1 ≤ d` in the preceding theorem gives exactly the
prime-product inequality needed by Corollary 3.7. -/
theorem normalizedSurfaceReservoir_salbergerProduct_of_two_le_degree
    (p : Parameters) (P : Finset ℕ)
    (hprime : ∀ s ∈ P, s.Prime)
    (hlower : manuscriptReservoirTarget normalizedSurfaceReservoirConstant
      p.T (5 / 7) ≤ primeProduct P)
    {d : ℕ} (hd : 2 ≤ d) :
    (((2 * surfaceTangentNaturalSide p : ℕ) : ℝ) ^
        (1 + (1 / 100 : ℝ))) ≤
      (primeProduct P : ℝ) ^
        (((d : ℝ) / (1 : ℝ)) ^ ((2 : ℝ)⁻¹)) := by
  have h :=
    normalizedSurfaceReservoir_salbergerProduct_of_twice_mu_le_degree
      p P hprime hlower (d := d) (fun _ ↦ 1)
      (fun _ ↦ by norm_num)
      (fun _ ↦ by simpa using hd)
  simpa only [Nat.cast_one, div_one,
    primeSubtype_prod_natCast_rpow_eq_primeProduct] using h

/-- The exact divided-packet side is at most twice the manuscript scale
`T^(2/7)`.  This is the elementary exponent conversion needed after the
rescaled Pila estimate. -/
theorem normalizedResidueQuotientSide_le_two_rpow
    (p : Parameters) (P : Finset ℕ)
    (hlower : manuscriptReservoirTarget normalizedSurfaceReservoirConstant
      p.T (5 / 7) ≤ primeProduct P) :
    1 + (4 * surfaceTangentNaturalSide p : ℝ) / primeProduct P ≤
      2 * p.T ^ (2 / 7 : ℝ) := by
  exact normalizedReservoirQuotientSide_le_two_rpow
    p (primeProduct P) hlower

/-- The honest rank-seven endpoint with the actual local
Hilbert--Samuel multiplicities retained.  This is the form applicable when
the Cramer section is not known to meet the original tangent space
transversally.  Pila is still applied only after dividing the residue
packet by its square-free modulus. -/
theorem rankSevenResiduePacketComponent_card_le_rescaledPila_of_multiplicities
    (hSalberger : Salberger2007Corollary37)
    (hPila : Pila1995TheoremA)
    (hBezout : StandardAG.ProjectiveSurfaceAffineHypersurfaceBezout)
    (x₀ : IntVector 13) {m : ℕ} (hm : 0 < m)
    (equations : Finset (MvPolynomial (Fin 13) ℤ))
    (hhomogeneous : ∀ f ∈ equations, ∃ e : ℕ, f.IsHomogeneous e)
    (A : Matrix (Fin 4) (Fin 14) ℚ)
    (Z : Finset (IntVector 13))
    (P : Finset ℕ) (hprime : ∀ s ∈ P, s.Prime)
    (rho : Fin 13 → ZMod (primeProduct P))
    (hrho : rho ∈ occupiedIntegralResidues (primeProduct P) Z)
    (I : Ideal (MvPolynomial (Fin 14) ℚ))
    (hI : I ∈ finiteMinimalPrimes
      (rankSevenSourceSectionIdeal x₀ m hm equations A))
    (hnonempty :
      (rankSevenPacketPointsOnSourceComponent
        (integralResiduePacket Z rho) I).Nonempty)
    {d : ℕ} (hIdimensionDegree : HasProjectiveDimensionDegree I 2 d)
    {εSalberger εPila B U : ℝ}
    (hεSalberger : 0 < εSalberger) (hεPila : 0 < εPila)
    (hB : 1 ≤ B) (hU : 1 < U)
    (mu : {s // s ∈ P} → ℕ) (hmu : ∀ s, 0 < mu s)
    (hmultiplicity : ∀ s,
      HasHilbertSamuelMultiplicityAt (hprime s.1 s.2)
        (projectiveSpecialFiberIdeal I)
        (reservoirAffineProjectivePoint P rho s) 2 (mu s))
    (hproduct : B ^ (1 + εSalberger) ≤
      ∏ s : {s // s ∈ P}, (s.1 : ℝ) ^
        (((d : ℝ) / (mu s : ℝ)) ^ ((2 : ℝ)⁻¹)))
    (hbox : ∀ z ∈ integralResiduePacket Z rho,
      ∀ i, |(z i : ℝ)| ≤ B)
    (hquotientBox : ∀ z ∈ integralResiduePacket Z rho, ∀ i,
      |(congruenceDisplacementOrZero (primeProduct P)
        (integralResiduePacketBase Z rho hrho) z i : ℝ)| < U) :
    ∃ K : ℕ,
      ∃ (k : ℕ) (G : MvPolynomial (Fin 14) ℚ) (C : ℝ),
        0 < C ∧ k ≤ K ∧ G.IsHomogeneous k ∧ G ∉ I ∧
        (∀ z ∈ rankSevenPacketPointsOnSourceComponent
            (integralResiduePacket Z rho) I,
          MvPolynomial.eval
            (fun i ↦ (integralAffineChartVector z i : ℚ)) G = 0) ∧
        ((rankSevenPacketPointsOnSourceComponent
          (integralResiduePacket Z rho) I).card : ℝ) ≤
          ((finitePointsOnLinearCurveComponents
            (realAffineChartIntersectionIdeal I G)
            (rankSevenPacketPointsOnSourceComponent
              (integralResiduePacket Z rho) I)).card : ℝ) +
          C * U ^ ((1 / 2 : ℝ) + εPila) := by
  classical
  obtain ⟨hIprime, hIhom, hIchart, hIirrelevant⟩ :=
    rankSevenSourceComponent_projectiveQualification_of_nonempty
      x₀ hm equations hhomogeneous A (integralResiduePacket Z rho)
        I hI hnonempty
  obtain ⟨hIscheme, hinfinity⟩ :=
    homogeneousPrime_salbergerProjectiveHypotheses I hIhom hIprime
      hIirrelevant hIdimensionDegree hIchart
  obtain ⟨K, hK⟩ := hSalberger 13 d εSalberger hεSalberger
  obtain ⟨k, G, hk, hGhomogeneous, hGnot, hGsource⟩ :=
    hK 2 (by omega) I hIscheme hinfinity B hB
      {s // s ∈ P} inferInstance (fun s ↦ s.1)
      (fun s ↦ hprime s.1 s.2) Subtype.val_injective mu hmu
      (reservoirAffineProjectivePoint P rho)
      (reservoirAffineProjectivePoint_zero_ne_zero P hprime rho)
      hmultiplicity hproduct
  refine ⟨K, ?_⟩
  let X := rankSevenPacketPointsOnSourceComponent
    (integralResiduePacket Z rho) I
  have hGzero : ∀ z ∈ X,
      MvPolynomial.eval
        (fun i ↦ (integralAffineChartVector z i : ℚ)) G = 0 := by
    intro z hz
    apply hGsource (integralAffineChartVector z)
    exact integralAffineChartVector_mem_InSalbergerSOne
      I B hB (fun s : {s // s ∈ P} ↦ s.1)
      (fun s ↦ hprime s.1 s.2)
      (reservoirAffineProjectivePoint P rho)
      (reservoirAffineProjectivePoint_zero_ne_zero P hprime rho)
      z
      (fun i ↦ hbox z
        ((mem_rankSevenPacketPointsOnSourceComponent_iff
          (integralResiduePacket Z rho) I z).mp hz).1 i)
      ((mem_rankSevenPacketPointsOnSourceComponent_iff
        (integralResiduePacket Z rho) I z).mp hz).2
      (fun s i ↦
        integralResiduePacket_specializesTo_reservoirAffineProjectivePoint
          P hprime Z rho
          ((mem_rankSevenPacketPointsOnSourceComponent_iff
            (integralResiduePacket Z rho) I z).mp hz).1 s i)
  let J := realAffineChartIntersectionIdeal I G
  have hJcomponents : ∀ Q ∈ finiteMinimalPrimes J,
      ∃ n e : ℕ, n ≤ 1 ∧ 1 ≤ e ∧ e ≤ d * K ∧
        HasAffineHilbertDimensionDegree Q n e := by
    intro Q hQ
    obtain ⟨n, e, hn, he, hedk, hHilbert⟩ :=
      projectiveSurfaceAffineHypersurface_component_degree_le
        hBezout I G hIprime hIhom hIchart hIdimensionDegree
          hGhomogeneous hGnot Q (by simpa only [J] using hQ)
    exact ⟨n, e, hn, he,
      hedk.trans (Nat.mul_le_mul_left d hk), hHilbert⟩
  have hXJ : ∀ z ∈ X,
      (fun i ↦ (z i : ℝ)) ∈ affineIdealZeroLocus J := by
    intro z hz
    apply intPoint_mem_realAffineChartIntersectionIdeal
    · intro f hf
      simpa [integralAffineChartVector] using
        ((mem_rankSevenPacketPointsOnSourceComponent_iff
          (integralResiduePacket Z rho) I z).mp hz).2 f hf
    · simpa [integralAffineChartVector] using hGzero z hz
  have hXcong : ∀ z ∈ X,
      IntVectorCongruent (primeProduct P) z
        (integralResiduePacketBase Z rho hrho) := by
    intro z hz
    exact intVectorCongruent_of_mem_same_integralResiduePacket
      ((mem_rankSevenPacketPointsOnSourceComponent_iff
        (integralResiduePacket Z rho) I z).mp hz).1
      (integralResiduePacketBase_mem Z rho hrho)
  have hqpos : 0 < primeProduct P :=
    Nat.pos_of_ne_zero (primeProduct_ne_zero hprime)
  obtain ⟨C₀, hC₀, hcount⟩ :=
    finiteSet_card_le_linearCurveComponents_add_pilaDimZeroOrNonlinearCurveComponents_rescaled
      hPila hqpos εPila hεPila
      (integralResiduePacketBase Z rho hrho) J hJcomponents X hXJ
      hXcong U hU
      (fun z hz i ↦ hquotientBox z
        ((mem_rankSevenPacketPointsOnSourceComponent_iff
          (integralResiduePacket Z rho) I z).mp hz).1 i)
  have hcomponentCount : (nonlinearAffineComponents J).card ≤ d * K := by
    have hfilter : (nonlinearAffineComponents J).card ≤
        (finiteMinimalPrimes J).card := by
      unfold nonlinearAffineComponents
      exact Finset.card_filter_le _ _
    have hBezoutCount : (finiteMinimalPrimes J).card ≤ d * k := by
      simpa only [J] using
        projectiveSurfaceAffineHypersurface_componentCount_le
          hBezout I G hIprime hIhom hIchart hIdimensionDegree
            hGhomogeneous hGnot
    exact hfilter.trans <| hBezoutCount.trans (Nat.mul_le_mul_left d hk)
  let C : ℝ := (1 + (d * K : ℕ)) * C₀
  have hC : 0 < C := by
    dsimp only [C]
    positivity
  have hcoefficient : ((nonlinearAffineComponents J).card : ℝ) * C₀ ≤ C := by
    have hcomponentCountReal :
        ((nonlinearAffineComponents J).card : ℝ) ≤ (d * K : ℕ) := by
      exact_mod_cast hcomponentCount
    calc
      ((nonlinearAffineComponents J).card : ℝ) * C₀ ≤
          (d * K : ℕ) * C₀ :=
        mul_le_mul_of_nonneg_right hcomponentCountReal hC₀.le
      _ ≤ (1 + (d * K : ℕ)) * C₀ := by
        nlinarith only [hC₀]
      _ = C := rfl
  refine ⟨k, G, C, hC, hk, hGhomogeneous, hGnot, hGzero, ?_⟩
  have hcount' := hcount
  simp only [X, J] at hcount' ⊢
  have htail :
      ((nonlinearAffineComponents J).card : ℝ) * C₀ *
          U ^ ((1 / 2 : ℝ) + εPila) ≤
        C * U ^ ((1 / 2 : ℝ) + εPila) :=
    mul_le_mul_of_nonneg_right hcoefficient
      (Real.rpow_nonneg (by positivity) _)
  exact hcount'.trans (add_le_add_right htail _)

/-- The actual source-component estimate with no abstract multiplicity
hypothesis and with Pila applied after the exact packet rescaling. -/
theorem rankSevenResiduePacketComponent_card_le_rescaledPila
    (hSalberger : Salberger2007Corollary37)
    (hPila : Pila1995TheoremA)
    (hBezout : StandardAG.ProjectiveSurfaceAffineHypersurfaceBezout)
    (x₀ : IntVector 13) {m : ℕ} (hm : 0 < m)
    (equations : Finset (MvPolynomial (Fin 13) ℤ))
    (hhomogeneous : ∀ f ∈ equations, ∃ e : ℕ, f.IsHomogeneous e)
    (A : Matrix (Fin 4) (Fin 14) ℚ)
    (Z : Finset (IntVector 13))
    (P : Finset ℕ) (hprime : ∀ s ∈ P, s.Prime)
    (rho : Fin 13 → ZMod (primeProduct P))
    (hrho : rho ∈ occupiedIntegralResidues (primeProduct P) Z)
    (I : Ideal (MvPolynomial (Fin 14) ℚ))
    (hI : I ∈ finiteMinimalPrimes
      (rankSevenSourceSectionIdeal x₀ m hm equations A))
    (hnonempty :
      (rankSevenPacketPointsOnSourceComponent
        (integralResiduePacket Z rho) I).Nonempty)
    {d : ℕ} (hIdimensionDegree : HasProjectiveDimensionDegree I 2 d)
    {εSalberger εPila B U : ℝ}
    (hεSalberger : 0 < εSalberger) (hεPila : 0 < εPila)
    (hB : 1 ≤ B) (hU : 1 < U)
    (localEquations : ∀ s : {s // s ∈ P},
      Fin 11 → MvPolynomial (Fin 13) (ZMod s.1))
    (selectedVar : ∀ _s : {s // s ∈ P}, Fin 11 → Fin 13)
    (hselected : ∀ s, Function.Injective (selectedVar s))
    (u : ∀ s : {s // s ∈ P}, MvPolynomial (Fin 13) (ZMod s.1))
    (hIJ : ∀ s,
      Ideal.span (Set.range (localEquations s)) ≤
        @standardAffineChartIdeal 13 s.1 ⟨hprime s.1 s.2⟩
          (projectiveSpecialFiberIdeal I))
    (hclear : ∀ (s : {s // s ∈ P})
        (f : MvPolynomial (Fin 13) (ZMod s.1)),
      f ∈ @standardAffineChartIdeal 13 s.1 ⟨hprime s.1 s.2⟩
          (projectiveSpecialFiberIdeal I) →
      u s * f ∈ Ideal.span (Set.range (localEquations s)))
    (hu : ∀ s,
      MvPolynomial.aeval
        (@standardAffineChartPoint 13 s.1 ⟨hprime s.1 s.2⟩
          (reservoirAffineProjectivePoint P rho s)) (u s) ≠ 0)
    (hminor : ∀ s,
      MvPolynomial.aeval
        (@standardAffineChartPoint 13 s.1 ⟨hprime s.1 s.2⟩
          (reservoirAffineProjectivePoint P rho s))
        (selectedJacobianDeterminant
          (localEquations s) (selectedVar s)) ≠ 0)
    (hproduct : B ^ (1 + εSalberger) ≤
      (primeProduct P : ℝ) ^
        (((d : ℝ) / (1 : ℝ)) ^ ((2 : ℝ)⁻¹)))
    (hbox : ∀ z ∈ integralResiduePacket Z rho,
      ∀ i, |(z i : ℝ)| ≤ B)
    (hquotientBox : ∀ z ∈ integralResiduePacket Z rho, ∀ i,
      |(congruenceDisplacementOrZero (primeProduct P)
        (integralResiduePacketBase Z rho hrho) z i : ℝ)| < U) :
    ∃ K : ℕ,
      ∃ (k : ℕ) (G : MvPolynomial (Fin 14) ℚ) (C : ℝ),
        0 < C ∧ k ≤ K ∧ G.IsHomogeneous k ∧ G ∉ I ∧
        (∀ z ∈ rankSevenPacketPointsOnSourceComponent
            (integralResiduePacket Z rho) I,
          MvPolynomial.eval
            (fun i ↦ (integralAffineChartVector z i : ℚ)) G = 0) ∧
        ((rankSevenPacketPointsOnSourceComponent
          (integralResiduePacket Z rho) I).card : ℝ) ≤
          ((finitePointsOnLinearCurveComponents
            (realAffineChartIntersectionIdeal I G)
            (rankSevenPacketPointsOnSourceComponent
              (integralResiduePacket Z rho) I)).card : ℝ) +
          C * U ^ ((1 / 2 : ℝ) + εPila) := by
  classical
  obtain ⟨hIprime, hIhom, hIchart, hIirrelevant⟩ :=
    rankSevenSourceComponent_projectiveQualification_of_nonempty
      x₀ hm equations hhomogeneous A (integralResiduePacket Z rho)
        I hI hnonempty
  obtain ⟨hIscheme, hinfinity⟩ :=
    homogeneousPrime_salbergerProjectiveHypotheses I hIhom hIprime
      hIirrelevant hIdimensionDegree hIchart
  have hmultiplicity :=
    rankSevenResiduePacketComponent_multiplicityOne_of_localEquations
      Z P hprime rho I hnonempty localEquations selectedVar hselected u
        hIJ hclear hu hminor
  obtain ⟨K, k, G, hk, hGhomogeneous, hGnot, hGsource⟩ :=
    salberger2007_corollary37_multiplicityOne
      hSalberger hεSalberger I (by omega) hIscheme hinfinity hB
      (fun s : {s // s ∈ P} ↦ s.1)
      (fun s ↦ hprime s.1 s.2) Subtype.val_injective
      (reservoirAffineProjectivePoint P rho)
      (reservoirAffineProjectivePoint_zero_ne_zero P hprime rho)
      hmultiplicity
      (by simpa only [primeSubtype_prod_natCast_rpow_eq_primeProduct]
        using hproduct)
  refine ⟨K, ?_⟩
  let X := rankSevenPacketPointsOnSourceComponent
    (integralResiduePacket Z rho) I
  have hGzero : ∀ z ∈ X,
      MvPolynomial.eval
        (fun i ↦ (integralAffineChartVector z i : ℚ)) G = 0 := by
    intro z hz
    apply hGsource (integralAffineChartVector z)
    exact integralAffineChartVector_mem_InSalbergerSOne
      I B hB (fun s : {s // s ∈ P} ↦ s.1)
      (fun s ↦ hprime s.1 s.2)
      (reservoirAffineProjectivePoint P rho)
      (reservoirAffineProjectivePoint_zero_ne_zero P hprime rho)
      z
      (fun i ↦ hbox z
        ((mem_rankSevenPacketPointsOnSourceComponent_iff
          (integralResiduePacket Z rho) I z).mp hz).1 i)
      ((mem_rankSevenPacketPointsOnSourceComponent_iff
        (integralResiduePacket Z rho) I z).mp hz).2
      (fun s i ↦
        integralResiduePacket_specializesTo_reservoirAffineProjectivePoint
          P hprime Z rho
          ((mem_rankSevenPacketPointsOnSourceComponent_iff
            (integralResiduePacket Z rho) I z).mp hz).1 s i)
  let J := realAffineChartIntersectionIdeal I G
  have hJcomponents : ∀ Q ∈ finiteMinimalPrimes J,
      ∃ n e : ℕ, n ≤ 1 ∧ 1 ≤ e ∧ e ≤ d * K ∧
        HasAffineHilbertDimensionDegree Q n e := by
    intro Q hQ
    obtain ⟨n, e, hn, he, hedk, hHilbert⟩ :=
      projectiveSurfaceAffineHypersurface_component_degree_le
        hBezout I G hIprime hIhom hIchart hIdimensionDegree
          hGhomogeneous hGnot Q (by simpa only [J] using hQ)
    exact ⟨n, e, hn, he,
      hedk.trans (Nat.mul_le_mul_left d hk), hHilbert⟩
  have hXJ : ∀ z ∈ X,
      (fun i ↦ (z i : ℝ)) ∈ affineIdealZeroLocus J := by
    intro z hz
    apply intPoint_mem_realAffineChartIntersectionIdeal
    · intro f hf
      simpa [integralAffineChartVector] using
        ((mem_rankSevenPacketPointsOnSourceComponent_iff
          (integralResiduePacket Z rho) I z).mp hz).2 f hf
    · simpa [integralAffineChartVector] using hGzero z hz
  have hXcong : ∀ z ∈ X,
      IntVectorCongruent (primeProduct P) z
        (integralResiduePacketBase Z rho hrho) := by
    intro z hz
    exact intVectorCongruent_of_mem_same_integralResiduePacket
      ((mem_rankSevenPacketPointsOnSourceComponent_iff
        (integralResiduePacket Z rho) I z).mp hz).1
      (integralResiduePacketBase_mem Z rho hrho)
  have hqpos : 0 < primeProduct P :=
    Nat.pos_of_ne_zero (primeProduct_ne_zero hprime)
  obtain ⟨C₀, hC₀, hcount⟩ :=
    finiteSet_card_le_linearCurveComponents_add_pilaDimZeroOrNonlinearCurveComponents_rescaled
      hPila hqpos εPila hεPila
      (integralResiduePacketBase Z rho hrho) J hJcomponents X hXJ
      hXcong U hU
      (fun z hz i ↦ hquotientBox z
        ((mem_rankSevenPacketPointsOnSourceComponent_iff
          (integralResiduePacket Z rho) I z).mp hz).1 i)
  have hcomponentCount : (nonlinearAffineComponents J).card ≤ d * K := by
    have hfilter : (nonlinearAffineComponents J).card ≤
        (finiteMinimalPrimes J).card := by
      unfold nonlinearAffineComponents
      exact Finset.card_filter_le _ _
    have hBezoutCount : (finiteMinimalPrimes J).card ≤ d * k := by
      simpa only [J] using
        projectiveSurfaceAffineHypersurface_componentCount_le
          hBezout I G hIprime hIhom hIchart hIdimensionDegree
            hGhomogeneous hGnot
    exact hfilter.trans <| hBezoutCount.trans (Nat.mul_le_mul_left d hk)
  let C : ℝ := (1 + (d * K : ℕ)) * C₀
  have hC : 0 < C := by
    dsimp only [C]
    positivity
  have hcoefficient : ((nonlinearAffineComponents J).card : ℝ) * C₀ ≤ C := by
    have hcomponentCountReal :
        ((nonlinearAffineComponents J).card : ℝ) ≤ (d * K : ℕ) := by
      exact_mod_cast hcomponentCount
    calc
      ((nonlinearAffineComponents J).card : ℝ) * C₀ ≤
          (d * K : ℕ) * C₀ :=
        mul_le_mul_of_nonneg_right hcomponentCountReal hC₀.le
      _ ≤ (1 + (d * K : ℕ)) * C₀ := by
        nlinarith only [hC₀]
      _ = C := rfl
  refine ⟨k, G, C, hC, hk, hGhomogeneous, hGnot, hGzero, ?_⟩
  have hcount' := hcount
  simp only [X, J] at hcount' ⊢
  have htail :
      ((nonlinearAffineComponents J).card : ℝ) * C₀ *
          U ^ ((1 / 2 : ℝ) + εPila) ≤
        C * U ^ ((1 / 2 : ℝ) + εPila) :=
    mul_le_mul_of_nonneg_right hcoefficient
      (Real.rpow_nonneg (by positivity) _)
  exact hcount'.trans (add_le_add_right htail _)

/-- Fully numerical specialization to one actual normalized rank-seven
residue packet.  The original Salberger box and the divided Pila box are
deduced from the definitions, and the reservoir lower bound proves the
Salberger product inequality for every nonlinear surface. -/
theorem rankSevenNormalizedResiduePacketComponent_card_le_rescaledPila
    (hSalberger : Salberger2007Corollary37)
    (hPila : Pila1995TheoremA)
    (hBezout : StandardAG.ProjectiveSurfaceAffineHypersurfaceBezout)
    (p : Parameters) (x₀ : IntVector 13)
    (equations : Finset (MvPolynomial (Fin 13) ℤ))
    (hhomogeneous : ∀ f ∈ equations, ∃ e : ℕ, f.IsHomogeneous e)
    (CF : ℕ) (Cchart : IntegralDepthSevenJacobianChartIndex equations)
    (P : Finset ℕ) (hprime : ∀ s ∈ P, s.Prime)
    (hlower : manuscriptReservoirTarget normalizedSurfaceReservoirConstant
      p.T (5 / 7) ≤ primeProduct P)
    (rho : Fin 13 → ZMod (primeProduct P))
    (hrho : rho ∈ occupiedIntegralResidues (primeProduct P)
      (depthSevenNormalizedJacobianChartCell
        p x₀ equations CF Cchart))
    (A : Matrix (Fin 4) (Fin 14) ℚ)
    (I : Ideal (MvPolynomial (Fin 14) ℚ))
    (hI : I ∈ finiteMinimalPrimes
      (rankSevenSourceSectionIdeal x₀ p.m p.hm equations A))
    (hnonempty :
      (rankSevenPacketPointsOnSourceComponent
        (integralResiduePacket
          (depthSevenNormalizedJacobianChartCell
            p x₀ equations CF Cchart) rho) I).Nonempty)
    {d : ℕ} (hd : 2 ≤ d)
    (hIdimensionDegree : HasProjectiveDimensionDegree I 2 d)
    {εPila : ℝ} (hεPila : 0 < εPila)
    (localEquations : ∀ s : {s // s ∈ P},
      Fin 11 → MvPolynomial (Fin 13) (ZMod s.1))
    (selectedVar : ∀ _s : {s // s ∈ P}, Fin 11 → Fin 13)
    (hselected : ∀ s, Function.Injective (selectedVar s))
    (u : ∀ s : {s // s ∈ P}, MvPolynomial (Fin 13) (ZMod s.1))
    (hIJ : ∀ s,
      Ideal.span (Set.range (localEquations s)) ≤
        @standardAffineChartIdeal 13 s.1 ⟨hprime s.1 s.2⟩
          (projectiveSpecialFiberIdeal I))
    (hclear : ∀ (s : {s // s ∈ P})
        (f : MvPolynomial (Fin 13) (ZMod s.1)),
      f ∈ @standardAffineChartIdeal 13 s.1 ⟨hprime s.1 s.2⟩
          (projectiveSpecialFiberIdeal I) →
      u s * f ∈ Ideal.span (Set.range (localEquations s)))
    (hu : ∀ s,
      MvPolynomial.aeval
        (@standardAffineChartPoint 13 s.1 ⟨hprime s.1 s.2⟩
          (reservoirAffineProjectivePoint P rho s)) (u s) ≠ 0)
    (hminor : ∀ s,
      MvPolynomial.aeval
        (@standardAffineChartPoint 13 s.1 ⟨hprime s.1 s.2⟩
          (reservoirAffineProjectivePoint P rho s))
        (selectedJacobianDeterminant
          (localEquations s) (selectedVar s)) ≠ 0) :
    ∃ K : ℕ,
      ∃ (k : ℕ) (G : MvPolynomial (Fin 14) ℚ) (C : ℝ),
        0 < C ∧ k ≤ K ∧ G.IsHomogeneous k ∧ G ∉ I ∧
        (∀ z ∈ rankSevenPacketPointsOnSourceComponent
            (integralResiduePacket
              (depthSevenNormalizedJacobianChartCell
                p x₀ equations CF Cchart) rho) I,
          MvPolynomial.eval
            (fun i ↦ (integralAffineChartVector z i : ℚ)) G = 0) ∧
        ((rankSevenPacketPointsOnSourceComponent
          (integralResiduePacket
            (depthSevenNormalizedJacobianChartCell
              p x₀ equations CF Cchart) rho) I).card : ℝ) ≤
          ((finitePointsOnLinearCurveComponents
            (realAffineChartIntersectionIdeal I G)
            (rankSevenPacketPointsOnSourceComponent
              (integralResiduePacket
                (depthSevenNormalizedJacobianChartCell
                  p x₀ equations CF Cchart) rho) I)).card : ℝ) +
          C * (1 + (4 * surfaceTangentNaturalSide p : ℝ) /
              primeProduct P) ^ ((1 / 2 : ℝ) + εPila) := by
  let Z := depthSevenNormalizedJacobianChartCell
    p x₀ equations CF Cchart
  let B : ℝ := (2 * surfaceTangentNaturalSide p : ℕ)
  let U : ℝ := 1 + (4 * surfaceTangentNaturalSide p : ℝ) /
    primeProduct P
  have hB : 1 ≤ B := by
    change (1 : ℝ) ≤ (2 * surfaceTangentNaturalSide p : ℕ)
    exact_mod_cast (show 1 ≤ 2 * surfaceTangentNaturalSide p by
      have := one_le_surfaceTangentNaturalSide p
      omega)
  have hqpos : (0 : ℝ) < primeProduct P := by
    exact_mod_cast Nat.pos_of_ne_zero (primeProduct_ne_zero hprime)
  have hU : 1 < U := by
    dsimp only [U]
    have hside : (0 : ℝ) < 4 * surfaceTangentNaturalSide p := by
      exact_mod_cast (show 0 < 4 * surfaceTangentNaturalSide p by
        have := one_le_surfaceTangentNaturalSide p
        omega)
    have : (0 : ℝ) <
        (4 * surfaceTangentNaturalSide p : ℝ) / primeProduct P :=
      div_pos hside hqpos
    linarith
  apply rankSevenResiduePacketComponent_card_le_rescaledPila
    hSalberger hPila hBezout x₀ p.hm equations hhomogeneous A Z P hprime rho hrho
      I hI hnonempty hIdimensionDegree (by norm_num : (0 : ℝ) < 1 / 100)
      hεPila hB hU localEquations selectedVar hselected u hIJ hclear hu hminor
  · exact normalizedSurfaceReservoir_salbergerProduct_of_two_le_degree
      p P hprime hlower hd
  · intro z hz i
    exact depthSevenNormalizedChartResiduePacket_realBox
      p x₀ equations CF Cchart P rho z hz i
  · intro z hz i
    exact depthSevenNormalizedChartResiduePacket_quotientBox
      p x₀ equations CF Cchart P hprime rho hrho z hz i

end

end TranslatedDepthSeven
