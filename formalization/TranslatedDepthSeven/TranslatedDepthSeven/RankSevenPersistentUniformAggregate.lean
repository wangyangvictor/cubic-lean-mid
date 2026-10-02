import TranslatedDepthSeven.RankSevenPersistentMultiplicityOneGlobal
import TranslatedDepthSeven.RankSevenRecordOccurrenceScale

/-!
# A coefficient-uniform Salberger--Pila estimate for persistent surfaces

Salberger's auxiliary-degree bound and Pila's coefficient-uniform constant
must be chosen before the translated point, the reservoir, and its finite
record set.  This file records that order of quantifiers explicitly and then
sums the resulting literal record estimates.

The points on degree-one affine curve components are retained as finite sums.
The only estimate on the other components is Pila's theorem, while their
degree mass and number come from the hypersurface case of projective Bezout.
-/

namespace TranslatedDepthSeven

noncomputable section

open MvPolynomial Published

set_option maxHeartbeats 6000000

/-- One Salberger degree bound and one Pila constant work for every retained
persistent record on every degree-`d` surface occurring in the construction.
Both constants are selected before all arithmetic and geometric record data.
-/
theorem exists_uniform_persistentMultiplicityOne_record_scale_constants
    (hSalberger : Salberger2007Corollary37)
    (hPila : Pila1995TheoremA)
    (hBezout : StandardAG.ProjectiveSurfaceAffineHypersurfaceBezout)
    (d : ℕ) (hd : 2 ≤ d) (ε : ℝ) (hε : 0 < ε) :
    ∃ (K : ℕ) (C : ℝ), 0 < C ∧
      ∀ (p : Parameters) (x₀ : IntVector 13)
        (equations : Finset (MvPolynomial (Fin 13) ℤ)),
      (∀ f ∈ equations, ∃ e : ℕ, f.IsHomogeneous e) →
      ∀ (CF : ℕ) (Cchart : IntegralDepthSevenJacobianChartIndex equations)
        (denominator : ℤ) (P : Finset ℕ) (k markCount : ℕ)
        (hP : ∀ s ∈ P, s.Prime)
        (hlower : ∀ q : ReservoirModulus P k,
          manuscriptReservoirTarget normalizedSurfaceReservoirConstant
            p.T (5 / 7) ≤ q.1)
        (I : Ideal (MvPolynomial (Fin 14) ℚ))
        (X : Finset (IntVector 13)),
      X ⊆ rankSevenPersistentSurfaceCell
        p x₀ equations CF Cchart denominator P k hP hlower I →
      ∀ (localEquations : Fin 11 → MvPolynomial (Fin 13) ℤ)
        (selectedVar : Fin 11 → Fin 13)
        (menu : Fin markCount → MvPolynomial (Fin 13) ℤ)
        (markOf : IntVector 13 → Fin markCount)
        (record : RankSevenPersistentRecord P k markCount),
      record ∈ occupiedRankSevenPersistentMultiplicityOneRecords
          p x₀ equations CF Cchart denominator P k hP hlower X markCount
            localEquations selectedVar menu markOf →
      HasProjectiveDimensionDegree I 2 d →
      ∃ (a : ℕ) (G : MvPolynomial (Fin 14) ℚ),
        a ≤ K ∧ G.IsHomogeneous a ∧ G ∉ I ∧
        (∀ z ∈ rankSevenPacketPointsOnSourceComponent
            (integralResiduePacket
              (depthSevenNormalizedJacobianChartCell
                p x₀ equations CF Cchart) record.residue) I,
          MvPolynomial.eval
            (fun i ↦ (integralAffineChartVector z i : ℚ)) G = 0) ∧
        ((rankSevenPersistentRecordPointCell
          p x₀ equations CF Cchart markOf record).card : ℝ) ≤
          ((finitePointsOnLinearCurveComponents
            (realAffineChartIntersectionIdeal I G)
            (rankSevenPacketPointsOnSourceComponent
              (integralResiduePacket
                (depthSevenNormalizedJacobianChartCell
                  p x₀ equations CF Cchart) record.residue) I)).card : ℝ) +
          C * (p.T ^ (2 / 7 : ℝ)) ^ ((1 / 2 : ℝ) + ε) := by
  classical
  obtain ⟨K, hK⟩ := hSalberger 13 d (1 / 100 : ℝ) (by norm_num)
  obtain ⟨C₀, hC₀, hPilaUniform⟩ :=
    exists_uniform_pilaDimZeroOrNonlinearCurveComponents_rescaled_constant
      hPila 13 (d * K) ε hε
  let C : ℝ :=
    (1 + (d * K : ℕ)) * C₀ *
      (2 : ℝ) ^ ((1 / 2 : ℝ) + ε)
  have hC : 0 < C := by
    dsimp only [C]
    positivity
  refine ⟨K, C, hC, ?_⟩
  intro p x₀ equations hhomogeneous CF Cchart denominator P k markCount
    hP hlower I X hX localEquations selectedVar menu markOf record
    hrecord hIdimensionDegree
  obtain ⟨hoccupied, hnonempty⟩ :=
    persistentMultiplicityOneRecord_occupied_and_nonempty
      p x₀ equations CF Cchart denominator P k markCount hP hlower X
        localEquations selectedVar menu markOf record hrecord
  have hcomponent : record.component = I :=
    persistentMultiplicityOneRecord_component_eq_fixedSurface
      p x₀ equations CF Cchart denominator P k markCount hP hlower I X
        hX localEquations selectedVar menu markOf record hrecord
  have hmultiplicity : ∀ (s : ℕ)
      (hs : s ∈ record.modulus.1.primeFactors),
      HasHilbertSamuelMultiplicityAt
        ((Nat.mem_primeFactors.mp hs).1)
        (projectiveSpecialFiberIdeal I)
        (rankSevenPersistentRecordPrimePoint record s hs) 2 1 := by
    intro s hs
    simpa only [hcomponent] using
      persistentMultiplicityOneRecord_factorwise_multiplicityOne
        p x₀ equations CF Cchart denominator P k markCount hP hlower X
          localEquations selectedVar menu markOf record hrecord s hs
  let factors : Finset ℕ := record.modulus.1.primeFactors
  have hfactorSpec := primeFactors_spec_of_mem_modulusReservoir
    hP record.modulus.2
  have hfactorPrime : ∀ s ∈ factors, s.Prime := by
    intro s hs
    exact (Nat.mem_primeFactors.mp hs).1
  have hproduct : record.modulus.1 = primeProduct factors := by
    exact hfactorSpec.2.2.symm
  let rho : Fin 13 → ZMod (primeProduct factors) :=
    castResidueVector hproduct record.residue
  let Z := depthSevenNormalizedJacobianChartCell p x₀ equations CF Cchart
  have hrecordOccupied : record.residue ∈
      occupiedIntegralResidues record.modulus.1 Z :=
    (mem_occupiedRankSevenPersistentRecords_iff
      p x₀ equations CF Cchart P k markCount record).mp hoccupied |>.1
  have hrho : rho ∈ occupiedIntegralResidues (primeProduct factors) Z := by
    exact (mem_occupiedIntegralResidues_castResidueVector_iff
      hproduct Z record.residue).2 hrecordOccupied
  let A : Matrix (Fin 4) (Fin 14) ℚ :=
    (selectedRankSevenPacketSectionMatrix p x₀ equations CF Cchart
      record.modulus.1 record.residue).map ((↑) : ℤ → ℚ)
  have hI : I ∈ finiteMinimalPrimes
      (rankSevenSourceSectionIdeal x₀ p.m p.hm equations A) := by
    have hsource := persistentRecord_component_mem_sourceSectionMinimalPrimes
      p x₀ equations CF Cchart record hoccupied
    simpa only [A, hcomponent] using hsource
  have hpacketNonempty :
      (rankSevenPacketPointsOnSourceComponent
        (integralResiduePacket Z rho) I).Nonempty := by
    have hsource :=
      sourceComponentPacket_nonempty_of_persistentRecordPointCell_nonempty
        p x₀ equations CF Cchart markOf record hproduct hnonempty
    simpa only [hcomponent] using hsource
  obtain ⟨hIprime, hIhom, hIchart, hIirrelevant⟩ :=
    rankSevenSourceComponent_projectiveQualification_of_nonempty
      x₀ p.hm equations hhomogeneous A (integralResiduePacket Z rho)
        I hI hpacketNonempty
  obtain ⟨hIscheme, hinfinity⟩ :=
    homogeneousPrime_salbergerProjectiveHypotheses I hIhom hIprime
      hIirrelevant hIdimensionDegree hIchart
  let B : ℝ := (2 * surfaceTangentNaturalSide p : ℕ)
  let U : ℝ := 1 + (4 * surfaceTangentNaturalSide p : ℝ) /
    primeProduct factors
  have hB : 1 ≤ B := by
    change (1 : ℝ) ≤ (2 * surfaceTangentNaturalSide p : ℕ)
    exact_mod_cast (show 1 ≤ 2 * surfaceTangentNaturalSide p by
      have := one_le_surfaceTangentNaturalSide p
      omega)
  have hprimeProductPos : (0 : ℝ) < primeProduct factors := by
    exact_mod_cast Nat.pos_of_ne_zero (primeProduct_ne_zero hfactorPrime)
  have hU : 1 < U := by
    dsimp only [U]
    have hside : (0 : ℝ) < 4 * surfaceTangentNaturalSide p := by
      exact_mod_cast (show 0 < 4 * surfaceTangentNaturalSide p by
        have := one_le_surfaceTangentNaturalSide p
        omega)
    have : (0 : ℝ) <
        (4 * surfaceTangentNaturalSide p : ℝ) / primeProduct factors :=
      div_pos hside hprimeProductPos
    exact lt_add_of_pos_right 1 this
  have hlowerFactors :
      manuscriptReservoirTarget normalizedSurfaceReservoirConstant
        p.T (5 / 7) ≤ primeProduct factors := by
    rw [← hproduct]
    exact hlower record.modulus
  let mu : {s // s ∈ factors} → ℕ := fun _ ↦ 1
  have hmu : ∀ s, 0 < mu s := by simp [mu]
  have hmultiplicity' : ∀ s,
      HasHilbertSamuelMultiplicityAt (hfactorPrime s.1 s.2)
        (projectiveSpecialFiberIdeal I)
        (reservoirAffineProjectivePoint factors rho s) 2 (mu s) := by
    intro s
    have hs := hmultiplicity s.1 s.2
    rw [persistentRecordPrimePoint_eq_reservoirAffineProjectivePoint
      record hproduct s.1 s.2] at hs
    simpa only [rho, factors, mu] using hs
  have hSalbergerProduct :
      B ^ (1 + (1 / 100 : ℝ)) ≤
        ∏ s : {s // s ∈ factors}, (s.1 : ℝ) ^
          (((d : ℝ) / (mu s : ℝ)) ^ ((2 : ℝ)⁻¹)) := by
    have hsource :=
      normalizedSurfaceReservoir_salbergerProduct_of_two_le_degree
        p factors hfactorPrime hlowerFactors hd
    simpa only [B, mu, Nat.cast_one, div_one,
      primeSubtype_prod_natCast_rpow_eq_primeProduct] using hsource
  obtain ⟨a, G, ha, hGhomogeneous, hGnot, hGsource⟩ :=
    hK 2 (by omega) I hIscheme hinfinity B hB
      {s // s ∈ factors} inferInstance (fun s ↦ s.1)
      (fun s ↦ hfactorPrime s.1 s.2) Subtype.val_injective mu hmu
      (reservoirAffineProjectivePoint factors rho)
      (reservoirAffineProjectivePoint_zero_ne_zero factors hfactorPrime rho)
      hmultiplicity' hSalbergerProduct
  let packet := rankSevenPacketPointsOnSourceComponent
    (integralResiduePacket Z rho) I
  have hbox : ∀ z ∈ integralResiduePacket Z rho,
      ∀ i, |(z i : ℝ)| ≤ B := by
    intro z hz i
    exact depthSevenNormalizedChartResiduePacket_realBox
      p x₀ equations CF Cchart factors rho z hz i
  have hGzero : ∀ z ∈ packet,
      MvPolynomial.eval
        (fun i ↦ (integralAffineChartVector z i : ℚ)) G = 0 := by
    intro z hz
    apply hGsource (integralAffineChartVector z)
    exact integralAffineChartVector_mem_InSalbergerSOne
      I B hB (fun s : {s // s ∈ factors} ↦ s.1)
      (fun s ↦ hfactorPrime s.1 s.2)
      (reservoirAffineProjectivePoint factors rho)
      (reservoirAffineProjectivePoint_zero_ne_zero factors hfactorPrime rho)
      z
      (fun i ↦ hbox z
        ((mem_rankSevenPacketPointsOnSourceComponent_iff
          (integralResiduePacket Z rho) I z).mp hz).1 i)
      ((mem_rankSevenPacketPointsOnSourceComponent_iff
        (integralResiduePacket Z rho) I z).mp hz).2
      (fun s i ↦
        integralResiduePacket_specializesTo_reservoirAffineProjectivePoint
          factors hfactorPrime Z rho
          ((mem_rankSevenPacketPointsOnSourceComponent_iff
            (integralResiduePacket Z rho) I z).mp hz).1 s i)
  let J := realAffineChartIntersectionIdeal I G
  have hJcomponents : ∀ Q ∈ finiteMinimalPrimes J,
      ∃ n e : ℕ, n ≤ 1 ∧ 1 ≤ e ∧ e ≤ d * K ∧
        HasAffineHilbertDimensionDegree Q n e := by
    intro Q hQ
    obtain ⟨n, e, hn, he, heda, hHilbert⟩ :=
      projectiveSurfaceAffineHypersurface_component_degree_le
        hBezout I G hIprime hIhom hIchart hIdimensionDegree
          hGhomogeneous hGnot Q (by simpa only [J] using hQ)
    exact ⟨n, e, hn, he,
      heda.trans (Nat.mul_le_mul_left d ha), hHilbert⟩
  have hcomponentCount : (nonlinearAffineComponents J).card ≤ d * K := by
    apply (Finset.card_filter_le _ _).trans
    have hcount := projectiveSurfaceAffineHypersurface_componentCount_le
      hBezout I G hIprime hIhom hIchart hIdimensionDegree
        hGhomogeneous hGnot
    exact hcount.trans (Nat.mul_le_mul_left d ha)
  have hXJ : ∀ z ∈ packet,
      (fun i ↦ (z i : ℝ)) ∈ affineIdealZeroLocus J := by
    intro z hz
    apply intPoint_mem_realAffineChartIntersectionIdeal
    · intro f hf
      simpa [integralAffineChartVector] using
        ((mem_rankSevenPacketPointsOnSourceComponent_iff
          (integralResiduePacket Z rho) I z).mp hz).2 f hf
    · simpa [integralAffineChartVector] using hGzero z hz
  have hXcong : ∀ z ∈ packet,
      IntVectorCongruent (primeProduct factors) z
        (integralResiduePacketBase Z rho hrho) := by
    intro z hz
    exact intVectorCongruent_of_mem_same_integralResiduePacket
      ((mem_rankSevenPacketPointsOnSourceComponent_iff
        (integralResiduePacket Z rho) I z).mp hz).1
      (integralResiduePacketBase_mem Z rho hrho)
  have hquotientBox : ∀ z ∈ packet, ∀ i,
      |(congruenceDisplacementOrZero (primeProduct factors)
        (integralResiduePacketBase Z rho hrho) z i : ℝ)| < U := by
    intro z hz i
    exact depthSevenNormalizedChartResiduePacket_quotientBox
      p x₀ equations CF Cchart factors hfactorPrime rho hrho z
        ((mem_rankSevenPacketPointsOnSourceComponent_iff
          (integralResiduePacket Z rho) I z).mp hz).1 i
  have hpacketBound := hPilaUniform
    (Nat.pos_of_ne_zero (primeProduct_ne_zero hfactorPrime))
    (integralResiduePacketBase Z rho hrho) J hJcomponents packet hXJ
      hXcong U hU hquotientBox
  have hnonlinearScale := recordPilaNonlinearTerm_le_reservoirScale
    p hlowerFactors hC₀ hε
      (count := (nonlinearAffineComponents J).card)
  have hcoefficient :
      (1 + ((nonlinearAffineComponents J).card : ℝ)) * C₀ *
          (2 : ℝ) ^ ((1 / 2 : ℝ) + ε) ≤ C := by
    dsimp only [C]
    gcongr
  have hscaleNonneg :
      0 ≤ (p.T ^ (2 / 7 : ℝ)) ^ ((1 / 2 : ℝ) + ε) :=
    Real.rpow_nonneg (Real.rpow_nonneg p.T_pos.le _) _
  have htail :
      ((nonlinearAffineComponents J).card : ℝ) * C₀ *
          U ^ ((1 / 2 : ℝ) + ε) ≤
        C * (p.T ^ (2 / 7 : ℝ)) ^ ((1 / 2 : ℝ) + ε) := by
    apply hnonlinearScale.trans
    exact mul_le_mul_of_nonneg_right hcoefficient hscaleNonneg
  have hcellSubset : rankSevenPersistentRecordPointCell
      p x₀ equations CF Cchart markOf record ⊆ packet := by
    have hsubset := persistentRecordPointCell_subset_sourceComponentPacket
      p x₀ equations CF Cchart markOf record hproduct
    simpa only [integralResiduePacket_castResidueVector hproduct,
      rho, hcomponent, packet] using hsubset
  have hcellCard :
      ((rankSevenPersistentRecordPointCell
        p x₀ equations CF Cchart markOf record).card : ℝ) ≤
        (packet.card : ℝ) := by
    exact_mod_cast Finset.card_le_card hcellSubset
  refine ⟨a, G, ha, hGhomogeneous, hGnot, ?_, ?_⟩
  · intro z hz
    apply hGzero z
    simpa only [integralResiduePacket_castResidueVector hproduct,
      rho, packet] using hz
  · apply hcellCard.trans
    apply hpacketBound.trans
    have htail' :
        ((nonlinearAffineComponents J).card : ℝ) * C₀ *
            U ^ ((1 / 2 : ℝ) + ε) ≤
          C * (p.T ^ (2 / 7 : ℝ)) ^ ((1 / 2 : ℝ) + ε) := htail
    simpa only [J, packet, integralResiduePacket_castResidueVector hproduct,
      rho] using add_le_add_right htail' _

/-- Summing the preceding coefficient-uniform estimate over the literal
retained record set gives exactly the exponent
`30/7 + (2/7)(1/2+ε) = 31/7 + (2/7)ε`.

The auxiliary form and its degree are retained for each record, and the
degree-one curve contribution is not estimated here. -/
theorem exists_uniform_persistentMultiplicityOne_sum_constant
    (hSalberger : Salberger2007Corollary37)
    (hPila : Pila1995TheoremA)
    (hBezout : StandardAG.ProjectiveSurfaceAffineHypersurfaceBezout)
    (d : ℕ) (hd : 2 ≤ d) (ε : ℝ) (hε : 0 < ε) :
    ∃ (K : ℕ) (Cgeom : ℝ), 0 < Cgeom ∧
      ∀ {M₀ δ Cres : ℝ},
      0 ≤ M₀ → 0 < δ → 0 ≤ Cres →
      ∀ (p : Parameters) (x₀ : IntVector 13)
        (equations : Finset (MvPolynomial (Fin 13) ℤ)),
      (∀ f ∈ equations, ∃ e : ℕ, f.IsHomogeneous e) →
      ∀ (CF : ℕ) (Cchart : IntegralDepthSevenJacobianChartIndex equations)
        (model : FixedFivefoldResidueModel
          (indexedFinsetFamily (rationalizedEquationFinset equations)))
        (P : Finset ℕ) (k markCount Drecords : ℕ)
        (hP : ∀ s ∈ P, s.Prime)
        (hlower : ∀ q : ReservoirModulus P k,
          manuscriptReservoirTarget normalizedSurfaceReservoirConstant
            p.T (5 / 7) ≤ q.1)
        (I : Ideal (MvPolynomial (Fin 14) ℚ))
        (X : Finset (IntVector 13)),
      X ⊆ rankSevenPersistentSurfaceCell
        p x₀ equations CF Cchart model.denominator P k hP hlower I →
      ∀ (localEquations : Fin 11 → MvPolynomial (Fin 13) ℤ)
        (selectedVar : Fin 11 → Fin 13)
        (menu : Fin markCount → MvPolynomial (Fin 13) ℤ)
        (markOf : IntVector 13 → Fin markCount),
      (∀ z ∈ X,
        ∃ record : RankSevenPersistentRecord P k markCount,
          record ∈ occupiedRankSevenPersistentRecords
            p x₀ equations CF Cchart P k markCount ∧
          record.component = I ∧
          record.mark = markOf z ∧
          (integralResidueVector z : Fin 13 → ZMod record.modulus.1) =
            record.residue ∧
          z ∈ rankSevenPersistentRecordPointCell
            p x₀ equations CF Cchart markOf record ∧
          survivesTwoCertificates record.modulus
            ((p.m : ℤ) * model.denominator)
            (MvPolynomial.eval
              (integralAffineMap x₀ z p.m) Cchart.determinant) ∧
          Nat.Coprime record.modulus.1
            (integralSelectedJacobianChartCertificate
              localEquations selectedVar (menu (markOf z)) z).natAbs ∧
          rankSevenStaticSurfaceLabel
            p x₀ equations CF Cchart model.denominator P k hP hlower
              z record.modulus = some I ∧
          ∀ (s : ℕ) (hs : s ∈ record.modulus.1.primeFactors),
            HasHilbertSamuelMultiplicityAt
              ((Nat.mem_primeFactors.mp hs).1)
              (projectiveSpecialFiberIdeal I)
              (rankSevenPersistentRecordPrimePoint record s hs) 2 1) →
      HasProjectiveDimensionDegree I 2 d →
      (∀ (q : ReservoirModulus P k) (rho : Fin 13 → ZMod q.1),
        rho ∈ occupiedIntegralResidues q.1
            (depthSevenNormalizedJacobianChartCell
              p x₀ equations CF Cchart) →
        (rankSevenSurfaceNodeComponents
          p x₀ equations CF Cchart q.1 rho).card ≤ Drecords) →
      k ≤ reservoirDepth M₀ p.H →
      reservoirSubpowerThreshold M₀
          (model.localConstant : ℝ) δ ≤ p.H →
      ((((modulusReservoir P k).card +
        (modulusReservoirDirectedEdges P k hP).card : ℕ) : ℝ) ≤
          2 * p.H ^ δ) →
      (∀ q : ReservoirModulus P k,
        (q.1 : ℝ) ≤ Cres * p.T ^ (5 / 7 : ℝ) * p.H ^ δ) →
      ∃ (auxiliaryDegree : RankSevenPersistentRecord P k markCount → ℕ)
        (auxiliaryForm : RankSevenPersistentRecord P k markCount →
          MvPolynomial (Fin 14) ℚ),
        (∀ record ∈ occupiedRankSevenPersistentMultiplicityOneRecords
            p x₀ equations CF Cchart model.denominator P k hP hlower X
              markCount localEquations selectedVar menu markOf,
          auxiliaryDegree record ≤ K ∧
          (auxiliaryForm record).IsHomogeneous (auxiliaryDegree record) ∧
          auxiliaryForm record ∉ I ∧
          ∀ z ∈ rankSevenPacketPointsOnSourceComponent
              (integralResiduePacket
                (depthSevenNormalizedJacobianChartCell
                  p x₀ equations CF Cchart) record.residue) I,
            MvPolynomial.eval
              (fun i ↦ (integralAffineChartVector z i : ℚ))
              (auxiliaryForm record) = 0) ∧
        ((X.card : ℝ) ≤
          (∑ record ∈ occupiedRankSevenPersistentMultiplicityOneRecords
              p x₀ equations CF Cchart model.denominator P k hP hlower X
                markCount localEquations selectedVar menu markOf,
            ((finitePointsOnLinearCurveComponents
              (realAffineChartIntersectionIdeal I (auxiliaryForm record))
              (rankSevenPacketPointsOnSourceComponent
                (integralResiduePacket
                  (depthSevenNormalizedJacobianChartCell
                    p x₀ equations CF Cchart) record.residue) I)).card : ℝ)) +
          (Cgeom * Cres ^ 6 * (Drecords * markCount)) *
            p.T ^ (31 / 7 + (2 / 7) * ε : ℝ) * p.H ^ (8 * δ)) := by
  classical
  obtain ⟨K, Crecord, hCrecord, huniform⟩ :=
    exists_uniform_persistentMultiplicityOne_record_scale_constants
      hSalberger hPila hBezout d hd ε hε
  refine ⟨K, 2 * Crecord, by positivity, ?_⟩
  intro M₀ δ Cres hM₀ hδ hCres p x₀ equations hhomogeneous CF Cchart
    model P k markCount Drecords hP hlower I X hX localEquations
    selectedVar menu markOf hrecords hIdimensionDegree hcomponents hk hH
    hfamily hupper
  let R : Finset (RankSevenPersistentRecord P k markCount) :=
    occupiedRankSevenPersistentMultiplicityOneRecords
      p x₀ equations CF Cchart model.denominator P k hP hlower X markCount
        localEquations selectedVar menu markOf
  have hperRecord : ∀ record : RankSevenPersistentRecord P k markCount,
      ∃ (a : ℕ) (G : MvPolynomial (Fin 14) ℚ),
        record ∈ R →
          a ≤ K ∧ G.IsHomogeneous a ∧ G ∉ I ∧
          (∀ z ∈ rankSevenPacketPointsOnSourceComponent
              (integralResiduePacket
                (depthSevenNormalizedJacobianChartCell
                  p x₀ equations CF Cchart) record.residue) I,
            MvPolynomial.eval
              (fun i ↦ (integralAffineChartVector z i : ℚ)) G = 0) ∧
          ((rankSevenPersistentRecordPointCell
            p x₀ equations CF Cchart markOf record).card : ℝ) ≤
            ((finitePointsOnLinearCurveComponents
              (realAffineChartIntersectionIdeal I G)
              (rankSevenPacketPointsOnSourceComponent
                (integralResiduePacket
                  (depthSevenNormalizedJacobianChartCell
                    p x₀ equations CF Cchart) record.residue) I)).card : ℝ) +
            Crecord *
              (p.T ^ (2 / 7 : ℝ)) ^ ((1 / 2 : ℝ) + ε) := by
    intro record
    by_cases hrecord : record ∈ R
    · obtain ⟨a, G, hdata⟩ := huniform p x₀ equations hhomogeneous CF
        Cchart model.denominator P k markCount hP hlower I X hX
        localEquations selectedVar menu markOf record (by
          simpa only [R] using hrecord) hIdimensionDegree
      exact ⟨a, G, fun _ ↦ hdata⟩
    · exact ⟨0, 0, fun h ↦ (hrecord h).elim⟩
  choose auxiliaryDegree auxiliaryForm hdata using hperRecord
  have hauxiliary : ∀ record ∈ R,
      auxiliaryDegree record ≤ K ∧
      (auxiliaryForm record).IsHomogeneous (auxiliaryDegree record) ∧
      auxiliaryForm record ∉ I ∧
      ∀ z ∈ rankSevenPacketPointsOnSourceComponent
          (integralResiduePacket
            (depthSevenNormalizedJacobianChartCell
              p x₀ equations CF Cchart) record.residue) I,
        MvPolynomial.eval
          (fun i ↦ (integralAffineChartVector z i : ℚ))
          (auxiliaryForm record) = 0 := by
    intro record hrecord
    have h := (hdata record) hrecord
    exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩
  have hcoverNat : X.card ≤ ∑ record ∈ R,
      (rankSevenPersistentRecordPointCell
        p x₀ equations CF Cchart markOf record).card := by
    simpa only [R] using
      card_finitePointSet_le_sum_persistentMultiplicityOneRecordCells
        p x₀ equations CF Cchart model.denominator P k markCount hP hlower I X
          hX localEquations selectedVar menu markOf hrecords
  have hcover : (X.card : ℝ) ≤ ∑ record ∈ R,
      ((rankSevenPersistentRecordPointCell
        p x₀ equations CF Cchart markOf record).card : ℝ) := by
    exact_mod_cast hcoverNat
  let linearContribution := fun
      (record : RankSevenPersistentRecord P k markCount) ↦
    ((finitePointsOnLinearCurveComponents
      (realAffineChartIntersectionIdeal I (auxiliaryForm record))
      (rankSevenPacketPointsOnSourceComponent
        (integralResiduePacket
          (depthSevenNormalizedJacobianChartCell
            p x₀ equations CF Cchart) record.residue) I)).card : ℝ)
  let scale : ℝ :=
    (p.T ^ (2 / 7 : ℝ)) ^ ((1 / 2 : ℝ) + ε)
  have hsumPointwise :
      (∑ record ∈ R,
        ((rankSevenPersistentRecordPointCell
          p x₀ equations CF Cchart markOf record).card : ℝ)) ≤
        (∑ record ∈ R, linearContribution record) +
          (R.card : ℝ) * (Crecord * scale) := by
    calc
      (∑ record ∈ R,
        ((rankSevenPersistentRecordPointCell
          p x₀ equations CF Cchart markOf record).card : ℝ)) ≤
          ∑ record ∈ R,
            (linearContribution record + Crecord * scale) := by
        apply Finset.sum_le_sum
        intro record hrecord
        exact ((hdata record) hrecord).2.2.2.2
      _ = (∑ record ∈ R, linearContribution record) +
          (R.card : ℝ) * (Crecord * scale) := by
        simp [Finset.sum_add_distrib]
  have hrecordMass : (R.card : ℝ) ≤
      2 * Cres ^ 6 * (Drecords * markCount) *
        p.T ^ (30 / 7 : ℝ) * p.H ^ (8 * δ) := by
    simpa only [R] using
      card_occupiedRankSevenPersistentMultiplicityOneRecords_cast_le_scale
        hM₀ hδ hCres p x₀ equations CF Cchart model P k markCount
          Drecords hP hlower X localEquations selectedVar menu markOf
          hcomponents hk hH hfamily hupper
  have hscaleNonneg : 0 ≤ Crecord * scale := by
    dsimp only [scale]
    exact mul_nonneg hCrecord.le
      (Real.rpow_nonneg (Real.rpow_nonneg p.T_pos.le _) _)
  have hmassTimes : (R.card : ℝ) * (Crecord * scale) ≤
      (2 * Cres ^ 6 * (Drecords * markCount) *
        p.T ^ (30 / 7 : ℝ) * p.H ^ (8 * δ)) *
          (Crecord * scale) :=
    mul_le_mul_of_nonneg_right hrecordMass hscaleNonneg
  have hpower :
      p.T ^ (30 / 7 : ℝ) *
          (p.T ^ (2 / 7 : ℝ)) ^ ((1 / 2 : ℝ) + ε) =
        p.T ^ (31 / 7 + (2 / 7) * ε : ℝ) := by
    rw [← Real.rpow_mul p.T_pos.le, ← Real.rpow_add p.T_pos]
    congr 1
    ring
  refine ⟨auxiliaryDegree, auxiliaryForm, ?_, ?_⟩
  · simpa only [R] using hauxiliary
  · apply hcover.trans
    apply hsumPointwise.trans
    calc
      (∑ record ∈ R, linearContribution record) +
          (R.card : ℝ) * (Crecord * scale) ≤
        (∑ record ∈ R, linearContribution record) +
          (2 * Cres ^ 6 * (Drecords * markCount) *
            p.T ^ (30 / 7 : ℝ) * p.H ^ (8 * δ)) *
              (Crecord * scale) := add_le_add_right hmassTimes _
      _ = (∑ record ∈ R, linearContribution record) +
          ((2 * Crecord) * Cres ^ 6 * (Drecords * markCount)) *
            p.T ^ (31 / 7 + (2 / 7) * ε : ℝ) * p.H ^ (8 * δ) := by
        dsimp only [scale]
        rw [← hpower]
        ring
      _ =
        (∑ record ∈ occupiedRankSevenPersistentMultiplicityOneRecords
            p x₀ equations CF Cchart model.denominator P k hP hlower X
              markCount localEquations selectedVar menu markOf,
          ((finitePointsOnLinearCurveComponents
            (realAffineChartIntersectionIdeal I (auxiliaryForm record))
            (rankSevenPacketPointsOnSourceComponent
              (integralResiduePacket
                (depthSevenNormalizedJacobianChartCell
                  p x₀ equations CF Cchart) record.residue) I)).card : ℝ)) +
        ((2 * Crecord) * Cres ^ 6 * (Drecords * markCount)) *
          p.T ^ (31 / 7 + (2 / 7) * ε : ℝ) * p.H ^ (8 * δ) := by
        rfl

end

end TranslatedDepthSeven
