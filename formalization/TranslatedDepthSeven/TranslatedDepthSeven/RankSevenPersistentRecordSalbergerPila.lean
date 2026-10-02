import TranslatedDepthSeven.RankSevenPersistentMultiplicityRecords
import TranslatedDepthSeven.RankSevenResidueSalbergerPila

/-!
# A persistent record as a literal Salberger--Pila packet

This file removes a small but logically important mismatch between the
finite persistent records and the terminal Salberger--Pila theorem.  A
record stores its residue modulo the integer `q`, whereas the terminal
theorem writes the same square-free modulus as the product of
`q.primeFactors`.  The equality of these two integers is part of membership
in the reservoir.  We transport the residue along that equality and prove
that the record cell is a subset of the resulting source-component packet.

No geometric estimate is assumed or proved here.
-/

namespace TranslatedDepthSeven

noncomputable section

open MvPolynomial Published

/-- Transport a residue vector along an equality of its moduli. -/
def castResidueVector {N q r : ℕ} (h : q = r)
    (rho : Fin N → ZMod q) : Fin N → ZMod r :=
  fun i ↦ ZMod.castHom h.symm.dvd (ZMod r) (rho i)

@[simp]
theorem castResidueVector_rfl {N q : ℕ} (rho : Fin N → ZMod q) :
    castResidueVector rfl rho = rho := by
  funext i
  simp [castResidueVector]

/-- Transporting the residue modulus transports the literal packet. -/
theorem integralResiduePacket_castResidueVector
    {N q r : ℕ} (h : q = r) (Z : Finset (IntVector N))
    (rho : Fin N → ZMod q) :
    integralResiduePacket Z (castResidueVector h rho) =
      integralResiduePacket Z rho := by
  cases h
  rw [castResidueVector_rfl]

/-- Occupancy is invariant under the same literal transport. -/
theorem mem_occupiedIntegralResidues_castResidueVector_iff
    {N q r : ℕ} (h : q = r) (Z : Finset (IntVector N))
    (rho : Fin N → ZMod q) :
    castResidueVector h rho ∈ occupiedIntegralResidues r Z ↔
      rho ∈ occupiedIntegralResidues q Z := by
  cases h
  rw [castResidueVector_rfl]

/-- The source component stored in an occupied record is an actual minimal
prime of the source section selected by that record's modulus and residue. -/
theorem persistentRecord_component_mem_sourceSectionMinimalPrimes
    (p : Parameters) (x₀ : IntVector 13)
    (equations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    (C : IntegralDepthSevenJacobianChartIndex equations)
    {P : Finset ℕ} {k markCount : ℕ}
    (record : RankSevenPersistentRecord P k markCount)
    (hrecord : record ∈ occupiedRankSevenPersistentRecords
      p x₀ equations CF C P k markCount) :
    record.component ∈ finiteMinimalPrimes
      (rankSevenSourceSectionIdeal x₀ p.m p.hm equations
        ((selectedRankSevenPacketSectionMatrix p x₀ equations CF C
          record.modulus.1 record.residue).map ((↑) : ℤ → ℚ))) := by
  have hsurface :=
    (mem_occupiedRankSevenPersistentRecords_iff
      p x₀ equations CF C P k markCount record).mp hrecord |>.2
  have hnode :=
    (mem_rankSevenSurfaceNodeComponents_iff
      p x₀ equations CF C record.modulus.1 record.residue
        record.component).mp hsurface |>.1
  simpa [rankSevenNodeComponents, rankSevenNodeEquationIdeal,
    rankSevenSourceSectionEquationsAtResidue,
    rankSevenSourceSectionIdeal] using hnode

/-- After replacing `q` by the product of its prime factors, a persistent
record cell lies in the full residue packet on its stored source component.
The pointwise mark condition is simply forgotten. -/
theorem persistentRecordPointCell_subset_sourceComponentPacket
    (p : Parameters) (x₀ : IntVector 13)
    (equations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    (C : IntegralDepthSevenJacobianChartIndex equations)
    {P : Finset ℕ} {k markCount : ℕ}
    (markOf : IntVector 13 → Fin markCount)
    (record : RankSevenPersistentRecord P k markCount)
    (hproduct : record.modulus.1 =
      primeProduct record.modulus.1.primeFactors) :
    rankSevenPersistentRecordPointCell
        p x₀ equations CF C markOf record ⊆
      rankSevenPacketPointsOnSourceComponent
        (integralResiduePacket
          (depthSevenNormalizedJacobianChartCell p x₀ equations CF C)
          (castResidueVector hproduct record.residue)) record.component := by
  intro z hz
  obtain ⟨hzChart, hzResidue, hzComponent, _hzMark⟩ :=
    (mem_rankSevenPersistentRecordPointCell_iff
      p x₀ equations CF C markOf record z).mp hz
  apply (mem_rankSevenPacketPointsOnSourceComponent_iff _ _ _).mpr
  constructor
  · rw [integralResiduePacket_castResidueVector hproduct]
    exact mem_integralResiduePacket_iff.mpr ⟨hzChart, hzResidue⟩
  · exact fun f hf ↦ hzComponent f hf

/-- Hence every nonempty persistent record cell supplies the nonempty
source-component packet required by the terminal theorem. -/
theorem sourceComponentPacket_nonempty_of_persistentRecordPointCell_nonempty
    (p : Parameters) (x₀ : IntVector 13)
    (equations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    (C : IntegralDepthSevenJacobianChartIndex equations)
    {P : Finset ℕ} {k markCount : ℕ}
    (markOf : IntVector 13 → Fin markCount)
    (record : RankSevenPersistentRecord P k markCount)
    (hproduct : record.modulus.1 =
      primeProduct record.modulus.1.primeFactors)
    (hnonempty : (rankSevenPersistentRecordPointCell
      p x₀ equations CF C markOf record).Nonempty) :
    (rankSevenPacketPointsOnSourceComponent
      (integralResiduePacket
        (depthSevenNormalizedJacobianChartCell p x₀ equations CF C)
        (castResidueVector hproduct record.residue))
      record.component).Nonempty := by
  obtain ⟨z, hz⟩ := hnonempty
  exact ⟨z, persistentRecordPointCell_subset_sourceComponentPacket
    p x₀ equations CF C markOf record hproduct hz⟩

/-- The projective residue point already stored in a persistent record is
literally the canonical point used by Salberger after the modulus is
written as the product of its prime factors. -/
theorem persistentRecordPrimePoint_eq_reservoirAffineProjectivePoint
    {P : Finset ℕ} {k markCount : ℕ}
    (record : RankSevenPersistentRecord P k markCount)
    (hproduct : record.modulus.1 =
      primeProduct record.modulus.1.primeFactors)
    (s : ℕ) (hs : s ∈ record.modulus.1.primeFactors) :
    rankSevenPersistentRecordPrimePoint record s hs =
      reservoirAffineProjectivePoint record.modulus.1.primeFactors
        (castResidueVector hproduct record.residue) ⟨s, hs⟩ := by
  funext i
  refine Fin.cases ?_ (fun j ↦ ?_) i
  · rfl
  · simp only [rankSevenPersistentRecordPrimePoint,
      reservoirAffineProjectivePoint_succ, reservoirPrimeReduction,
      castResidueVector]
    change
      ZMod.castHom (Nat.dvd_of_mem_primeFactors hs) (ZMod s)
          (record.residue j) =
        ((ZMod.castHom (by
            simpa [primeProduct] using
              (Finset.dvd_prod_of_mem id hs)) (ZMod s)).comp
          (ZMod.castHom hproduct.symm.dvd
            (ZMod (primeProduct record.modulus.1.primeFactors))))
          (record.residue j)
    rw [ZMod.castHom_comp]

/-! ## The terminal estimate for one occupied persistent record -/

/-- A nonempty occupied persistent record with multiplicity one at every
prime factor satisfies the literal Salberger--Pila terminal estimate.

The residue prime set, its product identity, the transported residue,
occupancy, source-section minimal-prime membership, the original box, the
divided box, and Salberger's prime-product inequality are all deduced from
the record and the normalized reservoir.  The degrees of the actual
components cut out by the auxiliary form are no longer bounded by a fixed
number chosen in advance: they are obtained from the textbook
surface--hypersurface Bezout mass `d * degree(G)`. -/
theorem rankSevenPersistentRecordPointCell_card_le_rescaledPila_of_multiplicityOne
    (hSalberger : Salberger2007Corollary37)
    (hPila : Pila1995TheoremA)
    (hBezout : StandardAG.ProjectiveSurfaceAffineHypersurfaceBezout)
    (p : Parameters) (x₀ : IntVector 13)
    (equations : Finset (MvPolynomial (Fin 13) ℤ))
    (hhomogeneous : ∀ f ∈ equations, ∃ e : ℕ, f.IsHomogeneous e)
    (CF : ℕ) (Cchart : IntegralDepthSevenJacobianChartIndex equations)
    {P : Finset ℕ} {k markCount : ℕ}
    (hP : ∀ s ∈ P, s.Prime)
    (hlower : ∀ q : ReservoirModulus P k,
      manuscriptReservoirTarget normalizedSurfaceReservoirConstant
        p.T (5 / 7) ≤ q.1)
    (markOf : IntVector 13 → Fin markCount)
    (record : RankSevenPersistentRecord P k markCount)
    (hrecord : record ∈ occupiedRankSevenPersistentRecords
      p x₀ equations CF Cchart P k markCount)
    (hnonempty : (rankSevenPersistentRecordPointCell
      p x₀ equations CF Cchart markOf record).Nonempty)
    {d : ℕ} (hd : 2 ≤ d)
    (hIdimensionDegree : HasProjectiveDimensionDegree
      record.component 2 d)
    (hmultiplicity : ∀ (s : ℕ)
      (hs : s ∈ record.modulus.1.primeFactors),
      HasHilbertSamuelMultiplicityAt
        ((Nat.mem_primeFactors.mp hs).1)
        (projectiveSpecialFiberIdeal record.component)
        (rankSevenPersistentRecordPrimePoint record s hs) 2 1)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ K : ℕ,
      ∃ (a : ℕ) (G : MvPolynomial (Fin 14) ℚ) (C : ℝ),
        0 < C ∧ a ≤ K ∧ G.IsHomogeneous a ∧
        G ∉ record.component ∧
        (∀ z ∈ rankSevenPacketPointsOnSourceComponent
            (integralResiduePacket
              (depthSevenNormalizedJacobianChartCell
                p x₀ equations CF Cchart) record.residue)
            record.component,
          MvPolynomial.eval
            (fun i ↦ (integralAffineChartVector z i : ℚ)) G = 0) ∧
        ((rankSevenPersistentRecordPointCell
          p x₀ equations CF Cchart markOf record).card : ℝ) ≤
          ((finitePointsOnLinearCurveComponents
            (realAffineChartIntersectionIdeal record.component G)
            (rankSevenPacketPointsOnSourceComponent
              (integralResiduePacket
                (depthSevenNormalizedJacobianChartCell
                  p x₀ equations CF Cchart) record.residue)
              record.component)).card : ℝ) +
          C * (1 + (4 * surfaceTangentNaturalSide p : ℝ) /
            record.modulus.1) ^ ((1 / 2 : ℝ) + ε) := by
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
  let Z := depthSevenNormalizedJacobianChartCell
    p x₀ equations CF Cchart
  have hrecordOccupied : record.residue ∈
      occupiedIntegralResidues record.modulus.1 Z :=
    (mem_occupiedRankSevenPersistentRecords_iff
      p x₀ equations CF Cchart P k markCount record).mp hrecord |>.1
  have hrho : rho ∈ occupiedIntegralResidues (primeProduct factors) Z := by
    exact (mem_occupiedIntegralResidues_castResidueVector_iff
      hproduct Z record.residue).2 hrecordOccupied
  let A : Matrix (Fin 4) (Fin 14) ℚ :=
    (selectedRankSevenPacketSectionMatrix p x₀ equations CF Cchart
      record.modulus.1 record.residue).map ((↑) : ℤ → ℚ)
  have hI : record.component ∈ finiteMinimalPrimes
      (rankSevenSourceSectionIdeal x₀ p.m p.hm equations A) := by
    simpa only [A] using
      persistentRecord_component_mem_sourceSectionMinimalPrimes
        p x₀ equations CF Cchart record hrecord
  have hpacketNonempty :
      (rankSevenPacketPointsOnSourceComponent
        (integralResiduePacket Z rho) record.component).Nonempty := by
    exact sourceComponentPacket_nonempty_of_persistentRecordPointCell_nonempty
      p x₀ equations CF Cchart markOf record hproduct hnonempty
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
    linarith
  have hlowerFactors :
      manuscriptReservoirTarget normalizedSurfaceReservoirConstant
        p.T (5 / 7) ≤ primeProduct factors := by
    rw [← hproduct]
    exact hlower record.modulus
  let mu : {s // s ∈ factors} → ℕ := fun _ ↦ 1
  have hmu : ∀ s, 0 < mu s := by
    intro s
    simp [mu]
  have hmultiplicity' : ∀ s,
      HasHilbertSamuelMultiplicityAt (hfactorPrime s.1 s.2)
        (projectiveSpecialFiberIdeal record.component)
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
  have hbox : ∀ z ∈ integralResiduePacket Z rho,
      ∀ i, |(z i : ℝ)| ≤ B := by
    intro z hz i
    exact depthSevenNormalizedChartResiduePacket_realBox
      p x₀ equations CF Cchart factors rho z hz i
  have hquotientBox : ∀ z ∈ integralResiduePacket Z rho, ∀ i,
      |(congruenceDisplacementOrZero (primeProduct factors)
        (integralResiduePacketBase Z rho hrho) z i : ℝ)| < U := by
    intro z hz i
    exact depthSevenNormalizedChartResiduePacket_quotientBox
      p x₀ equations CF Cchart factors hfactorPrime rho hrho z hz i
  obtain ⟨K, hterminal⟩ :=
    rankSevenResiduePacketComponent_card_le_rescaledPila_of_multiplicities
      hSalberger hPila hBezout x₀ p.hm equations hhomogeneous A Z factors
      hfactorPrime rho hrho record.component hI hpacketNonempty
      hIdimensionDegree (by norm_num : (0 : ℝ) < 1 / 100) hε hB hU
      mu hmu hmultiplicity' hSalbergerProduct hbox hquotientBox
  obtain ⟨a, G, C, hC, ha, hGhomogeneous, hGnot, hGzero, hcount⟩ :=
    hterminal
  have hcellSubset : rankSevenPersistentRecordPointCell
      p x₀ equations CF Cchart markOf record ⊆
      rankSevenPacketPointsOnSourceComponent
        (integralResiduePacket Z record.residue) record.component := by
    have hsubset := persistentRecordPointCell_subset_sourceComponentPacket
      p x₀ equations CF Cchart markOf record hproduct
    simpa only [integralResiduePacket_castResidueVector hproduct,
      rho] using hsubset
  have hcellCard :
      ((rankSevenPersistentRecordPointCell
        p x₀ equations CF Cchart markOf record).card : ℝ) ≤
      ((rankSevenPacketPointsOnSourceComponent
        (integralResiduePacket Z record.residue)
          record.component).card : ℝ) := by
    exact_mod_cast Finset.card_le_card hcellSubset
  refine ⟨K, a, G, C, hC, ha, hGhomogeneous, hGnot, ?_, ?_⟩
  · intro z hz
    apply hGzero z
    simpa only [integralResiduePacket_castResidueVector hproduct,
      rho] using hz
  · apply hcellCard.trans
    simpa only [integralResiduePacket_castResidueVector hproduct,
      rho, Z, U, ← hproduct] using hcount

end

end TranslatedDepthSeven
