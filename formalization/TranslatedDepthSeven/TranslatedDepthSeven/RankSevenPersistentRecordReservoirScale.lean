import TranslatedDepthSeven.RankSevenPersistentRecordSalbergerPila
import TranslatedDepthSeven.RankSevenRecordPila

/-!
# The reservoir-scale estimate for a persistent rank-seven record

The literal Salberger--Pila theorem for a persistent record retains the
exact divided-packet side

`1 + 4 * surfaceTangentNaturalSide p / record.modulus`.

This file converts only that final factor to the manuscript scale
`T^(2/7)`.  The conversion uses the reservoir lower bound for the actual
record modulus and therefore requires no upper bound on that modulus.  The
auxiliary form, its degree bound, its vanishing on the source-component
packet, and the literal contribution of degree-one curve components are all
retained unchanged.
-/

namespace TranslatedDepthSeven

noncomputable section

open MvPolynomial Published

set_option maxHeartbeats 2000000

/-- Reservoir-scale form of the terminal estimate for one occupied
persistent record.  Zero-dimensional components of the affine intersection
are allowed.  Their degrees, and those of the curve components, come from
the correct Bezout mass `d * degree(G)`.  No upper bound on
`record.modulus` is used. -/
theorem rankSevenPersistentRecordPointCell_card_le_rescaledPila_scale_of_multiplicityOne
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
          C * (p.T ^ (2 / 7 : ℝ)) ^ ((1 / 2 : ℝ) + ε) := by
  obtain ⟨K, hterminal⟩ :=
    rankSevenPersistentRecordPointCell_card_le_rescaledPila_of_multiplicityOne
      hSalberger hPila hBezout p x₀ equations hhomogeneous CF Cchart hP hlower
        markOf record hrecord hnonempty hd hIdimensionDegree hmultiplicity
        ε hε
  obtain ⟨a, G, C₀, hC₀, ha, hGhomogeneous, hGnot, hGzero, hcount⟩ :=
    hterminal
  let C : ℝ :=
    (1 + (1 : ℝ)) * C₀ *
      (2 : ℝ) ^ ((1 / 2 : ℝ) + ε)
  have hC : 0 < C := by
    dsimp only [C]
    positivity
  refine ⟨K, a, G, C, hC, ha, hGhomogeneous, hGnot, hGzero, ?_⟩
  apply hcount.trans
  have hterm := recordPilaNonlinearTerm_le_reservoirScale
    p (hlower record.modulus) hC₀ hε (count := 1)
  have hterm' :
      C₀ * (1 + (4 * surfaceTangentNaturalSide p : ℝ) /
          record.modulus.1) ^ ((1 / 2 : ℝ) + ε) ≤
        C * (p.T ^ (2 / 7 : ℝ)) ^ ((1 / 2 : ℝ) + ε) := by
    simpa only [Nat.cast_one, one_mul, C] using hterm
  exact add_le_add_right hterm' _

end

end TranslatedDepthSeven
