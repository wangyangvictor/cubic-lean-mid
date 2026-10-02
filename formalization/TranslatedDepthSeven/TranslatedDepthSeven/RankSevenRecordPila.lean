import TranslatedDepthSeven.RankSevenNodeRecordCover
import TranslatedDepthSeven.RankSevenEdgeRecordCover
import TranslatedDepthSeven.ResiduePacketPilaDimensionZeroOrCurve
import TranslatedDepthSeven.RankSevenResidueMultiplicityOne
import TranslatedDepthSeven.NormalizedReservoirQuotientSide

/-!
# Pila's curve bound for the literal node and edge-frontier records

The finite record decomposition retains a residue class modulo the record
modulus, but its point cells are not definitionally `integralResiduePacket`s.
This file supplies that last exact bridge.  The residue equality in a record
cell gives congruence to a chosen point in the occupied residue; division by
the modulus then puts the points in a box of side

`1 + 4 * surfaceTangentNaturalSide p / q`.

The only geometric hypothesis below concerns the actual minimal primes of
the literal real affine-chart ideal: each has dimension zero or one and
degree at most `D`.  Only genuine degree-one curves are retained for the
line analysis.  No point-counting estimate is assumed.
-/

namespace TranslatedDepthSeven

noncomputable section

open MvPolynomial Published

set_option maxHeartbeats 2000000

/-- Every literal reservoir modulus is positive. -/
theorem reservoirModulus_pos
    {P : Finset ℕ} {k : ℕ} (hP : ∀ s ∈ P, s.Prime)
    (q : ReservoirModulus P k) :
    0 < q.1 := by
  obtain ⟨S, hS, hSq⟩ := Finset.mem_image.mp q.2
  have hSsub : S ⊆ P := (Finset.mem_powersetCard.mp hS).1
  have hSprime : ∀ s ∈ S, s.Prime := fun s hs ↦ hP s (hSsub hs)
  rw [← hSq]
  exact Nat.pos_of_ne_zero (primeProduct_ne_zero hSprime)

/-- The real standard affine-chart ideal of a rational projective ideal. -/
def realProjectiveAffineChartIdeal {N : ℕ}
    (I : Ideal (MvPolynomial (Fin (N + 1)) ℚ)) :
    Ideal (MvPolynomial (Fin N) ℝ) :=
  (I.map (MvPolynomial.map (algebraMap ℚ ℝ))).map
    (standardDehomogenizationHom ℝ N)

/-- A rational affine-chart point of `I` is a real point of the literal real
affine-chart ideal. -/
theorem intPoint_mem_realProjectiveAffineChartIdeal
    {N : ℕ} (I : Ideal (MvPolynomial (Fin (N + 1)) ℚ))
    (z : IntVector N)
    (hI : (fun i ↦ (integralAffineChartVector z i : ℚ)) ∈
      affineIdealZeroLocus I) :
    (fun i ↦ (z i : ℝ)) ∈
      affineIdealZeroLocus (realProjectiveAffineChartIdeal I) := by
  change realProjectiveAffineChartIdeal I ≤
    RingHom.ker (MvPolynomial.eval fun i ↦ (z i : ℝ))
  rw [realProjectiveAffineChartIdeal, Ideal.map_le_iff_le_comap,
    Ideal.map_le_iff_le_comap]
  intro f hf
  rw [Ideal.mem_comap, Ideal.mem_comap, RingHom.mem_ker]
  change MvPolynomial.eval (fun i ↦ (z i : ℝ))
    (standardDehomogenizationHom ℝ N
      (MvPolynomial.map (algebraMap ℚ ℝ) f)) = 0
  rw [eval_standardDehomogenizationHom]
  have hzero := hI f hf
  have heval :
      MvPolynomial.eval
          (Fin.cases (1 : ℝ) (fun i ↦ (z i : ℝ)))
          (MvPolynomial.map (algebraMap ℚ ℝ) f) =
        algebraMap ℚ ℝ
          (MvPolynomial.eval
            (fun i ↦ (integralAffineChartVector z i : ℚ)) f) := by
    rw [← MvPolynomial.eval₂_eq_eval_map]
    have hcoordinates :
        (Fin.cases (1 : ℝ) (fun i ↦ (z i : ℝ))) =
          fun i ↦ algebraMap ℚ ℝ
            (integralAffineChartVector z i : ℚ) := by
      funext i
      refine Fin.cases ?_ (fun j ↦ ?_) i <;>
        simp [integralAffineChartVector]
    rw [hcoordinates]
    simpa [MvPolynomial.eval₂_id] using
      (MvPolynomial.eval₂_comp_left (algebraMap ℚ ℝ)
        (RingHom.id ℚ)
        (fun i ↦ (integralAffineChartVector z i : ℚ)) f).symm
  rw [heval, hzero, map_zero]

/-- The real box bound for a normalized chart packet is independent of the
arithmetic nature of its modulus. -/
theorem depthSevenNormalizedChartResiduePacket_realBox_anyModulus
    (p : Parameters) (x₀ : IntVector 13)
    (equations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    (C : IntegralDepthSevenJacobianChartIndex equations)
    (q : ℕ) (rho : Fin 13 → ZMod q) :
    ∀ z ∈ integralResiduePacket
        (depthSevenNormalizedJacobianChartCell p x₀ equations CF C) rho,
      ∀ i, |(z i : ℝ)| ≤ (2 * surfaceTangentNaturalSide p : ℕ) := by
  intro z hz i
  have hnat := depthSevenNormalized_coordinate_le_two_surfaceTangentNaturalSide
    p x₀ equations CF
      ((mem_depthSevenNormalizedJacobianChartCell_iff
        p x₀ equations CF C z).mp
          (mem_integralResiduePacket_iff.mp hz).1).1 i
  have hreal : ((z i).natAbs : ℝ) ≤
      ((2 * surfaceTangentNaturalSide p : ℕ) : ℝ) := by
    exact_mod_cast hnat
  simpa only [Nat.cast_natAbs, Int.cast_abs] using hreal

/-- Exact divided-box estimate for an occupied residue modulo an arbitrary
positive modulus. -/
theorem depthSevenNormalizedChartResiduePacket_quotientBox_anyModulus
    (p : Parameters) (x₀ : IntVector 13)
    (equations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    (C : IntegralDepthSevenJacobianChartIndex equations)
    {q : ℕ} (hq : 0 < q) (rho : Fin 13 → ZMod q)
    (hrho : rho ∈ occupiedIntegralResidues q
      (depthSevenNormalizedJacobianChartCell p x₀ equations CF C)) :
    ∀ z ∈ integralResiduePacket
        (depthSevenNormalizedJacobianChartCell p x₀ equations CF C) rho,
      ∀ i,
        |(congruenceDisplacementOrZero q
          (integralResiduePacketBase
            (depthSevenNormalizedJacobianChartCell p x₀ equations CF C)
            rho hrho) z i : ℝ)| <
          1 + (4 * surfaceTangentNaturalSide p : ℝ) / q := by
  intro z hz i
  let Z := depthSevenNormalizedJacobianChartCell p x₀ equations CF C
  let base := integralResiduePacketBase Z rho hrho
  have hzcong : IntVectorCongruent q z base :=
    intVectorCongruent_of_mem_same_integralResiduePacket hz
      (integralResiduePacketBase_mem Z rho hrho)
  have hzbox : ∀ j, |(z j : ℝ) - 0| ≤
      (2 * surfaceTangentNaturalSide p : ℕ) := by
    intro j
    simpa using depthSevenNormalizedChartResiduePacket_realBox_anyModulus
      p x₀ equations CF C q rho z hz j
  have hbasebox : ∀ j, |(base j : ℝ) - 0| ≤
      (2 * surfaceTangentNaturalSide p : ℕ) := by
    intro j
    simpa [base, Z] using
      depthSevenNormalizedChartResiduePacket_realBox_anyModulus
        p x₀ equations CF C q rho base
          (integralResiduePacketBase_mem Z rho hrho) j
  have hbound := congruenceDisplacementOrZero_coordinate_bound
    hq base z hzcong (center := fun _ ↦ 0)
      (R := (2 * surfaceTangentNaturalSide p : ℕ)) hzbox hbasebox i
  have hrewrite :
      2 * ((2 * surfaceTangentNaturalSide p : ℕ) : ℝ) / (q : ℝ) =
        (4 * surfaceTangentNaturalSide p : ℝ) / q := by
    norm_num
    ring
  rw [hrewrite] at hbound
  linarith

/-- If the record modulus is at most `T`, the exact divided side is bounded
by a fixed multiple of `T/q`. -/
theorem normalizedRecordQuotientSide_le_thirteen_mul_ratio
    (p : Parameters) {q : ℕ} (hq : 0 < q)
    (hqT : (q : ℝ) ≤ p.T) :
    1 + (4 * surfaceTangentNaturalSide p : ℝ) / q ≤
      13 * (p.T / q) := by
  have hqreal : (0 : ℝ) < q := by exact_mod_cast hq
  have hsideRaw := surfaceTangentNaturalSide_cast_le_three_mul p
  change (surfaceTangentNaturalSide p : ℝ) ≤ 3 * p.T at hsideRaw
  have hside : (4 * surfaceTangentNaturalSide p : ℝ) ≤ 12 * p.T := by
    linarith
  have hdiv : (4 * surfaceTangentNaturalSide p : ℝ) / q ≤
      12 * p.T / q :=
    (div_le_div_iff_of_pos_right hqreal).2 hside
  have hdiv' : (4 * surfaceTangentNaturalSide p : ℝ) / q ≤
      12 * (p.T / q) := by
    simpa only [mul_div_assoc] using hdiv
  have hone : (1 : ℝ) ≤ p.T / q := by
    rw [le_div_iff₀ hqreal]
    simpa using hqT
  linarith

/-- The nonlinear Pila term on the exact divided side is absorbed into one
positive coefficient times `(T/q)^(1/2+ε)`. -/
theorem recordPilaNonlinearTerm_le_ratio
    (p : Parameters) {q count : ℕ} (hq : 0 < q)
    (hqT : (q : ℝ) ≤ p.T) {C₀ ε : ℝ}
    (hC₀ : 0 < C₀) (hε : 0 < ε) :
    (count : ℝ) * C₀ *
        (1 + (4 * surfaceTangentNaturalSide p : ℝ) / q) ^
          ((1 / 2 : ℝ) + ε) ≤
      ((1 + (count : ℝ)) * C₀ *
          (13 : ℝ) ^ ((1 / 2 : ℝ) + ε)) *
        (p.T / q) ^ ((1 / 2 : ℝ) + ε) := by
  let α : ℝ := (1 / 2 : ℝ) + ε
  have hα : 0 ≤ α := by dsimp only [α]; linarith
  have hratio : 0 < p.T / (q : ℝ) := by
    exact div_pos p.T_pos (by exact_mod_cast hq)
  have hside := normalizedRecordQuotientSide_le_thirteen_mul_ratio
    p hq hqT
  have hpow :
      (1 + (4 * surfaceTangentNaturalSide p : ℝ) / q) ^ α ≤
        (13 : ℝ) ^ α * (p.T / q) ^ α := by
    calc
      (1 + (4 * surfaceTangentNaturalSide p : ℝ) / q) ^ α ≤
          (13 * (p.T / q)) ^ α :=
        Real.rpow_le_rpow (by positivity) hside hα
      _ = (13 : ℝ) ^ α * (p.T / q) ^ α := by
        rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 13) hratio.le]
  calc
    (count : ℝ) * C₀ *
        (1 + (4 * surfaceTangentNaturalSide p : ℝ) / q) ^ α ≤
        (count : ℝ) * C₀ *
          ((13 : ℝ) ^ α * (p.T / q) ^ α) := by
      exact mul_le_mul_of_nonneg_left hpow
        (mul_nonneg (Nat.cast_nonneg count) hC₀.le)
    _ ≤ (1 + (count : ℝ)) * C₀ *
          ((13 : ℝ) ^ α * (p.T / q) ^ α) := by
      gcongr
      norm_num
    _ = ((1 + (count : ℝ)) * C₀ * (13 : ℝ) ^ α) *
        (p.T / q) ^ α := by ring

/-- The nonlinear Pila term is controlled directly by the manuscript scale
`T^(2/7)` from the reservoir lower bound.  Unlike the ratio form above, this
requires no upper bound on the record modulus. -/
theorem recordPilaNonlinearTerm_le_reservoirScale
    (p : Parameters) {q count : ℕ}
    (hlower : manuscriptReservoirTarget normalizedSurfaceReservoirConstant
      p.T (5 / 7) ≤ q)
    {C₀ ε : ℝ} (hC₀ : 0 < C₀) (hε : 0 < ε) :
    (count : ℝ) * C₀ *
        (1 + (4 * surfaceTangentNaturalSide p : ℝ) / q) ^
          ((1 / 2 : ℝ) + ε) ≤
      ((1 + (count : ℝ)) * C₀ *
          (2 : ℝ) ^ ((1 / 2 : ℝ) + ε)) *
        (p.T ^ (2 / 7 : ℝ)) ^ ((1 / 2 : ℝ) + ε) := by
  let α : ℝ := (1 / 2 : ℝ) + ε
  have hα : 0 ≤ α := by dsimp only [α]; linarith
  have hside := normalizedReservoirQuotientSide_le_two_rpow p q hlower
  have hpow :
      (1 + (4 * surfaceTangentNaturalSide p : ℝ) / q) ^ α ≤
        (2 : ℝ) ^ α * (p.T ^ (2 / 7 : ℝ)) ^ α := by
    calc
      (1 + (4 * surfaceTangentNaturalSide p : ℝ) / q) ^ α ≤
          (2 * p.T ^ (2 / 7 : ℝ)) ^ α :=
        Real.rpow_le_rpow (by positivity) hside hα
      _ = (2 : ℝ) ^ α * (p.T ^ (2 / 7 : ℝ)) ^ α := by
        rw [Real.mul_rpow (by positivity) (Real.rpow_nonneg p.T_pos.le _)]
  calc
    (count : ℝ) * C₀ *
        (1 + (4 * surfaceTangentNaturalSide p : ℝ) / q) ^ α ≤
        (count : ℝ) * C₀ *
          ((2 : ℝ) ^ α * (p.T ^ (2 / 7 : ℝ)) ^ α) := by
      exact mul_le_mul_of_nonneg_left hpow
        (mul_nonneg (Nat.cast_nonneg count) hC₀.le)
    _ ≤ (1 + (count : ℝ)) * C₀ *
          ((2 : ℝ) ^ α * (p.T ^ (2 / 7 : ℝ)) ^ α) := by
      have hcoefficient : (count : ℝ) * C₀ ≤
          (1 + (count : ℝ)) * C₀ := by
        exact mul_le_mul_of_nonneg_right (by norm_num) hC₀.le
      exact mul_le_mul_of_nonneg_right hcoefficient
        (mul_nonneg (Real.rpow_nonneg (by norm_num) _)
          (Real.rpow_nonneg (Real.rpow_nonneg p.T_pos.le _) _))
    _ = ((1 + (count : ℝ)) * C₀ * (2 : ℝ) ^ α) *
        (p.T ^ (2 / 7 : ℝ)) ^ α := by ring

/-- Every point of a non-surface node record lies in its literal occupied
residue packet. -/
theorem mem_integralResiduePacket_of_mem_nonSurfaceNodeRecordPointCell
    (p : Parameters) (x₀ : IntVector 13)
    (equations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    (C : IntegralDepthSevenJacobianChartIndex equations)
    {P : Finset ℕ} {k : ℕ} {q : ReservoirModulus P k}
    (record : RankSevenNonSurfaceNodeRecord q.1)
    {z : IntVector 13}
    (hz : z ∈ rankSevenNonSurfaceNodeRecordPointCell
      p x₀ equations CF C record) :
    z ∈ integralResiduePacket
      (depthSevenNormalizedJacobianChartCell p x₀ equations CF C)
      record.residue := by
  exact (mem_integralResiduePacket_iff.mpr
    ⟨(mem_rankSevenNonSurfaceNodeRecordPointCell_iff
      p x₀ equations CF C record z).mp hz |>.1,
     (mem_rankSevenNonSurfaceNodeRecordPointCell_iff
      p x₀ equations CF C record z).mp hz |>.2.1⟩)

/-- The literal node-record cell is counted after exact division by its
record modulus. -/
theorem rankSevenNonSurfaceNodeRecordPointCell_card_le_rescaledPila
    (hPila : Pila1995TheoremA)
    (p : Parameters) (x₀ : IntVector 13)
    (equations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    (Cchart : IntegralDepthSevenJacobianChartIndex equations)
    {P : Finset ℕ} {k : ℕ} (hP : ∀ s ∈ P, s.Prime)
    (q : ReservoirModulus P k)
    (record : RankSevenNonSurfaceNodeRecord q.1)
    (hrecord : record ∈ occupiedRankSevenNonSurfaceNodeRecords
      p x₀ equations CF Cchart q)
    {D : ℕ}
    (hcomponents : ∀ Q ∈ finiteMinimalPrimes
        (realProjectiveAffineChartIdeal record.component),
      ∃ n d : ℕ, n ≤ 1 ∧ 1 ≤ d ∧ d ≤ D ∧
        HasAffineHilbertDimensionDegree Q n d)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧
      ((rankSevenNonSurfaceNodeRecordPointCell
        p x₀ equations CF Cchart record).card : ℝ) ≤
        ((finitePointsOnLinearCurveComponents
          (realProjectiveAffineChartIdeal record.component)
          (rankSevenNonSurfaceNodeRecordPointCell
            p x₀ equations CF Cchart record)).card : ℝ) +
        ((nonlinearAffineComponents
          (realProjectiveAffineChartIdeal record.component)).card : ℝ) * C *
          (1 + (4 * surfaceTangentNaturalSide p : ℝ) / q.1) ^
            ((1 / 2 : ℝ) + ε) := by
  let Z := depthSevenNormalizedJacobianChartCell
    p x₀ equations CF Cchart
  have hrho : record.residue ∈ occupiedIntegralResidues q.1 Z :=
    (mem_occupiedRankSevenNonSurfaceNodeRecords_iff
      p x₀ equations CF Cchart q record).mp hrecord |>.1
  let base := integralResiduePacketBase Z record.residue hrho
  let U : ℝ := 1 + (4 * surfaceTangentNaturalSide p : ℝ) / q.1
  have hq : 0 < q.1 := reservoirModulus_pos hP q
  have hU : 1 < U := by
    dsimp only [U]
    have hside : (0 : ℝ) < 4 * surfaceTangentNaturalSide p := by
      exact_mod_cast (show 0 < 4 * surfaceTangentNaturalSide p by
        have := one_le_surfaceTangentNaturalSide p
        omega)
    have hqreal : (0 : ℝ) < q.1 := by exact_mod_cast hq
    have : (0 : ℝ) <
        (4 * surfaceTangentNaturalSide p : ℝ) / q.1 :=
      div_pos hside hqreal
    linarith
  apply finiteSet_card_le_linearCurveComponents_add_pilaDimZeroOrNonlinearCurveComponents_rescaled
    hPila hq ε hε base
      (realProjectiveAffineChartIdeal record.component) hcomponents
      (rankSevenNonSurfaceNodeRecordPointCell
        p x₀ equations CF Cchart record)
  · intro z hz
    exact intPoint_mem_realProjectiveAffineChartIdeal record.component z
      ((mem_rankSevenNonSurfaceNodeRecordPointCell_iff
        p x₀ equations CF Cchart record z).mp hz |>.2.2)
  · intro z hz
    exact intVectorCongruent_of_mem_same_integralResiduePacket
      (mem_integralResiduePacket_of_mem_nonSurfaceNodeRecordPointCell
        p x₀ equations CF Cchart record hz)
      (integralResiduePacketBase_mem Z record.residue hrho)
  · exact hU
  · intro z hz i
    exact depthSevenNormalizedChartResiduePacket_quotientBox_anyModulus
      p x₀ equations CF Cchart hq record.residue hrho z
        (mem_integralResiduePacket_of_mem_nonSurfaceNodeRecordPointCell
          p x₀ equations CF Cchart record hz) i

/-- Ratio form of the preceding node-record estimate.  The harmless actual
number of nonlinear components is absorbed into the positive coefficient. -/
theorem rankSevenNonSurfaceNodeRecordPointCell_card_le_rescaledPila_ratio
    (hPila : Pila1995TheoremA)
    (p : Parameters) (x₀ : IntVector 13)
    (equations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    (Cchart : IntegralDepthSevenJacobianChartIndex equations)
    {P : Finset ℕ} {k : ℕ} (hP : ∀ s ∈ P, s.Prime)
    (q : ReservoirModulus P k)
    (hqT : (q.1 : ℝ) ≤ p.T)
    (record : RankSevenNonSurfaceNodeRecord q.1)
    (hrecord : record ∈ occupiedRankSevenNonSurfaceNodeRecords
      p x₀ equations CF Cchart q)
    {D : ℕ}
    (hcomponents : ∀ Q ∈ finiteMinimalPrimes
        (realProjectiveAffineChartIdeal record.component),
      ∃ n d : ℕ, n ≤ 1 ∧ 1 ≤ d ∧ d ≤ D ∧
        HasAffineHilbertDimensionDegree Q n d)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧
      ((rankSevenNonSurfaceNodeRecordPointCell
        p x₀ equations CF Cchart record).card : ℝ) ≤
        ((finitePointsOnLinearCurveComponents
          (realProjectiveAffineChartIdeal record.component)
          (rankSevenNonSurfaceNodeRecordPointCell
            p x₀ equations CF Cchart record)).card : ℝ) +
        C * (p.T / q.1) ^ ((1 / 2 : ℝ) + ε) := by
  obtain ⟨C₀, hC₀, hcount⟩ :=
    rankSevenNonSurfaceNodeRecordPointCell_card_le_rescaledPila
      hPila p x₀ equations CF Cchart hP q record hrecord
        hcomponents ε hε
  let componentCount : ℕ :=
    (nonlinearAffineComponents
      (realProjectiveAffineChartIdeal record.component)).card
  let C : ℝ :=
    (1 + (componentCount : ℝ)) * C₀ *
      (13 : ℝ) ^ ((1 / 2 : ℝ) + ε)
  have hC : 0 < C := by
    dsimp only [C]
    positivity
  refine ⟨C, hC, hcount.trans ?_⟩
  have hterm := recordPilaNonlinearTerm_le_ratio
    p (reservoirModulus_pos hP q) hqT hC₀ hε
      (count := componentCount)
  dsimp only [componentCount, C] at hterm ⊢
  gcongr

/-- Reservoir-scale form of the node-record estimate.  This is the form
used in the final exponent ledger and does not assume `q ≤ T`. -/
theorem rankSevenNonSurfaceNodeRecordPointCell_card_le_rescaledPila_scale
    (hPila : Pila1995TheoremA)
    (p : Parameters) (x₀ : IntVector 13)
    (equations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    (Cchart : IntegralDepthSevenJacobianChartIndex equations)
    {P : Finset ℕ} {k : ℕ} (hP : ∀ s ∈ P, s.Prime)
    (q : ReservoirModulus P k)
    (hlower : manuscriptReservoirTarget normalizedSurfaceReservoirConstant
      p.T (5 / 7) ≤ q.1)
    (record : RankSevenNonSurfaceNodeRecord q.1)
    (hrecord : record ∈ occupiedRankSevenNonSurfaceNodeRecords
      p x₀ equations CF Cchart q)
    {D : ℕ}
    (hcomponents : ∀ Q ∈ finiteMinimalPrimes
        (realProjectiveAffineChartIdeal record.component),
      ∃ n d : ℕ, n ≤ 1 ∧ 1 ≤ d ∧ d ≤ D ∧
        HasAffineHilbertDimensionDegree Q n d)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧
      ((rankSevenNonSurfaceNodeRecordPointCell
        p x₀ equations CF Cchart record).card : ℝ) ≤
        ((finitePointsOnLinearCurveComponents
          (realProjectiveAffineChartIdeal record.component)
          (rankSevenNonSurfaceNodeRecordPointCell
            p x₀ equations CF Cchart record)).card : ℝ) +
        C * (p.T ^ (2 / 7 : ℝ)) ^ ((1 / 2 : ℝ) + ε) := by
  obtain ⟨C₀, hC₀, hcount⟩ :=
    rankSevenNonSurfaceNodeRecordPointCell_card_le_rescaledPila
      hPila p x₀ equations CF Cchart hP q record hrecord
        hcomponents ε hε
  let componentCount : ℕ :=
    (nonlinearAffineComponents
      (realProjectiveAffineChartIdeal record.component)).card
  let C : ℝ :=
    (1 + (componentCount : ℝ)) * C₀ *
      (2 : ℝ) ^ ((1 / 2 : ℝ) + ε)
  have hC : 0 < C := by
    dsimp only [C]
    positivity
  refine ⟨C, hC, hcount.trans ?_⟩
  have hterm := recordPilaNonlinearTerm_le_reservoirScale
    p hlower hC₀ hε (count := componentCount)
  dsimp only [componentCount, C] at hterm ⊢
  gcongr

/-- Every edge-frontier point lies in the literal occupied lcm-residue
packet retained by its record. -/
theorem mem_integralResiduePacket_of_mem_surfaceEdgeFrontierPointCell
    (p : Parameters) (x₀ : IntVector 13)
    (equations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    (C : IntegralDepthSevenJacobianChartIndex equations)
    (P : Finset ℕ) (k : ℕ) {q r : ReservoirModulus P k}
    (record : RankSevenEdgeRecord (Nat.lcm q.1 r.1))
    (L : Ideal (MvPolynomial (Fin 14) ℚ)) {z : IntVector 13}
    (hz : z ∈ rankSevenSurfaceEdgeFrontierPointCell
      p x₀ equations CF C P k record L) :
    z ∈ integralResiduePacket
      (depthSevenNormalizedJacobianChartCell p x₀ equations CF C)
      record.residue := by
  exact mem_integralResiduePacket_iff.mpr
    ⟨(mem_rankSevenSurfaceEdgeFrontierPointCell_iff
      p x₀ equations CF C P k record L z).mp hz |>.1,
     (mem_rankSevenSurfaceEdgeFrontierPointCell_iff
      p x₀ equations CF C P k record L z).mp hz |>.2.1⟩

/-- The literal edge-frontier cell is counted after exact division by its
lcm record modulus. -/
theorem rankSevenSurfaceEdgeFrontierPointCell_card_le_rescaledPila
    (hPila : Pila1995TheoremA)
    (p : Parameters) (x₀ : IntVector 13)
    (equations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    (Cchart : IntegralDepthSevenJacobianChartIndex equations)
    (P : Finset ℕ) (k : ℕ) (hP : ∀ s ∈ P, s.Prime)
    (q r : ReservoirModulus P k)
    (record : RankSevenEdgeRecord (Nat.lcm q.1 r.1))
    (hrecord : record ∈ occupiedRankSevenSurfaceEdgeRecords
      p x₀ equations CF Cchart P k q r hP)
    (L : Ideal (MvPolynomial (Fin 14) ℚ))
    {D : ℕ}
    (hcomponents : ∀ Q ∈ finiteMinimalPrimes
        (realProjectiveAffineChartIdeal L),
      ∃ n d : ℕ, n ≤ 1 ∧ 1 ≤ d ∧ d ≤ D ∧
        HasAffineHilbertDimensionDegree Q n d)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧
      ((rankSevenSurfaceEdgeFrontierPointCell
        p x₀ equations CF Cchart P k record L).card : ℝ) ≤
        ((finitePointsOnLinearCurveComponents
          (realProjectiveAffineChartIdeal L)
          (rankSevenSurfaceEdgeFrontierPointCell
            p x₀ equations CF Cchart P k record L)).card : ℝ) +
        ((nonlinearAffineComponents
          (realProjectiveAffineChartIdeal L)).card : ℝ) * C *
          (1 + (4 * surfaceTangentNaturalSide p : ℝ) /
            Nat.lcm q.1 r.1) ^ ((1 / 2 : ℝ) + ε) := by
  let Z := depthSevenNormalizedJacobianChartCell
    p x₀ equations CF Cchart
  have hrho : record.residue ∈
      occupiedIntegralResidues (Nat.lcm q.1 r.1) Z :=
    (mem_occupiedRankSevenSurfaceEdgeRecords_iff
      p x₀ equations CF Cchart P k q r hP record).mp hrecord |>.2
  let base := integralResiduePacketBase Z record.residue hrho
  let U : ℝ := 1 + (4 * surfaceTangentNaturalSide p : ℝ) /
    Nat.lcm q.1 r.1
  have hq : 0 < q.1 := reservoirModulus_pos hP q
  have hr : 0 < r.1 := reservoirModulus_pos hP r
  have hlcm : 0 < Nat.lcm q.1 r.1 := Nat.lcm_pos hq hr
  have hU : 1 < U := by
    dsimp only [U]
    have hside : (0 : ℝ) < 4 * surfaceTangentNaturalSide p := by
      exact_mod_cast (show 0 < 4 * surfaceTangentNaturalSide p by
        have := one_le_surfaceTangentNaturalSide p
        omega)
    have hlcmreal : (0 : ℝ) < Nat.lcm q.1 r.1 := by
      exact_mod_cast hlcm
    have : (0 : ℝ) <
        (4 * surfaceTangentNaturalSide p : ℝ) / Nat.lcm q.1 r.1 :=
      div_pos hside hlcmreal
    linarith
  apply finiteSet_card_le_linearCurveComponents_add_pilaDimZeroOrNonlinearCurveComponents_rescaled
    hPila hlcm ε hε base (realProjectiveAffineChartIdeal L) hcomponents
      (rankSevenSurfaceEdgeFrontierPointCell
        p x₀ equations CF Cchart P k record L)
  · intro z hz
    exact intPoint_mem_realProjectiveAffineChartIdeal L z
      ((mem_rankSevenSurfaceEdgeFrontierPointCell_iff
        p x₀ equations CF Cchart P k record L z).mp hz |>.2.2)
  · intro z hz
    exact intVectorCongruent_of_mem_same_integralResiduePacket
      (mem_integralResiduePacket_of_mem_surfaceEdgeFrontierPointCell
        p x₀ equations CF Cchart P k record L hz)
      (integralResiduePacketBase_mem Z record.residue hrho)
  · exact hU
  · intro z hz i
    exact depthSevenNormalizedChartResiduePacket_quotientBox_anyModulus
      p x₀ equations CF Cchart hlcm record.residue hrho z
        (mem_integralResiduePacket_of_mem_surfaceEdgeFrontierPointCell
          p x₀ equations CF Cchart P k record L hz) i

/-- Ratio form of the edge-frontier estimate, with the lcm residue modulus
displayed explicitly. -/
theorem rankSevenSurfaceEdgeFrontierPointCell_card_le_rescaledPila_ratio
    (hPila : Pila1995TheoremA)
    (p : Parameters) (x₀ : IntVector 13)
    (equations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    (Cchart : IntegralDepthSevenJacobianChartIndex equations)
    (P : Finset ℕ) (k : ℕ) (hP : ∀ s ∈ P, s.Prime)
    (q r : ReservoirModulus P k)
    (hlcmT : (Nat.lcm q.1 r.1 : ℝ) ≤ p.T)
    (record : RankSevenEdgeRecord (Nat.lcm q.1 r.1))
    (hrecord : record ∈ occupiedRankSevenSurfaceEdgeRecords
      p x₀ equations CF Cchart P k q r hP)
    (L : Ideal (MvPolynomial (Fin 14) ℚ))
    {D : ℕ}
    (hcomponents : ∀ Q ∈ finiteMinimalPrimes
        (realProjectiveAffineChartIdeal L),
      ∃ n d : ℕ, n ≤ 1 ∧ 1 ≤ d ∧ d ≤ D ∧
        HasAffineHilbertDimensionDegree Q n d)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧
      ((rankSevenSurfaceEdgeFrontierPointCell
        p x₀ equations CF Cchart P k record L).card : ℝ) ≤
        ((finitePointsOnLinearCurveComponents
          (realProjectiveAffineChartIdeal L)
          (rankSevenSurfaceEdgeFrontierPointCell
            p x₀ equations CF Cchart P k record L)).card : ℝ) +
        C * (p.T / Nat.lcm q.1 r.1) ^ ((1 / 2 : ℝ) + ε) := by
  obtain ⟨C₀, hC₀, hcount⟩ :=
    rankSevenSurfaceEdgeFrontierPointCell_card_le_rescaledPila
      hPila p x₀ equations CF Cchart P k hP q r record hrecord L
        hcomponents ε hε
  let componentCount : ℕ :=
    (nonlinearAffineComponents (realProjectiveAffineChartIdeal L)).card
  let C : ℝ :=
    (1 + (componentCount : ℝ)) * C₀ *
      (13 : ℝ) ^ ((1 / 2 : ℝ) + ε)
  have hq : 0 < q.1 := reservoirModulus_pos hP q
  have hr : 0 < r.1 := reservoirModulus_pos hP r
  have hlcm : 0 < Nat.lcm q.1 r.1 := Nat.lcm_pos hq hr
  have hC : 0 < C := by
    dsimp only [C]
    positivity
  refine ⟨C, hC, hcount.trans ?_⟩
  have hterm := recordPilaNonlinearTerm_le_ratio
    p hlcm hlcmT hC₀ hε (count := componentCount)
  dsimp only [componentCount, C] at hterm ⊢
  gcongr

/-- Reservoir-scale form of the edge-frontier estimate.  It uses only the
lower bound for the adjacent least common multiple and does not assume that
the lcm is at most `T`. -/
theorem rankSevenSurfaceEdgeFrontierPointCell_card_le_rescaledPila_scale
    (hPila : Pila1995TheoremA)
    (p : Parameters) (x₀ : IntVector 13)
    (equations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    (Cchart : IntegralDepthSevenJacobianChartIndex equations)
    (P : Finset ℕ) (k : ℕ) (hP : ∀ s ∈ P, s.Prime)
    (q r : ReservoirModulus P k)
    (hlower : manuscriptReservoirTarget normalizedSurfaceReservoirConstant
      p.T (5 / 7) ≤ Nat.lcm q.1 r.1)
    (record : RankSevenEdgeRecord (Nat.lcm q.1 r.1))
    (hrecord : record ∈ occupiedRankSevenSurfaceEdgeRecords
      p x₀ equations CF Cchart P k q r hP)
    (L : Ideal (MvPolynomial (Fin 14) ℚ))
    {D : ℕ}
    (hcomponents : ∀ Q ∈ finiteMinimalPrimes
        (realProjectiveAffineChartIdeal L),
      ∃ n d : ℕ, n ≤ 1 ∧ 1 ≤ d ∧ d ≤ D ∧
        HasAffineHilbertDimensionDegree Q n d)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧
      ((rankSevenSurfaceEdgeFrontierPointCell
        p x₀ equations CF Cchart P k record L).card : ℝ) ≤
        ((finitePointsOnLinearCurveComponents
          (realProjectiveAffineChartIdeal L)
          (rankSevenSurfaceEdgeFrontierPointCell
            p x₀ equations CF Cchart P k record L)).card : ℝ) +
        C * (p.T ^ (2 / 7 : ℝ)) ^ ((1 / 2 : ℝ) + ε) := by
  obtain ⟨C₀, hC₀, hcount⟩ :=
    rankSevenSurfaceEdgeFrontierPointCell_card_le_rescaledPila
      hPila p x₀ equations CF Cchart P k hP q r record hrecord L
        hcomponents ε hε
  let componentCount : ℕ :=
    (nonlinearAffineComponents (realProjectiveAffineChartIdeal L)).card
  let C : ℝ :=
    (1 + (componentCount : ℝ)) * C₀ *
      (2 : ℝ) ^ ((1 / 2 : ℝ) + ε)
  have hC : 0 < C := by
    dsimp only [C]
    positivity
  refine ⟨C, hC, hcount.trans ?_⟩
  have hterm := recordPilaNonlinearTerm_le_reservoirScale
    p hlower hC₀ hε (count := componentCount)
  dsimp only [componentCount, C] at hterm ⊢
  gcongr

end

end TranslatedDepthSeven
