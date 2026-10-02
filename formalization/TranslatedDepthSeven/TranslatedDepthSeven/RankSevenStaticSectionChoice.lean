import TranslatedDepthSeven.DepthSevenRankSevenPacketAssembly
import TranslatedDepthSeven.CertificateDeletedEquationComponentPartition
import TranslatedDepthSeven.RankSevenSourceSectionComponents

/-!
# A fixed source section for every surviving rank-seven packet

For a point `z` and a reservoir modulus `q` avoiding the scale/denominator
and chart-determinant certificates, reduction of `z` modulo `q` is an
occupied rank-seven packet.  The tangent-minor and Cramer lemmas therefore
produce four homogeneous integral row equations containing that entire
packet.  This file makes one such matrix a literal function of `(q,z)` and
uses it to define the finite source-section equation family compared across
the reservoir.

The choice is made only after proving the full displayed specification.  No
geometric component, dimension assertion, or counting bound is selected or
assumed here.
-/

namespace TranslatedDepthSeven

noncomputable section

open MvPolynomial

set_option maxHeartbeats 4000000

/-- The exact Cramer data retained for one occupied rank-seven packet. -/
structure RankSevenPacketSectionData
    (p : Parameters) (x₀ : IntVector 13)
    (equations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    (C : IntegralDepthSevenJacobianChartIndex equations)
    (q : ℕ) (rho : Fin 13 → ZMod q) where
  matrix : Matrix (Fin 4) (Fin 14) ℤ
  rank : (matrix.map ((↑) : ℤ → ℚ)).rank = 4
  packet_mem : ∀ w ∈ integralResiduePacket
      (depthSevenNormalizedJacobianChartCell p x₀ equations CF C)
      rho,
    Matrix.mulVec (matrix.map ((↑) : ℤ → ℚ))
      (rationalHomogeneousAffinePoint w) = 0
  entry_le : ∀ i j,
    (matrix i j).natAbs ≤ depthSevenPacketSectionEntryBound p
  height_le : rationalProjectiveLinearHeight
      (matrix.map ((↑) : ℤ → ℚ)) ≤
    ⌈p.H ^ packetSectionHeightExponent⌉₊

/-- Every point of a static reservoir cell yields the complete Cramer data
for its full chart packet. -/
theorem exists_rankSevenPacketSectionData_of_mem_reservoirCell
    (p : Parameters) (x₀ : IntVector 13)
    (equations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    (C : IntegralDepthSevenJacobianChartIndex equations)
    (denominator : ℤ) (P : Finset ℕ) (k : ℕ)
    (hP : ∀ s ∈ P, s.Prime)
    (hlower : ∀ q : ReservoirModulus P k,
      manuscriptReservoirTarget normalizedSurfaceReservoirConstant
        p.T (5 / 7) ≤ q.1)
    (q : ReservoirModulus P k) (z : IntVector 13)
    (hz : z ∈ rankSevenChartReservoirCell
      p x₀ equations CF C denominator q.1) :
    Nonempty (RankSevenPacketSectionData
      p x₀ equations CF C q.1
        (integralResidueVector z : Fin 13 → ZMod q.1)) := by
  obtain ⟨hzChart, hscale, hchart⟩ := Finset.mem_filter.mp hz
  have hrhoFull : (integralResidueVector z : Fin 13 → ZMod q.1) ∈
      occupiedIntegralResidues q.1
        (depthSevenNormalizedJacobianChartCell p x₀ equations CF C) :=
    mem_occupiedIntegralResidues_iff.mpr ⟨z, hzChart, rfl⟩
  have hscale' : Nat.Coprime q.1 (p.m * denominator.natAbs) := by
    simpa [Int.natAbs_mul] using hscale
  have hqm : Nat.Coprime q.1 p.m :=
    hscale'.of_dvd_right (Nat.dvd_mul_right p.m denominator.natAbs)
  let S := q.1.primeFactors
  have hSprime : ∀ s ∈ S, s.Prime := fun s hs ↦
    Nat.prime_of_mem_primeFactors hs
  have hproduct : primeProduct S = q.1 :=
    (primeFactors_spec_of_mem_modulusReservoir hP q.2).2.2
  have hlowerS : manuscriptReservoirTarget normalizedSurfaceReservoirConstant
      p.T (5 / 7) ≤ primeProduct S := by
    rw [hproduct]
    exact hlower q
  rw [← hproduct] at hrhoFull hqm hchart
  let base := integralResiduePacketBase
    (depthSevenNormalizedJacobianChartCell p x₀ equations CF C)
    (integralResidueVector z : Fin 13 → ZMod (primeProduct S)) hrhoFull
  have hbasePacket : base ∈ integralResiduePacket
      (depthSevenNormalizedJacobianChartCell p x₀ equations CF C)
      (integralResidueVector z : Fin 13 → ZMod (primeProduct S)) :=
    integralResiduePacketBase_mem
      (depthSevenNormalizedJacobianChartCell p x₀ equations CF C)
      (integralResidueVector z) hrhoFull
  have hcoordinate : ∀ i,
      (integralAffineMap x₀ z p.m i : ZMod (primeProduct S)) =
        (integralAffineMap x₀ base p.m i : ZMod (primeProduct S)) := by
    intro i
    have hbaseResidue := congrFun
      (mem_integralResiduePacket_iff.mp hbasePacket).2 i
    change (base i : ZMod (primeProduct S)) =
      (z i : ZMod (primeProduct S)) at hbaseResidue
    simp only [integralAffineMap, Int.cast_add, Int.cast_mul,
      Int.cast_natCast]
    rw [hbaseResidue]
  have hqchart : Nat.Coprime (primeProduct S)
      (MvPolynomial.eval (integralAffineMap x₀ base p.m)
        C.determinant).natAbs :=
    coprime_eval_natAbs_of_coordinate_cast_eq C.determinant
      (integralAffineMap x₀ z p.m) (integralAffineMap x₀ base p.m)
      hcoordinate hchart
  obtain ⟨A, hArank, hAmem, hAentry, hAheight, _hprojected⟩ :=
    exists_projectedSection_for_rankSevenChartPacket
      p x₀ equations CF C S hSprime hlowerS
      (integralResidueVector z) hrhoFull hqm hqchart
  refine ⟨⟨A, hArank, ?_, hAentry, hAheight⟩⟩
  intro w hw
  rw [← hproduct] at hw
  exact hAmem w hw

/-- One fixed Cramer datum for a modulus and a residue packet whenever such
data exist.  The choice is indexed by the residue itself, not by a lift of
that residue to an integral point. -/
def selectedRankSevenPacketSectionData
    (p : Parameters) (x₀ : IntVector 13)
    (equations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    (C : IntegralDepthSevenJacobianChartIndex equations)
    (q : ℕ) (rho : Fin 13 → ZMod q)
    (hdata : Nonempty
      (RankSevenPacketSectionData p x₀ equations CF C q rho)) :
    RankSevenPacketSectionData p x₀ equations CF C q rho :=
  Classical.choice hdata

/-- The selected source-section matrix, defined for every modulus and
residue vector and equal to zero precisely when no certified datum exists.
Consequently equal residue vectors give literally equal matrices. -/
def selectedRankSevenPacketSectionMatrix
    (p : Parameters) (x₀ : IntVector 13)
    (equations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    (C : IntegralDepthSevenJacobianChartIndex equations)
    (q : ℕ) (rho : Fin 13 → ZMod q) :
    Matrix (Fin 4) (Fin 14) ℤ := by
  classical
  by_cases hdata : Nonempty
      (RankSevenPacketSectionData p x₀ equations CF C q rho)
  · exact (selectedRankSevenPacketSectionData
      p x₀ equations CF C q rho hdata).matrix
  · exact 0

/-- On a surviving chart point, the selected matrix has rank four. -/
theorem selectedRankSevenPacketSectionMatrix_rank
    (p : Parameters) (x₀ : IntVector 13)
    (equations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    (C : IntegralDepthSevenJacobianChartIndex equations)
    (denominator : ℤ) (P : Finset ℕ) (k : ℕ)
    (hP : ∀ s ∈ P, s.Prime)
    (hlower : ∀ q : ReservoirModulus P k,
      manuscriptReservoirTarget normalizedSurfaceReservoirConstant
        p.T (5 / 7) ≤ q.1)
    (q : ReservoirModulus P k) (z : IntVector 13)
    (hz : z ∈ rankSevenChartReservoirCell
      p x₀ equations CF C denominator q.1) :
    ((selectedRankSevenPacketSectionMatrix
      p x₀ equations CF C q.1
        (integralResidueVector z : Fin 13 → ZMod q.1)).map
        ((↑) : ℤ → ℚ)).rank = 4 := by
  let hdata := exists_rankSevenPacketSectionData_of_mem_reservoirCell
    p x₀ equations CF C denominator P k hP hlower q z hz
  rw [selectedRankSevenPacketSectionMatrix]
  simp only [dif_pos hdata]
  exact (selectedRankSevenPacketSectionData
    p x₀ equations CF C q.1
      (integralResidueVector z : Fin 13 → ZMod q.1) hdata).rank

/-- Every member of the full residue packet lies on the selected source
section. -/
theorem selectedRankSevenPacketSectionMatrix_packet_mem
    (p : Parameters) (x₀ : IntVector 13)
    (equations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    (C : IntegralDepthSevenJacobianChartIndex equations)
    (denominator : ℤ) (P : Finset ℕ) (k : ℕ)
    (hP : ∀ s ∈ P, s.Prime)
    (hlower : ∀ q : ReservoirModulus P k,
      manuscriptReservoirTarget normalizedSurfaceReservoirConstant
        p.T (5 / 7) ≤ q.1)
    (q : ReservoirModulus P k) (z w : IntVector 13)
    (hz : z ∈ rankSevenChartReservoirCell
      p x₀ equations CF C denominator q.1)
    (hw : w ∈ integralResiduePacket
      (depthSevenNormalizedJacobianChartCell p x₀ equations CF C)
      (integralResidueVector z : Fin 13 → ZMod q.1)) :
    Matrix.mulVec
      ((selectedRankSevenPacketSectionMatrix
        p x₀ equations CF C q.1
          (integralResidueVector z : Fin 13 → ZMod q.1)).map
          ((↑) : ℤ → ℚ))
      (rationalHomogeneousAffinePoint w) = 0 := by
  let hdata := exists_rankSevenPacketSectionData_of_mem_reservoirCell
    p x₀ equations CF C denominator P k hP hlower q z hz
  rw [selectedRankSevenPacketSectionMatrix]
  simp only [dif_pos hdata]
  exact (selectedRankSevenPacketSectionData
    p x₀ equations CF C q.1
      (integralResidueVector z : Fin 13 → ZMod q.1) hdata).packet_mem w hw

/-- Literal finite source-section equations attached to a modulus and one
residue vector.  This is the node object used in the finite record count. -/
def rankSevenSourceSectionEquationsAtResidue
    (p : Parameters) (x₀ : IntVector 13)
    (equations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    (C : IntegralDepthSevenJacobianChartIndex equations)
    (q : ℕ) (rho : Fin 13 → ZMod q) :
    Finset (MvPolynomial (Fin 14) ℚ) :=
  rankSevenSourceSectionEquationFinset x₀ p.m p.hm equations
    ((selectedRankSevenPacketSectionMatrix
      p x₀ equations CF C q rho).map ((↑) : ℤ → ℚ))

/-- Literal finite source-section equations attached to `(q,z)`, obtained
by applying the residue-indexed node construction to `z mod q`. -/
def rankSevenStaticSourceSectionEquations
    (p : Parameters) (x₀ : IntVector 13)
    (equations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    (C : IntegralDepthSevenJacobianChartIndex equations)
    (_denominator : ℤ) (P : Finset ℕ) (k : ℕ)
    (_hP : ∀ s ∈ P, s.Prime)
    (_hlower : ∀ q : ReservoirModulus P k,
      manuscriptReservoirTarget normalizedSurfaceReservoirConstant
        p.T (5 / 7) ≤ q.1)
    (q : ReservoirModulus P k) (z : IntVector 13) :
    Finset (MvPolynomial (Fin 14) ℚ) :=
  rankSevenSourceSectionEquationsAtResidue p x₀ equations CF C q.1
    (integralResidueVector z : Fin 13 → ZMod q.1)

/-- The complete source-section equation family depends only on the residue
class modulo its displayed reservoir modulus. -/
theorem rankSevenStaticSourceSectionEquations_eq_of_residue_eq
    (p : Parameters) (x₀ : IntVector 13)
    (equations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    (C : IntegralDepthSevenJacobianChartIndex equations)
    (denominator : ℤ) (P : Finset ℕ) (k : ℕ)
    (hP : ∀ s ∈ P, s.Prime)
    (hlower : ∀ q : ReservoirModulus P k,
      manuscriptReservoirTarget normalizedSurfaceReservoirConstant
        p.T (5 / 7) ≤ q.1)
    (q : ReservoirModulus P k) (z w : IntVector 13)
    (hresidue : (integralResidueVector z : Fin 13 → ZMod q.1) =
      integralResidueVector w) :
    rankSevenStaticSourceSectionEquations
        p x₀ equations CF C denominator P k hP hlower q z =
      rankSevenStaticSourceSectionEquations
        p x₀ equations CF C denominator P k hP hlower q w := by
  simp only [rankSevenStaticSourceSectionEquations]
  rw [hresidue]

/-- A surviving chart point lies on its selected literal source-section
equation family in the standard affine chart. -/
theorem integralAffineChartVector_mem_rankSevenStaticSourceSectionEquations
    (p : Parameters) (x₀ : IntVector 13)
    (equations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    (hhomogeneous : ∀ f ∈ equations, ∃ e : ℕ, f.IsHomogeneous e)
    (C : IntegralDepthSevenJacobianChartIndex equations)
    (denominator : ℤ) (P : Finset ℕ) (k : ℕ)
    (hP : ∀ s ∈ P, s.Prime)
    (hlower : ∀ q : ReservoirModulus P k,
      manuscriptReservoirTarget normalizedSurfaceReservoirConstant
        p.T (5 / 7) ≤ q.1)
    (q : ReservoirModulus P k) (z : IntVector 13)
    (hz : z ∈ rankSevenChartReservoirCell
      p x₀ equations CF C denominator q.1) :
    (fun i ↦ (integralAffineChartVector z i : ℚ)) ∈
      finiteAffineCommonZeroLocus
        (rankSevenStaticSourceSectionEquations
          p x₀ equations CF C denominator P k hP hlower q z) := by
  have hzChart : z ∈ depthSevenNormalizedJacobianChartCell
      p x₀ equations CF C := (Finset.mem_filter.mp hz).1
  have hzero := depthSevenNormalized_integralCommonZero
    p x₀ equations CF
      ((mem_depthSevenNormalizedJacobianChartCell_iff
        p x₀ equations CF C z).mp hzChart).1
  have hzPacket : z ∈ integralResiduePacket
      (depthSevenNormalizedJacobianChartCell p x₀ equations CF C)
      (integralResidueVector z : Fin 13 → ZMod q.1) :=
    mem_integralResiduePacket_iff.mpr ⟨hzChart, rfl⟩
  have hA := selectedRankSevenPacketSectionMatrix_packet_mem
    p x₀ equations CF C denominator P k hP hlower q z z hz hzPacket
  intro g hg
  apply integralAffineChartVector_mem_rankSevenSourceSectionIdeal
    x₀ p.hm equations hhomogeneous
      ((selectedRankSevenPacketSectionMatrix
        p x₀ equations CF C q.1
          (integralResidueVector z : Fin 13 → ZMod q.1)).map
          ((↑) : ℤ → ℚ)) z hzero hA
  exact Ideal.subset_span hg

end

end TranslatedDepthSeven
