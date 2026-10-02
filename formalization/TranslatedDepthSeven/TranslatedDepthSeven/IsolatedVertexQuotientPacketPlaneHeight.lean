import TranslatedDepthSeven.IsolatedVertexQuotientPacketNode
import TranslatedDepthSeven.IntegralPacketSpanBasis
import TranslatedDepthSeven.AffinePacketProjectiveSection

/-!
# Integral equations and height for a quotient packet plane

The tangent-packet argument first places a finite packet in a rational
affine subspace of direction dimension at most eight.  Rather than choosing
four equations for that subspace abstractly, this file chooses an integral
basis from the actual point differences and writes four Cramer equations.
Thus the four-plane used in the quotient-node decomposition is rational for
a literal reason, and its coefficient and Plucker heights have explicit
bounds.  No component or point-counting assertion occurs here.
-/

namespace TranslatedDepthSeven

noncomputable section

open Matrix

set_option maxHeartbeats 3000000

/-- Four integral homogeneous equations containing an actual quotient
residue packet, together with the dimension of the selected difference
basis and the elementary coefficient and Plucker-height bounds. -/
structure IntegralIsolatedVertexQuotientPacketPlane
    (Z : Finset (IntVector 12)) (q R : ℕ)
    (rho : Fin 12 → ZMod q) where
  spanRank : ℕ
  spanRank_le_eight : spanRank ≤ 8
  matrix : Matrix (Fin 4) (Fin 13) ℤ
  rank_matrix : (matrix.map ((↑) : ℤ → ℚ)).rank = 4
  packet_mem : ∀ z ∈ integralResiduePacket Z rho,
    Matrix.mulVec (matrix.map ((↑) : ℤ → ℚ))
      (quotientRationalHomogeneousAffinePoint z) = 0
  entry_natAbs_le : ∀ i j,
    (matrix i j).natAbs ≤
      (12 * R + 1) * (spanRank.factorial * (2 * R) ^ spanRank)
  height_le : rationalProjectiveLinearHeight
      (matrix.map ((↑) : ℤ → ℚ)) ≤
    Nat.factorial 4 *
      ((12 * R + 1) * (spanRank.factorial * (2 * R) ^ spanRank)) ^ 4

namespace IntegralIsolatedVertexQuotientPacketPlane

/-- Forgetting the integral Cramer presentation gives the rational packet
plane used by the quotient-node component decomposition. -/
def toPacketPlane
    {Z : Finset (IntVector 12)} {q R : ℕ} {rho : Fin 12 → ZMod q}
    (plane : IntegralIsolatedVertexQuotientPacketPlane Z q R rho) :
    IsolatedVertexQuotientPacketPlane Z q rho where
  matrix := plane.matrix.map ((↑) : ℤ → ℚ)
  rank_matrix := plane.rank_matrix
  packet_mem := plane.packet_mem

@[simp]
theorem toPacketPlane_matrix
    {Z : Finset (IntVector 12)} {q R : ℕ} {rho : Fin 12 → ZMod q}
    (plane : IntegralIsolatedVertexQuotientPacketPlane Z q R rho) :
    plane.toPacketPlane.matrix = plane.matrix.map ((↑) : ℤ → ℚ) :=
  rfl

end IntegralIsolatedVertexQuotientPacketPlane

/-- An affine eight-plane containing the packet yields four *integral*
Cramer equations.  The basis rows are chosen from packet differences, so
their entries are bounded by `2R`; all remaining bounds are the literal
Cramer determinant bounds. -/
theorem nonempty_integralIsolatedVertexQuotientPacketPlane_of_affineSubspace
    (Z : Finset (IntVector 12)) (q R : ℕ) (rho : Fin 12 → ZMod q)
    (hrho : rho ∈ occupiedIntegralResidues q Z)
    (S : AffineSubspace ℚ (Fin 12 → ℚ))
    (hSdim : Module.finrank ℚ S.direction ≤ 8)
    (hpacket : ∀ z ∈ integralResiduePacket Z rho,
      (fun i ↦ (z i : ℚ)) ∈ S)
    (hbox : ∀ z ∈ integralResiduePacket Z rho, ∀ i,
      (z i).natAbs ≤ R) :
    Nonempty (IntegralIsolatedVertexQuotientPacketPlane Z q R rho) := by
  classical
  let packet := integralResiduePacket Z rho
  let base := integralResiduePacketBase Z rho hrho
  have hbase : base ∈ packet := integralResiduePacketBase_mem Z rho hrho
  have hcoord : ∀ z ∈ packet, ∀ j,
      (z j - base j).natAbs ≤ 2 * R := by
    intro z hz j
    exact intVectorDifference_natAbs_le_twice
      (hbox z hz) (hbox base hbase) j
  obtain ⟨r, point, J, hr, hdet, hspan, hB⟩ :=
    exists_integralDifferenceBasis_with_pivot_of_affineSubspace
      packet base hbase S hSdim hpacket hcoord
  have hfour : 4 ≤ 12 - r := by omega
  let B : Matrix (Fin r) (Fin 12) ℤ :=
    integralDifferenceMatrix base (fun i ↦ (point i).1)
  let A : Matrix (Fin 4) (Fin 13) ℤ :=
    fourRowCramerAffineProjectiveSectionMatrix hfour base B J
  refine ⟨{
    spanRank := r
    spanRank_le_eight := hr
    matrix := A
    rank_matrix := ?_
    packet_mem := ?_
    entry_natAbs_le := ?_
    height_le := ?_ }⟩
  · exact fourRowCramerAffineProjectiveSectionMatrix_rank
      hfour base B J hdet
  · intro z hz
    apply fourRowCramerAffineProjectiveSectionMatrix_mulVec_eq_zero
    apply cramerAffineProjectiveSectionMatrix_mulVec_of_difference_mem_span
    rw [hspan]
    exact Submodule.subset_span
      (Set.mem_range_self (⟨z, hz⟩ : {w // w ∈ packet}))
  · intro i j
    exact fourRowCramerAffineProjectiveSectionMatrix_entry_natAbs_le
      hfour base B J hB (hbox base hbase) i j
  · exact fourRowCramerAffineProjectiveSectionMatrix_height_le
      hfour base B J hB (hbox base hbase)

/-- Direct bounded-height replacement for the abstract four-equation choice
in `nonempty_isolatedVertexQuotientPacketPlane_of_affineSubspace`. -/
theorem nonempty_integralIsolatedVertexQuotientPacketPlane_for_occupied_packet
    (U : IntegralUnimodularChange 13) (p : Parameters)
    (x₀ : IntVector 13)
    (sourceEquations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    (quotientEquations : Finset (MvPolynomial (Fin 12) ℤ))
    (hquotient : isolatedVertexQuotientPointFinset U p x₀
      sourceEquations CF ⊆ integralCommonZeroInBox
        (M := isolatedVertexTransformedNaturalSide U p) quotientEquations)
    (q : ℕ) (hqpos : 0 < q) (hqsf : Squarefree q)
    (hq : manuscriptReservoirTarget
      (isolatedVertexQuotientReservoirConstant U : ℝ)
      p.T (9 / 13) ≤ q)
    (rho : Fin 12 → ZMod q)
    (hrho : rho ∈ occupiedIntegralResidues q
      (isolatedVertexQuotientPointFinset U p x₀ sourceEquations CF))
    (hrank : ∀ l, l.Prime → l ∣ q →
      7 ≤ (jacobianMatrix (indexedFinsetFamily quotientEquations)
        (integralResiduePacketBase
          (isolatedVertexQuotientPointFinset U p x₀ sourceEquations CF)
          rho hrho) l).rank) :
    Nonempty (IntegralIsolatedVertexQuotientPacketPlane
      (isolatedVertexQuotientPointFinset U p x₀ sourceEquations CF)
      q (isolatedVertexTransformedNaturalSide U p) rho) := by
  obtain ⟨S, hSdim, hpacket⟩ :=
    exists_isolatedVertexQuotient_affineSubspace_for_occupied_packet
      U p x₀ sourceEquations CF quotientEquations hquotient
      q hqpos hqsf hq rho hrho hrank
  apply nonempty_integralIsolatedVertexQuotientPacketPlane_of_affineSubspace
    _ q (isolatedVertexTransformedNaturalSide U p) rho hrho S hSdim hpacket
  intro z hz i
  have hzSet : z ∈ isolatedVertexQuotientPointFinset
      U p x₀ sourceEquations CF :=
    (mem_integralResiduePacket_iff.mp hz).1
  exact isolatedVertexQuotientPoint_coordinate_le
    U p x₀ sourceEquations CF hzSet i

end

end TranslatedDepthSeven
