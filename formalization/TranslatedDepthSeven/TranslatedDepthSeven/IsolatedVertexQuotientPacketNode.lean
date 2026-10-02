import TranslatedDepthSeven.IsolatedVertexQuotientNodeDecomposition
import TranslatedDepthSeven.IsolatedVertexQuotientTangentPacket
import TranslatedDepthSeven.EquationFamilyTangentBaseChange

/-!
# Literal node components attached to a quotient residue packet

The tangent argument returns an affine subspace of direction dimension at
most eight in twelve affine variables.  Four independent affine-linear
equations vanishing on that subspace give four homogeneous equations in
thirteen projective coordinates.  This file retains those equations, the
actual residue packet, and the actual minimal-prime node components.

The only new outside input is the elementary finite-dimensional linear-
algebra statement that an affine subspace of codimension at least four is
contained in the common zero set of four independent affine-linear forms.
No component or counting conclusion is included in that input.
-/

namespace TranslatedDepthSeven

noncomputable section

open Matrix MvPolynomial Published

attribute [local instance] MvPolynomial.gradedAlgebra

set_option maxHeartbeats 4000000

/-- The standard homogeneous representative `(1,z)` of a rational affine
point in twelve variables. -/
def quotientRationalHomogeneousAffinePoint
    (z : IntVector 12) : Fin 13 → ℚ :=
  Fin.cases 1 (fun i ↦ (z i : ℚ))

namespace StandardLinearAlgebra

/-- Four independent homogeneous affine equations containing any affine
subspace of `ℚ^12` whose direction has dimension at most eight.  This is
ordinary annihilator duality in finite-dimensional linear algebra. -/
def AffineEightPlaneFourHomogeneousEquations : Prop :=
  ∀ S : AffineSubspace ℚ (Fin 12 → ℚ),
    Module.finrank ℚ S.direction ≤ 8 →
      ∃ A : Matrix (Fin 4) (Fin 13) ℚ,
        A.rank = 4 ∧
        ∀ z : IntVector 12,
          (fun i ↦ (z i : ℚ)) ∈ S →
            Matrix.mulVec A (quotientRationalHomogeneousAffinePoint z) = 0

end StandardLinearAlgebra

/-- A literal choice of four projective row equations for one occupied
quotient residue packet. -/
structure IsolatedVertexQuotientPacketPlane
    (Z : Finset (IntVector 12)) (q : ℕ) (rho : Fin 12 → ZMod q) where
  matrix : Matrix (Fin 4) (Fin 13) ℚ
  rank_matrix : matrix.rank = 4
  packet_mem : ∀ z ∈ integralResiduePacket Z rho,
    Matrix.mulVec matrix (quotientRationalHomogeneousAffinePoint z) = 0

/-- The elementary affine-subspace input turns the output of the tangent
packet theorem into four literal projective equations. -/
theorem nonempty_isolatedVertexQuotientPacketPlane_of_affineSubspace
    (hlinear : StandardLinearAlgebra.AffineEightPlaneFourHomogeneousEquations)
    (Z : Finset (IntVector 12)) (q : ℕ) (rho : Fin 12 → ZMod q)
    (S : AffineSubspace ℚ (Fin 12 → ℚ))
    (hSdim : Module.finrank ℚ S.direction ≤ 8)
    (hpacket : ∀ z ∈ integralResiduePacket Z rho,
      (fun i ↦ (z i : ℚ)) ∈ S) :
    Nonempty (IsolatedVertexQuotientPacketPlane Z q rho) := by
  obtain ⟨A, hA, hAS⟩ := hlinear S hSdim
  exact ⟨{
    matrix := A
    rank_matrix := hA
    packet_mem := fun z hz ↦ hAS z (hpacket z hz) }⟩

/-- Direct specialization to the affine subspace supplied by the quotient
tangent-packet theorem.  The point set remains the literal
`isolatedVertexQuotientPointFinset`; it is not enlarged to the full zero
locus of the quotient equations. -/
theorem nonempty_isolatedVertexQuotientPacketPlane_for_occupied_packet
    (hlinear : StandardLinearAlgebra.AffineEightPlaneFourHomogeneousEquations)
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
    Nonempty (IsolatedVertexQuotientPacketPlane
      (isolatedVertexQuotientPointFinset U p x₀ sourceEquations CF)
      q rho) := by
  obtain ⟨S, hSdim, hpacket⟩ :=
    exists_isolatedVertexQuotient_affineSubspace_for_occupied_packet
      U p x₀ sourceEquations CF quotientEquations hquotient
      q hqpos hqsf hq rho hrho hrank
  exact nonempty_isolatedVertexQuotientPacketPlane_of_affineSubspace
    hlinear _ q rho S hSdim hpacket

namespace IsolatedVertexQuotientPacketPlane

/-- The same four-row matrix after scalar extension to the fixed algebraic
closure in which geometric components are taken. -/
def geometricMatrix
    {Z : Finset (IntVector 12)} {q : ℕ} {rho : Fin 12 → ZMod q}
    (plane : IsolatedVertexQuotientPacketPlane Z q rho) :
    Matrix (Fin 4) (Fin 13) Qbar :=
  plane.matrix.map (algebraMap ℚ Qbar)

/-- Field extension preserves the rank of the four selected equations. -/
theorem geometricMatrix_rank
    {Z : Finset (IntVector 12)} {q : ℕ} {rho : Fin 12 → ZMod q}
    (plane : IsolatedVertexQuotientPacketPlane Z q rho) :
    plane.geometricMatrix.rank = 4 := by
  rw [geometricMatrix, TangentBaseChange.rank_map_algebraMap]
  exact plane.rank_matrix

end IsolatedVertexQuotientPacketPlane

/-- The literal finite component list at the actual occupied pair
`(q,rho)`, for the chosen packet plane. -/
def isolatedVertexQuotientPacketNodeComponents
    (J : Ideal (MvPolynomial (Fin 12) Qbar))
    (b : Fin 12 → Qbar) (m : Qbar) (hm : m ≠ 0)
    {Z : Finset (IntVector 12)} {q : ℕ} {rho : Fin 12 → ZMod q}
    (plane : IsolatedVertexQuotientPacketPlane Z q rho) :
    Finset (Ideal (MvPolynomial (Fin 13) Qbar)) :=
  isolatedVertexQuotientNodeComponents J b m hm plane.geometricMatrix

/-- The full component decomposition and degree mass, now specialized to
the literal four equations attached to an actual residue packet. -/
theorem exists_isolatedVertexQuotientPacketNodeComponentDecomposition
    (hMass : StandardAG.GeometricFourPlaneSectionComponentDegreeMass)
    (hAway : StandardAG.QuotientNodeAwayVertexComponentLift)
    (hContained : StandardAG.QuotientNodeVertexContainedComponentLift)
    (hZero : StandardAG.AlgebraicallyClosedIntegralProjectiveZerofoldDegreeOne)
    (J : Ideal (MvPolynomial (Fin 12) Qbar))
    (hJprime : J.IsPrime)
    (hJhomogeneous : J.IsHomogeneous
      (MvPolynomial.homogeneousSubmodule (Fin 12) Qbar))
    (degree : ℕ) (hJHilbert : HasProjectiveDimensionDegree (N := 11) J 4 degree)
    (b : Fin 12 → Qbar) (m : Qbar) (hm : m ≠ 0)
    {Z : Finset (IntVector 12)} {q : ℕ} {rho : Fin 12 → ZMod q}
    (plane : IsolatedVertexQuotientPacketPlane Z q rho) :
    ∃ componentDimension componentDegree :
        Ideal (MvPolynomial (Fin 13) Qbar) → ℕ,
      (∀ P ∈ isolatedVertexQuotientPacketNodeComponents
          J b m hm plane,
        1 ≤ componentDimension P ∧
        HasGeometricProjectiveDimensionDegree P
          (componentDimension P) (componentDegree P) ∧
        QuotientNodeComponentDisposition J b m hm plane.geometricMatrix P
          (componentDimension P) (componentDegree P)) ∧
      ∑ P ∈ isolatedVertexQuotientPacketNodeComponents J b m hm plane,
        componentDegree P ≤ degree := by
  simpa only [isolatedVertexQuotientPacketNodeComponents] using
    exists_quotientNodeComponentDecomposition
      hMass hAway hContained hZero J hJprime hJhomogeneous degree hJHilbert
      b m hm plane.geometricMatrix plane.geometricMatrix_rank

end

end TranslatedDepthSeven
