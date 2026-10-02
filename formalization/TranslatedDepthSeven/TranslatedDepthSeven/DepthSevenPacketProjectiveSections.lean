import TranslatedDepthSeven.AffinePacketProjectiveSection
import TranslatedDepthSeven.DepthSevenOccupiedTangentPackets
import TranslatedDepthSeven.PacketSectionHeightDomination

/-!
# Literal codimension-four projective sections for occupied packets

The tangent-minor argument places an occupied normalized packet in a
rational affine subspace of direction dimension at most nine.  The integral
packet points themselves then provide a basis of their rational difference
span.  Applying the Cramer construction to that basis gives four independent
homogeneous integral equations in the fourteen projective coordinates of the
translated join.  This file records the resulting packet containment and its
explicit Plücker-height bound.
-/

namespace TranslatedDepthSeven

noncomputable section

open scoped LinearAlgebra.Projectivization

set_option maxHeartbeats 6000000

/-- Generic final Cramer step.  A finite integral set contained in a rational
affine subspace of direction dimension at most nine and in the displayed box
admits four independent homogeneous equations of the required height. -/
theorem exists_fourRow_projectiveSection_of_affineSubspace
    (p : Parameters) (Z : Finset (IntVector 13)) (base : IntVector 13)
    (hbase : base ∈ Z) (A₀ : AffineSubspace ℚ (Fin 13 → ℚ))
    (hA₀dim : Module.finrank ℚ A₀.direction ≤ 9)
    (hA₀mem : ∀ z ∈ Z, (fun j ↦ (z j : ℚ)) ∈ A₀)
    (hbox : ∀ z ∈ Z, ∀ j,
      (z j).natAbs ≤ 2 * surfaceTangentNaturalSide p) :
    ∃ A : Matrix (Fin 4) (Fin 14) ℤ,
      (A.map ((↑) : ℤ → ℚ)).rank = 4 ∧
      (∀ z ∈ Z,
        Projectivization.mk ℚ (rationalHomogeneousAffinePoint z)
            (rationalHomogeneousAffinePoint_ne_zero z) ∈
          rationalProjectiveLinearSpace (A.map ((↑) : ℤ → ℚ))) ∧
      rationalProjectiveLinearHeight (A.map ((↑) : ℤ → ℚ)) ≤
        ⌈p.H ^ packetSectionHeightExponent⌉₊ := by
  have hcoord : ∀ z ∈ Z, ∀ j,
      (z j - base j).natAbs ≤ 4 * surfaceTangentNaturalSide p := by
    intro z hz j
    calc
      (z j - base j).natAbs ≤ (z j).natAbs + (base j).natAbs :=
        Int.natAbs_sub_le _ _
      _ ≤ 2 * surfaceTangentNaturalSide p +
          2 * surfaceTangentNaturalSide p :=
        Nat.add_le_add (hbox z hz j) (hbox base hbase j)
      _ = 4 * surfaceTangentNaturalSide p := by omega
  obtain ⟨r, point, J, hr, hdet, hspan, hB⟩ :=
    exists_integralDifferenceBasis_with_pivot_of_affineSubspace
      Z base hbase A₀ hA₀dim hA₀mem hcoord
  let B := integralDifferenceMatrix base (fun i ↦ (point i).1)
  have hfour : 4 ≤ 13 - r := by omega
  let A := fourRowCramerAffineProjectiveSectionMatrix hfour base B J
  refine ⟨A, ?_, ?_, ?_⟩
  · exact fourRowCramerAffineProjectiveSectionMatrix_rank
      hfour base B J hdet
  · intro z hz
    exact finitePacket_mem_fourRowCramerAffineProjectiveSection_of_span_eq
      hfour Z base B J hspan ⟨z, hz⟩
  · have hraw : rationalProjectiveLinearHeight (A.map ((↑) : ℤ → ℚ)) ≤
        Nat.factorial 4 *
          ((13 * (2 * surfaceTangentNaturalSide p) + 1) *
            (r.factorial *
              (4 * surfaceTangentNaturalSide p) ^ r)) ^ 4 := by
      exact fourRowCramerAffineProjectiveSectionMatrix_height_le
        hfour base B J hB (hbox base hbase)
    exact hraw.trans
      (codimensionFour_packetSectionHeight_le_ceil_heightPower p hr)

end

end TranslatedDepthSeven
