import TranslatedDepthSeven.AffineIntegralPointTransport
import TranslatedDepthSeven.FiniteResiduePacket

/-!
# Rescaling a finite residue packet

This file turns the proof-dependent congruence displacement into one total
function on integral vectors.  On a fixed congruence class it is the inverse
of `z ↦ base + q z`; consequently it is injective there and has the usual
divided box bound.
-/

namespace TranslatedDepthSeven

noncomputable section

/-- The unique quotient `(z-base)/q` when it is integral, and zero away from
that congruence class. -/
def congruenceDisplacementOrZero {N : ℕ} (q : ℕ)
    (base z : IntVector N) : IntVector N := by
  classical
  exact if h : IntVectorCongruent q z base then
    congruenceDisplacement base ⟨z, h⟩
  else 0

theorem congruenceDisplacementOrZero_spec {N q : ℕ}
    (base z : IntVector N) (hz : IntVectorCongruent q z base)
    (i : Fin N) :
    z i = base i + q * congruenceDisplacementOrZero q base z i := by
  classical
  rw [congruenceDisplacementOrZero, dif_pos hz]
  exact congruenceDisplacement_spec base ⟨z, hz⟩ i

/-- The total quotient map is injective on the displayed congruence class. -/
theorem congruenceDisplacementOrZero_injOn {N q : ℕ}
    (base : IntVector N) :
    Set.InjOn (congruenceDisplacementOrZero q base)
      {z : IntVector N | IntVectorCongruent q z base} := by
  intro z hz w hw heq
  funext i
  rw [congruenceDisplacementOrZero_spec base z hz i,
    congruenceDisplacementOrZero_spec base w hw i, congrFun heq i]

/-- If the point and the base lie in the same real box about `center`, the
quotient coordinate is at most `2R/q`. -/
theorem congruenceDisplacementOrZero_coordinate_bound
    {N q : ℕ} (hq : 0 < q) (base z : IntVector N)
    (hz : IntVectorCongruent q z base)
    {center : RealVector N} {R : ℝ}
    (hzbox : ∀ i, |(z i : ℝ) - center i| ≤ R)
    (hbasebox : ∀ i, |(base i : ℝ) - center i| ≤ R)
    (i : Fin N) :
    |(congruenceDisplacementOrZero q base z i : ℝ)| ≤ 2 * R / q := by
  classical
  rw [congruenceDisplacementOrZero, dif_pos hz]
  exact congruenceDisplacement_coordinate_bound hq base ⟨z, hz⟩
    hzbox hbasebox i

/-- Membership in one literal residue packet gives the exact reconstruction
formula from its chosen base. -/
theorem integralResiduePacket_reconstruct_from_displacement
    {N q : ℕ} (Z : Finset (IntVector N))
    (rho : Fin N → ZMod q)
    (base : IntVector N) (hbase : base ∈ integralResiduePacket Z rho)
    {z : IntVector N} (hz : z ∈ integralResiduePacket Z rho)
    (i : Fin N) :
    z i = base i + q * congruenceDisplacementOrZero q base z i := by
  apply congruenceDisplacementOrZero_spec
  exact intVectorCongruent_of_mem_same_integralResiduePacket hz hbase

/-- The quotient map is injective on a literal residue packet. -/
theorem congruenceDisplacementOrZero_injOn_integralResiduePacket
    {N q : ℕ} (Z : Finset (IntVector N))
    (rho : Fin N → ZMod q)
    (base : IntVector N) (hbase : base ∈ integralResiduePacket Z rho) :
    Set.InjOn (congruenceDisplacementOrZero q base)
      (↑(integralResiduePacket Z rho) : Set (IntVector N)) := by
  apply (congruenceDisplacementOrZero_injOn base).mono
  intro z hz
  exact intVectorCongruent_of_mem_same_integralResiduePacket hz hbase

end

end TranslatedDepthSeven
