import TranslatedDepthSeven.FiniteResiduePacket
import TranslatedDepthSeven.NormalizedTangentPacket

/-!
# Concrete occupied tangent packets

This file applies the normalized tangent-minor theorem to the actual fibres
of reduction modulo `q` in a finite set `Z`.  The packet base point is chosen
from the nonempty fibre itself.  Thus the index set of the resulting affine
planes is literally `occupiedIntegralResidues q Z`, whose cardinality is
controlled by `FixedConeOccupiedResidueCRT`.
-/

namespace TranslatedDepthSeven

noncomputable section

open NormalizedTangentPacket

/-- A fixed member of a nonempty occupied packet. -/
def integralResiduePacketBase {N q : ℕ} (Z : Finset (IntVector N))
    (rho : Fin N → ZMod q) (hrho : rho ∈ occupiedIntegralResidues q Z) :
    IntVector N :=
  Classical.choose
    (integralResiduePacket_nonempty_iff_mem_occupied.mpr hrho)

theorem integralResiduePacketBase_mem {N q : ℕ}
    (Z : Finset (IntVector N)) (rho : Fin N → ZMod q)
    (hrho : rho ∈ occupiedIntegralResidues q Z) :
    integralResiduePacketBase Z rho hrho ∈ integralResiduePacket Z rho :=
  Classical.choose_spec
    (integralResiduePacket_nonempty_iff_mem_occupied.mpr hrho)

/-- Every occupied manuscript-scale packet whose chosen base point has
rank-seven reduction at the primes dividing `q` is contained in a rational
affine subspace of direction dimension at most nine. -/
theorem exists_surface_affineSubspace_for_occupied_packet
    (equations : Finset (MvPolynomial (Fin 13) ℤ))
    (x₀ : IntVector 13) (m q T : ℕ)
    (Z : Finset (IntVector 13))
    (hT : 1 ≤ T) (hqpos : 0 < q) (hqsf : Squarefree q)
    (hq : surfaceTangentQThreshold T ≤ q)
    (hzero : ∀ z ∈ Z, IntegralCommonZero equations
      (integralAffineMap x₀ z m))
    (hbox : ∀ z ∈ Z, ∀ j, (z j).natAbs ≤ 2 * T)
    (hscale : ∀ p, p.Prime → p ∣ q → ¬ p ∣ m)
    (rho : Fin 13 → ZMod q)
    (hrho : rho ∈ occupiedIntegralResidues q Z)
    (hrank : ∀ p, p.Prime → p ∣ q →
      7 ≤ (jacobianMatrix (indexedFinsetFamily equations)
        (integralAffineMap x₀
          (integralResiduePacketBase Z rho hrho) m) p).rank) :
    ∃ A : AffineSubspace ℚ (Fin 13 → ℚ),
      Module.finrank ℚ A.direction ≤ 9 ∧
      ∀ z ∈ integralResiduePacket Z rho,
        (fun j ↦ (z j : ℚ)) ∈ A := by
  let Packet := {z : IntVector 13 // z ∈ integralResiduePacket Z rho}
  let y : Packet → IntVector 13 := fun z ↦ z.1
  let i₀ : Packet :=
    ⟨integralResiduePacketBase Z rho hrho,
      integralResiduePacketBase_mem Z rho hrho⟩
  obtain ⟨A, hdim, hmem⟩ :=
    exists_affineSubspace_finrank_le_nine_of_surface_threshold
      equations x₀ m q T y i₀ hT hqpos hqsf hq
      (by
        intro z
        exact hzero z.1
          (mem_integralResiduePacket_iff.mp z.2).1)
      (by
        intro z
        exact intVectorCongruent_of_mem_same_integralResiduePacket
          z.2 i₀.2)
      hscale (by simpa only [y, i₀] using hrank)
      (by
        intro z j
        exact hbox z.1
          (mem_integralResiduePacket_iff.mp z.2).1 j)
  refine ⟨A, hdim, ?_⟩
  intro z hz
  exact hmem ⟨z, hz⟩

/-- The certificate form has the order needed by the reservoir argument:
rank over `ℚ` first selects a bounded nonzero integral minor at the chosen
packet base; any subsequent squarefree modulus coprime to the scale and that
minor supplies the rational nine-plane. -/
theorem exists_bounded_certificate_for_occupied_packet_then_surface_plane
    (equations : Finset (MvPolynomial (Fin 13) ℤ))
    (x₀ : IntVector 13) (m q T Y : ℕ)
    (Z : Finset (IntVector 13))
    (hT : 1 ≤ T) (hqpos : 0 < q) (hqsf : Squarefree q)
    (hq : surfaceTangentQThreshold T ≤ q)
    (hzero : ∀ z ∈ Z, IntegralCommonZero equations
      (integralAffineMap x₀ z m))
    (hbox : ∀ z ∈ Z, ∀ j, (z j).natAbs ≤ 2 * T)
    (rho : Fin 13 → ZMod q)
    (hrho : rho ∈ occupiedIntegralResidues q Z)
    (hregular : IsDepthSevenJacobianRegularAt equations
      (integralAffineMap x₀
        (integralResiduePacketBase Z rho hrho) m))
    (hx : ∀ j, (integralAffineMap x₀
      (integralResiduePacketBase Z rho hrho) m j).natAbs ≤ Y) :
    ∃ rows : Fin 7 → Fin equations.card,
      ∃ cols : Fin 7 → Fin 13,
        Function.Injective rows ∧ Function.Injective cols ∧
        integralJacobianMinor (indexedFinsetFamily equations)
          (integralAffineMap x₀
            (integralResiduePacketBase Z rho hrho) m) rows cols ≠ 0 ∧
        (integralJacobianMinor (indexedFinsetFamily equations)
          (integralAffineMap x₀
            (integralResiduePacketBase Z rho hrho) m) rows cols).natAbs ≤
          Nat.factorial 7 *
            (equationFamilySupportBound equations *
              equationFamilyDegreeBound equations *
              equationFamilyCoefficientBound equations *
              max 1 Y ^ equationFamilyDegreeBound equations) ^ 7 ∧
        (Nat.Coprime q m →
          Nat.Coprime q
            (integralJacobianMinor (indexedFinsetFamily equations)
              (integralAffineMap x₀
                (integralResiduePacketBase Z rho hrho) m)
              rows cols).natAbs →
          ∃ A : AffineSubspace ℚ (Fin 13 → ℚ),
            Module.finrank ℚ A.direction ≤ 9 ∧
            ∀ z ∈ integralResiduePacket Z rho,
              (fun j ↦ (z j : ℚ)) ∈ A) := by
  let Packet := {z : IntVector 13 // z ∈ integralResiduePacket Z rho}
  let y : Packet → IntVector 13 := fun z ↦ z.1
  let i₀ : Packet :=
    ⟨integralResiduePacketBase Z rho hrho,
      integralResiduePacketBase_mem Z rho hrho⟩
  obtain ⟨rows, cols, hrows, hcols, hminor, hbound, hplane⟩ :=
    exists_bounded_certificate_then_surface_affineSubspace_finrank_le_nine
      equations x₀ m q T Y y i₀ hT hqpos hqsf hq hregular hx
      (by
        intro z
        exact hzero z.1
          (mem_integralResiduePacket_iff.mp z.2).1)
      (by
        intro z
        exact intVectorCongruent_of_mem_same_integralResiduePacket
          z.2 i₀.2)
      (by
        intro z j
        exact hbox z.1
          (mem_integralResiduePacket_iff.mp z.2).1 j)
  refine ⟨rows, cols, hrows, hcols, hminor, hbound, ?_⟩
  intro hqm hqminor
  obtain ⟨A, hdim, hmem⟩ := hplane hqm hqminor
  refine ⟨A, hdim, ?_⟩
  intro z hz
  exact hmem ⟨z, hz⟩

end

end TranslatedDepthSeven
