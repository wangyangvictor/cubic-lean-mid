import TranslatedDepthSeven.FixedConeOccupiedResidueCRT
import TranslatedDepthSeven.FiniteProjectionResidueCount

/-!
# The literal finite partition into occupied residue packets

For a finite set of integral vectors and a modulus `q`, the packets in this
file are the actual fibres of coordinatewise reduction modulo `q`.  Their
index set is exactly `occupiedIntegralResidues q Z`; hence empty residue
classes never enter an occurrence count.  The cardinality identity below is
an equality, not a union-bound surrogate.
-/

namespace TranslatedDepthSeven

noncomputable section

/-- Coordinatewise reduction of an integral vector modulo `q`. -/
def integralResidueVector {N q : ℕ} (z : IntVector N) : Fin N → ZMod q :=
  fun i ↦ (z i : ZMod q)

/-- The members of `Z` having the displayed residue vector modulo `q`. -/
def integralResiduePacket {N q : ℕ} (Z : Finset (IntVector N))
    (rho : Fin N → ZMod q) : Finset (IntVector N) :=
  Z.filter fun z ↦ integralResidueVector z = rho

@[simp]
theorem mem_integralResiduePacket_iff
    {N q : ℕ} {Z : Finset (IntVector N)}
    {rho : Fin N → ZMod q} {z : IntVector N} :
    z ∈ integralResiduePacket Z rho ↔
      z ∈ Z ∧ integralResidueVector z = rho := by
  simp [integralResiduePacket]

theorem occupiedIntegralResidues_eq_image_integralResidueVector
    {N q : ℕ} (Z : Finset (IntVector N)) :
    occupiedIntegralResidues q Z = Z.image integralResidueVector := by
  rfl

/-- A residue vector is occupied exactly when its packet is nonempty. -/
theorem integralResiduePacket_nonempty_iff_mem_occupied
    {N q : ℕ} {Z : Finset (IntVector N)}
    {rho : Fin N → ZMod q} :
    (integralResiduePacket Z rho).Nonempty ↔
      rho ∈ occupiedIntegralResidues q Z := by
  classical
  constructor
  · rintro ⟨z, hz⟩
    have hz' := (mem_integralResiduePacket_iff.mp hz)
    exact Finset.mem_image.mpr ⟨z, hz'.1, hz'.2⟩
  · intro hrho
    obtain ⟨z, hz, hzr⟩ := Finset.mem_image.mp hrho
    exact ⟨z, mem_integralResiduePacket_iff.mpr ⟨hz, hzr⟩⟩

/-- The occupied packets form an exact disjoint cardinality partition. -/
theorem card_eq_sum_integralResiduePacket_over_occupied
    {N q : ℕ} (Z : Finset (IntVector N)) :
    Z.card = ∑ rho ∈ occupiedIntegralResidues q Z,
      (integralResiduePacket Z rho).card := by
  classical
  simpa [integralResiduePacket, integralResidueVector,
    occupiedIntegralResidues] using
    (Finset.card_eq_sum_card_fiberwise
      (s := Z) (t := occupiedIntegralResidues q Z)
      (f := integralResidueVector)
      (fun z hz ↦ Finset.mem_image.mpr ⟨z, hz, rfl⟩))

/-- The union of the occupied packets is literally the original set. -/
theorem biUnion_integralResiduePacket_over_occupied
    {N q : ℕ} (Z : Finset (IntVector N)) :
    (occupiedIntegralResidues q Z).biUnion
        (integralResiduePacket Z) = Z := by
  classical
  ext z
  constructor
  · intro hz
    obtain ⟨rho, _hrho, hzr⟩ := Finset.mem_biUnion.mp hz
    exact (mem_integralResiduePacket_iff.mp hzr).1
  · intro hz
    let rho : Fin N → ZMod q := integralResidueVector z
    have hrho : rho ∈ occupiedIntegralResidues q Z := by
      exact Finset.mem_image.mpr ⟨z, hz, rfl⟩
    exact Finset.mem_biUnion.mpr
      ⟨rho, hrho, mem_integralResiduePacket_iff.mpr ⟨hz, rfl⟩⟩

/-- Two members of one packet are coordinatewise congruent modulo `q`. -/
theorem intVectorCongruent_of_mem_same_integralResiduePacket
    {N q : ℕ} {Z : Finset (IntVector N)}
    {rho : Fin N → ZMod q} {z w : IntVector N}
    (hz : z ∈ integralResiduePacket Z rho)
    (hw : w ∈ integralResiduePacket Z rho) :
    IntVectorCongruent q z w := by
  intro i
  exact congrFun
    ((mem_integralResiduePacket_iff.mp hz).2.trans
      (mem_integralResiduePacket_iff.mp hw).2.symm) i

/-- Any pointwise property of `Z` restricts to each occupied packet. -/
theorem property_of_mem_integralResiduePacket
    {N q : ℕ} {Z : Finset (IntVector N)}
    {rho : Fin N → ZMod q} {P : IntVector N → Prop}
    (hP : ∀ z ∈ Z, P z) {z : IntVector N}
    (hz : z ∈ integralResiduePacket Z rho) : P z :=
  hP z (mem_integralResiduePacket_iff.mp hz).1

end

end TranslatedDepthSeven
