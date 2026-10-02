import TranslatedDepthSeven.PrimeSubsetPrefixReservoirBridge
import TranslatedDepthSeven.QuantitativePrefixEffectiveResidualScaleSpecialization

/-!
# Terminal prefix vertices inherit the reservoir scale

A vertex in the terminal layer of the rooted prime-subset graph is literally
a fixed-cardinality reservoir member.  This file records that identification
in the direction needed by the quantitative surface argument and applies the
sharp full-reservoir determinant-degree estimate.
-/

namespace TranslatedDepthSeven

noncomputable section

open PrimeSubsetPrefix

/-- The modulus of a full-depth prefix vertex belongs to the old
fixed-cardinality modulus reservoir. -/
theorem terminalPrefix_modulus_mem_modulusReservoir
    {P : Finset ℕ} {depth : ℕ} (v : Vertex P depth)
    (hv : v.1.card = depth) :
    modulus v ∈ modulusReservoir P depth := by
  rw [modulusReservoir]
  exact Finset.mem_image.mpr
    ⟨v.1, Finset.mem_powersetCard.mpr
      ⟨(mem_vertices.mp v.2).1, hv⟩, rfl⟩

/-- Any lower bound imposed on every modulus in the fixed-cardinality
reservoir therefore holds at every full-depth prefix vertex. -/
theorem terminalPrefix_modulus_lower
    {P : Finset ℕ} {depth Q : ℕ}
    (hlower : ∀ q ∈ modulusReservoir P depth, Q ≤ q)
    (v : Vertex P depth) (hv : v.1.card = depth) :
    Q ≤ modulus v :=
  hlower (modulus v) (terminalPrefix_modulus_mem_modulusReservoir v hv)

/-- At the actual tangent-reservoir scale, every full-depth block has the
small terminal degree `ceil (4 H^eta)`.  The large empty-root degree is not
used in this statement. -/
theorem terminalPrefix_blockDegree_le_ceil_four_heightPower
    (p : Parameters) {P : Finset ℕ} {depth H : ℕ}
    (blockDegree : Vertex P depth → ℕ) (eta a : ℝ)
    (ha0 : 0 ≤ a) (ha : a ≤ 5 / 7)
    (hlower : ∀ q ∈ modulusReservoir P depth,
      manuscriptReservoirTarget normalizedSurfaceReservoirConstant
        p.T (5 / 7) ≤ q)
    (hblock : ∀ v,
      ((blockDegree v : ℕ) : ℝ) ≤ 2 * (H : ℝ) ^ eta *
        (1 + ((2 * surfaceTangentNaturalSide p : ℕ) : ℝ) ^ a /
          (modulus v : ℝ)))
    (v : Vertex P depth) (hv : v.1.card = depth) :
    blockDegree v ≤ ⌈4 * (H : ℝ) ^ eta⌉₊ := by
  apply terminalBlockDegree_le_ceil_four_heightPower
    p H (modulus v) (blockDegree v) eta a ha0 ha
  · exact terminalPrefix_modulus_lower hlower v hv
  · exact hblock v

/-- The total cutting degree, including the fixed base degree `b`, has the
corresponding terminal cap used by the two-cap persistent-cell theorem. -/
theorem terminalPrefix_totalDegree_le_add_ceil_four_heightPower
    (p : Parameters) {P : Finset ℕ} {depth H b : ℕ}
    (blockDegree : Vertex P depth → ℕ) (eta a : ℝ)
    (ha0 : 0 ≤ a) (ha : a ≤ 5 / 7)
    (hlower : ∀ q ∈ modulusReservoir P depth,
      manuscriptReservoirTarget normalizedSurfaceReservoirConstant
        p.T (5 / 7) ≤ q)
    (hblock : ∀ v,
      ((blockDegree v : ℕ) : ℝ) ≤ 2 * (H : ℝ) ^ eta *
        (1 + ((2 * surfaceTangentNaturalSide p : ℕ) : ℝ) ^ a /
          (modulus v : ℝ)))
    (v : Vertex P depth) (hv : v.1.card = depth) :
    b + blockDegree v ≤ b + ⌈4 * (H : ℝ) ^ eta⌉₊ :=
  Nat.add_le_add_left
    (terminalPrefix_blockDegree_le_ceil_four_heightPower
      p blockDegree eta a ha0 ha hlower hblock v hv) b

end

end TranslatedDepthSeven
