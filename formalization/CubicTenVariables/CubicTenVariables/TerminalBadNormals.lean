import CubicTenVariables.TerminalComponentSelection
import CubicTenVariables.RationalClosureIdempotent

/-!
The literal affine bad-normal set is a cone, without a semicontinuity
assumption. Its rational generators are dense in every component of their
rational closure. If the bad-normal set is nonempty, these generators
(including the origin) all have the required large literal incidence fiber.
This does not assert closedness of the bad-normal set or equality of its
rational points with those of its closure.
-/

noncomputable section
namespace CubicTenVariables.TerminalBadNormals
open MvPolynomial HessianTheorem11 Matrix
open TerminalSectionIncidence RationalConeClosure

/-- Actual bad affine normals, defined by the dimension of the displayed
section-singularity equations. At a nonzero normal this is the actual
embedded singular locus of the restricted polynomial. -/
def badNormals {n : ℕ} (F : GeometricPolynomial n) (t : ℕ) : Set (GeometricPoint n) :=
  {v | ((t + 1 : ℕ) : Dimension) ≤ affineDimension (sectionSingularFiber F v)}

/-- Scaling a normal preserves all incidence equations; scaling to zero
can enlarge the fiber, so this statement includes that case. -/
theorem sectionSingularFiber_subset_smul {n : ℕ} (F : GeometricPolynomial n)
    (v : GeometricPoint n) (a : GeometricField) :
    sectionSingularFiber F v ⊆ sectionSingularFiber F (a • v) := by
  rintro x ⟨hF, hpair, hm⟩
  refine ⟨hF, ?_, ?_⟩
  · rw [smul_dotProduct, hpair, smul_zero]
  · intro i j
    change (a * v i) * gradient F x j - (a * v j) * gradient F x i = 0
    calc
      _ = a * (v i * gradient F x j - v j * gradient F x i) := by ring
      _ = 0 := by rw [hm i j, mul_zero]

theorem badNormals_isAffineCone {n : ℕ} (F : GeometricPolynomial n) (t : ℕ) :
    IsAffineCone (badNormals F t) := by
  intro a v hv
  exact hv.trans (affineDimension_mono (sectionSingularFiber_subset_smul F v a))

theorem zero_mem_badNormals_of_nonempty {n : ℕ} (F : GeometricPolynomial n) (t : ℕ)
    (hne : (badNormals F t).Nonempty) : (0 : GeometricPoint n) ∈ badNormals F t := by
  obtain ⟨v, hv⟩ := hne
  simpa only [zero_smul] using badNormals_isAffineCone F t 0 v hv

/-- The literal rational-closure construction is a closed cone, without
requiring prior closedness of the bad-normal set. -/
theorem rational_badNormals_closed_cone {n : ℕ} (F : GeometricPolynomial n) (t : ℕ) :
    AlgebraicallyClosedSet (rationalConeClosure (badNormals F t)) ∧
      IsAffineCone (rationalConeClosure (badNormals F t)) :=
  ⟨rationalConeClosure_closed _, rationalConeClosure_isAffineCone _
    (badNormals_isAffineCone F t)⟩

/-- Actual rational generators remain in the actual bad-normal set when
it is nonempty, including the adjoined origin. -/
theorem rational_generators_subset_badNormals {n : ℕ} (F : GeometricPolynomial n) (t : ℕ)
    (hne : (badNormals F t).Nonempty) :
    rationalEmbedding '' (rationalPoints (badNormals F t) ∪ {0}) ⊆ badNormals F t := by
  rintro _ ⟨q, hq | hq, rfl⟩
  · exact hq
  · rw [Set.mem_singleton_iff] at hq
    simpa only [hq, rationalEmbedding_zero] using zero_mem_badNormals_of_nonempty F t hne

/-- Each actual irreducible component has a dense set of parameters with
the required literal large fibers. No component-selection premise remains. -/
theorem exists_dense_large_fibers_in_component {n : ℕ}
    (F : GeometricPolynomial n) (t : ℕ) (hne : (badNormals F t).Nonempty)
    (Z : Set (GeometricPoint n))
    (hZ : IsIrreducibleComponent (rationalConeClosure (badNormals F t)) Z) :
    ∃ A, geometricClosure A = Z ∧ ∀ v ∈ A,
      ((t + 1 : ℕ) : Dimension) ≤ affineDimension (sectionSingularFiber F v) := by
  let A := rationalEmbedding '' (rationalPoints (badNormals F t) ∪ {0})
  refine ⟨A ∩ Z, ?_, ?_⟩
  · exact RationalConeComponents.closure_inter_component_of_dense _ A Z
      (rationalConeClosure_closed _) (closure_rational_generators _) hZ
  · intro v hv
    exact rational_generators_subset_badNormals F t hne hv.1

/-- A sufficiently large dominating component is constructed for each
component of the actual rational closure, directly from the bad-normal
definition rather than from a supplied incidence-family hypothesis. -/
theorem exists_large_incidence_component {n z t : ℕ}
    (F : GeometricPolynomial n) (hne : (badNormals F t).Nonempty)
    (Z : Set (GeometricPoint n))
    (hZ : IsIrreducibleComponent (rationalConeClosure (badNormals F t)) Z)
    (hz : affineDimension Z = (z : Dimension)) :
    ∃ Y, IsIrreducibleComponent (TerminalIncidenceFamily.incidenceOver F Z) Y ∧
      geometricClosure (polynomialMap (TerminalFiberCoordinates.normalProjection n) '' Y) = Z ∧
      ((z + t + 1 : ℕ) : Dimension) ≤ affineDimension Y := by
  obtain ⟨A, hd, hf⟩ := exists_dense_large_fibers_in_component F t hne Z hZ
  obtain ⟨Y, hY, hdom, hdim⟩ := TerminalComponentSelection.exists_large_incidence_component
    F Z A hZ.closed hZ.irreducible hz hd (by omega : 0 < t + 1) hf
  exact ⟨Y, hY, hdom, by simpa only [Nat.add_assoc] using hdim⟩

end CubicTenVariables.TerminalBadNormals
