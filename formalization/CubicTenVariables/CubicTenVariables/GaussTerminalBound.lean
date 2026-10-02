import CubicTenVariables.GaussGraphProjection
import CubicTenVariables.GaussDualDimension
import CubicTenVariables.FiberJumpDimension

/-!
The actual geometric Gauss terminal bound, in normalized projective
fiber dimensions. The affine graph, its dimension, its normal-image
dimension, and the strict generic threshold are all constructed/proved.
Closedness of the large-fiber parameter set and reduction modulo primes
are not assumed or asserted.
-/

noncomputable section
namespace CubicTenVariables.GaussTerminalBound
open MvPolynomial HessianTheorem11 BibleProjectiveGeometry
open TerminalFiberCoordinates AffineProductGeometry

/-- The literal point fiber of the closed affine Gauss graph at v. -/
def fiber {n : ℕ} (F : GeometricPolynomial n) (v : GeometricPoint n) :
    Set (GeometricPoint n) := {x | join x v ∈ GaussGraph.graph F}

theorem fiber_closed {n : ℕ} (F : GeometricPolynomial n) (v : GeometricPoint n) :
    AlgebraicallyClosedSet (fiber F v) := by
  have he : polynomialMap (fixedNormalSection v) = fun x => join x v := by
    funext x
    ext i
    refine Fin.addCases ?_ ?_ i <;> intro j <;>
      simp only [fixedNormalSection, polynomialMap, join, Fin.addCases_left,
        Fin.addCases_right, eval_X, eval_C]
  have h := ReducedDominantOpen.closed_preimage (fixedNormalSection v) (GaussGraph.graph_closed F)
  rw [he] at h
  exact h

theorem fiber_isAffineCone {n : ℕ} (F : GeometricPolynomial n)
    (hF : F.IsHomogeneous 3) (v : GeometricPoint n) : IsAffineCone (fiber F v) := by
  intro a x hx
  exact (by simpa only [point_join, normal_join, one_smul] using
    GaussGraph.graph_bicone_smul F hF (join x v) hx a 1)

theorem fiber_subset_sectionSingularFiber {n : ℕ} (F : GeometricPolynomial n)
    (hF : F.IsHomogeneous 3) (v : GeometricPoint n) :
    fiber F v ⊆ TerminalSectionIncidence.sectionSingularFiber F v := by
  intro x hx
  simpa only [point_join, normal_join] using GaussGraph.graph_mem_incidence F hF (join x v) hx

/-- Point coordinates and the literal two-block projection fiber have
identical dimensions, by the actual polynomial inverse x↦(x,v). -/
theorem fiber_dimension {n : ℕ} (F : GeometricPolynomial n) (v : GeometricPoint n) :
    affineDimension (fiber F v) =
      affineDimension {p | p ∈ GaussGraph.graph F ∧ polynomialMap (normalProjection n) p = v} := by
  have he : polynomialMap (pointProjection n) ''
      {p | p ∈ GaussGraph.graph F ∧ polynomialMap (normalProjection n) p = v} = fiber F v := by
    ext x
    constructor
    · rintro ⟨p, ⟨hp, hpv⟩, rfl⟩
      change join (polynomialMap (pointProjection n) p) v ∈ GaussGraph.graph F
      rw [← hpv, join_projections]
      exact hp
    · intro hx
      exact ⟨join x v, ⟨hx, normal_join x v⟩, point_join x v⟩
  simpa only [he] using TerminalFiberCoordinates.fiber_dimension (GaussGraph.graph F) v

/-- Actual projective large-fiber normals, via the standard normalized
point charts of the fixed-normal closed cone. -/
def badNormals {n : ℕ} (F : GeometricPolynomial n) (t : ℕ) : Set (GeometricPoint n) :=
  {v | (t : Dimension) ≤ projectiveDimension (fiber F v)}

theorem badNormals_eq_largeFiberParameters {n : ℕ} (F : GeometricPolynomial n)
    (hF : F.IsHomogeneous 3) (t : ℕ) :
    badNormals F t = FiberJumpDimension.largeFiberParameters (normalProjection n)
      (GaussGraph.graph F) (t + 1) := by
  ext v
  change (t : Dimension) ≤ projectiveDimension (fiber F v) ↔ _
  rw [TerminalProjectiveDimension.nat_le_projectiveDimension_iff _
    (fiber_closed F v) (fiber_isAffineCone F hF v) t, fiber_dimension]
  rfl

/-- The geometric Gauss large-fiber bound for the actual constructed
closed graph. The source hypotheses themselves imply the generic threshold. -/
theorem badNormals_closure_dimension_le {n t : ℕ} (F : AnisotropicCubic n)
    (hn : 4 ≤ n) (ht : n < 3 * t) :
    affineDimension (geometricClosure (badNormals (geometricPolynomial F.polynomial) t)) ≤
      ((n - (t + 2) : ℕ) : Dimension) := by
  rw [badNormals_eq_largeFiberParameters _ (geometric_homogeneous F.homogeneous)]
  have h := FiberJumpDimension.closure_dimension_le (normalProjection n)
    (GaussGraph.graph (geometricPolynomial F.polynomial))
    (GaussGraph.graph_closed _) (GaussGraph.anisotropic_graph_irreducible F hn)
    (GaussGraph.anisotropic_graph_dimension F hn)
    (GaussGraph.anisotropic_normal_projection_dimension F hn)
    (Nat.succ_pos t) (GaussDualDimension.terminal_threshold_above_generic F hn ht)
  simpa only [Nat.add_assoc] using h

/-- The source cone convention: take nonzero geometric normals, close,
then adjoin the origin. Empty strata are included without any convention
identifying the empty set's dimension with zero. -/
theorem nonzero_badNormals_cone_dimension_le {n t : ℕ} (F : AnisotropicCubic n)
    (hn : 4 ≤ n) (ht : n < 3 * t) :
    affineDimension (geometricClosure
      {v : GeometricPoint n | (t : Dimension) ≤ projectiveDimension
        (fiber (geometricPolynomial F.polynomial) v) ∧ v ≠ 0} ∪ {0}) ≤
      ((n - (t + 2) : ℕ) : Dimension) := by
  rw [affineDimension_union, affineDimension_origin]
  apply max_le
  · apply le_trans (affineDimension_mono (geometricClosure_mono
      (show {v : GeometricPoint n | (t : Dimension) ≤ projectiveDimension
          (fiber (geometricPolynomial F.polynomial) v) ∧ v ≠ 0} ⊆
        badNormals (geometricPolynomial F.polynomial) t from fun _ hv => hv.1)))
    exact badNormals_closure_dimension_le F hn ht
  · exact_mod_cast Nat.zero_le (n - (t + 2))

/-- The ten-variable fourth Gauss stratum has affine cone dimension≤4.
This concerns all geometric normals, unlike the stronger rational-closure bound. -/
theorem ten_fourth_gauss_cone_dimension_le_four (F : AnisotropicCubic 10) :
    affineDimension (geometricClosure
      {v : GeometricPoint 10 | (4 : Dimension) ≤ projectiveDimension
        (fiber (geometricPolynomial F.polynomial) v) ∧ v ≠ 0} ∪ {0}) ≤ (4 : Dimension) := by
  simpa using nonzero_badNormals_cone_dimension_le (t := 4) F (by norm_num) (by norm_num)

end CubicTenVariables.GaussTerminalBound
