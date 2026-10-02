import CubicTenVariables.TerminalFiberCoordinates
import HessianTheorem11.ReducedDominantOpen

/-!
The literal closed two-block incidence over an arbitrary closed parameter set.
Its fixed-normal fiber has exactly the dimension of the original singular
section fiber. No projective properness or semicontinuity statement is used.
-/

noncomputable section
namespace CubicTenVariables.TerminalIncidenceFamily
open MvPolynomial HessianTheorem11
open TerminalSectionIncidence TerminalFiberCoordinates

/-- The actual affine incidence, restricted only by its normal parameter. -/
def incidenceOver {n : ℕ} (F : GeometricPolynomial n) (Z : Set (GeometricPoint n)) :
    Set (GeometricPoint (n + n)) :=
  {y | (polynomialMap (pointProjection n) y, polynomialMap (normalProjection n) y) ∈
      affineSectionSingularIncidence F ∧ polynomialMap (normalProjection n) y ∈ Z}

theorem closed_incidenceOver {n : ℕ} (F : GeometricPolynomial n)
    (Z : Set (GeometricPoint n)) (hZ : AlgebraicallyClosedSet Z) :
    AlgebraicallyClosedSet (incidenceOver F Z) := by
  let R : (Fin n ⊕ Fin n) → GeometricPolynomial (n + n) :=
    Sum.elim (pointProjection n) (normalProjection n)
  have hI := ReducedDominantOpen.closed_preimage R (affineSectionSingularIncidence_closed F)
  have he : polynomialMap R ⁻¹'
      {z : (Fin n ⊕ Fin n) → GeometricField |
        ((fun i => z (Sum.inl i)), (fun i => z (Sum.inr i))) ∈
          affineSectionSingularIncidence F} =
      {y : GeometricPoint (n+n) |
        (polynomialMap (pointProjection n) y, polynomialMap (normalProjection n) y) ∈
          affineSectionSingularIncidence F} := by
    ext y
    rfl
  rw [he] at hI
  have hN := ReducedDominantOpen.closed_preimage (normalProjection n) hZ
  apply Set.Subset.antisymm _ (subset_geometricClosure _)
  intro y hy
  exact ⟨geometricClosure_subset_closed (fun _ hz => hz.1) hI hy,
    geometricClosure_subset_closed (fun _ hz => hz.2) hN hy⟩

theorem normal_image_subset {n : ℕ} (F : GeometricPolynomial n)
    (Z : Set (GeometricPoint n)) :
    polynomialMap (normalProjection n) '' incidenceOver F Z ⊆ Z := by
  rintro _ ⟨y, hy, rfl⟩
  exact hy.2

/-- The actual point image of a normal fiber is the singular section fiber.
The assertion includes the zero normal with its literal incidence meaning. -/
theorem point_image_fiber {n : ℕ} (F : GeometricPolynomial n)
    (Z : Set (GeometricPoint n)) (v : GeometricPoint n) (hv : v ∈ Z) :
    polynomialMap (pointProjection n) ''
      {y | y ∈ incidenceOver F Z ∧ polynomialMap (normalProjection n) y = v} =
        sectionSingularFiber F v := by
  ext x
  constructor
  · rintro ⟨y, ⟨hy, hyv⟩, rfl⟩
    change (polynomialMap (pointProjection n) y, v) ∈ affineSectionSingularIncidence F
    rw [← hyv]
    exact hy.1
  · intro hx
    refine ⟨polynomialMap (fixedNormalSection v) x, ⟨?_, normalProjection_section v x⟩,
      pointProjection_section v x⟩
    change _ ∈ affineSectionSingularIncidence F ∧ _ ∈ Z
    simpa only [pointProjection_section, normalProjection_section] using And.intro hx hv

/-- The incidence fiber and the section singular fiber have exactly equal
reduced affine dimensions, using a genuine polynomial inverse. -/
theorem incidence_fiber_dimension {n : ℕ} (F : GeometricPolynomial n)
    (Z : Set (GeometricPoint n)) (v : GeometricPoint n) (hv : v ∈ Z) :
    affineDimension {y | y ∈ incidenceOver F Z ∧ polynomialMap (normalProjection n) y = v} =
      affineDimension (sectionSingularFiber F v) := by
  rw [← fiber_dimension, point_image_fiber F Z v hv]

end CubicTenVariables.TerminalIncidenceFamily
