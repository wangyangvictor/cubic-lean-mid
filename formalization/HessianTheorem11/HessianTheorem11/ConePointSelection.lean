import HessianTheorem11.AffineGeometry
import HessianTheorem11.TextbookGeometry

/-! A general textbook common-open point selection theorem. The input applies
to every closed irreducible affine cone, arbitrary polynomial equations, and
an arbitrary rectangular linear pencil. No cubic or incidence bound occurs. -/

noncomputable section
namespace HessianTheorem11
open MvPolynomial Module

structure GenericConePointData {n e a b : ℕ} (Z : Set (GeometricPoint n))
    (M : GeometricPoint n →ₗ[GeometricField] Matrix (Fin a) (Fin b) GeometricField)
    (q : Fin e → GeometricPolynomial n) where
  point : GeometricPoint n
  member : point ∈ Z
  nonzero : point ≠ 0
  dimension : affineDimension Z =
    (finrank GeometricField (affineTangentSpace Z point) : Dimension)
  radial : point ∈ affineTangentSpace Z point
  rank_maximal : ∀ y ∈ Z, (M y).rank ≤ (M point).rank
  detects_equations : point ∈ finiteEquationZeroSet q → Z ⊆ finiteEquationZeroSet q

/-- Finite intersection of nonempty opens in an irreducible variety, density
of its smooth locus in characteristic zero, openness of maximal matrix rank,
and the radial tangent of a cone. The last field avoids a proper closed
polynomial zero set when it is not the whole cone. -/
structure GenericConePointSelectionInput : Prop where
  select : ∀ {n e a b : ℕ} (Z : Set (GeometricPoint n)),
    AlgebraicallyClosedSet Z → GeometricallyIrreducible Z → IsAffineCone Z →
    ¬ Z ⊆ {0} →
    ∀ (M : GeometricPoint n →ₗ[GeometricField] Matrix (Fin a) (Fin b) GeometricField)
      (q : Fin e → GeometricPolynomial n), Nonempty (GenericConePointData Z M q)

def GenericConePointSelectionInput.choose
    (input : GenericConePointSelectionInput) {n e a b : ℕ}
    (Z : Set (GeometricPoint n)) (closed : AlgebraicallyClosedSet Z)
    (irreducible : GeometricallyIrreducible Z) (cone : IsAffineCone Z)
    (nonorigin : ¬ Z ⊆ {0})
    (M : GeometricPoint n →ₗ[GeometricField] Matrix (Fin a) (Fin b) GeometricField)
    (q : Fin e → GeometricPolynomial n) : GenericConePointData Z M q :=
  Classical.choice (input.select Z closed irreducible cone nonorigin M q)

end HessianTheorem11
