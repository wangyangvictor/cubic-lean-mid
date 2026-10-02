import HessianTheorem11.SingularLinearAlgebra

/-!+# Explicit textbook AG interfaces

This module contains **no axioms** and supplies **no instances** of its input
structures.  A caller must provide the general textbook results explicitly.

The finite-cone-cover input packages finite irreducible decomposition, density
of the smooth locus in characteristic zero, and the openness of maximum matrix
rank.  Its equations can have arbitrary positive homogeneous degrees; its matrix
pencil is arbitrary and rectangular, with row/column counts independent of the
number of variables.  A nonzero cone component has a nonzero smooth point in the
open maximum-rank locus, and the radial vector belongs to its tangent space.

The determinantal-tangent input is the standard first-order description of a
rank locus: at a point of rank `r`, the differential of a matrix pencil maps its
kernel into its image.  For a symmetric pencil, pairing with another kernel
vector gives zero.  It is stated for an arbitrary subset `Z`, because all
`(r+1)`-minors that vanish on `Z` lie in its full vanishing ideal.  It therefore
uses the same reduced embedded tangent definition as the rest of the project.
This is the determinantal tangent calculation associated with Harris,
*Algebraic Geometry: A First Course*, Examples 14.16 and 16.18; it is not a
claim about special Gauss fibers or cubic Hessian dimensions.

Neither interface mentions anisotropy, cubic forms, radial weights, the source's
singular radial inequality, or any of the nine requested numerical targets.
-/

namespace HessianTheorem11

open MvPolynomial Module

noncomputable section

/-- The common zero set of a finite polynomial family. -/
def finiteEquationZeroSet {n e : ℕ} (q : Fin e → GeometricPolynomial n) :
    Set (GeometricPoint n) :=
  {x | ∀ j, eval x (q j) = 0}

/-- A finite cover with a chosen smooth maximum-rank point on each component
that is not supported at the origin.  Irreducibility itself is unnecessary in
the downstream API; it is used to obtain these simultaneous point properties. -/
structure HomogeneousConeComponentCover {n e a b : ℕ}
    (q : Fin e → GeometricPolynomial n)
    (M : GeometricPoint n →ₗ[GeometricField] Matrix (Fin a) (Fin b) GeometricField) where
  count : ℕ
  component : Fin count → Set (GeometricPoint n)
  point : Fin count → GeometricPoint n
  covers : finiteEquationZeroSet q = ⋃ i, component i
  component_property : ∀ i,
    component i ⊆ {0} ∨
      (point i ≠ 0 ∧ point i ∈ component i ∧
        affineDimension (component i) =
          (finrank GeometricField (affineTangentSpace (component i) (point i)) : Dimension) ∧
        point i ∈ affineTangentSpace (component i) (point i) ∧
        ∀ y ∈ component i, (M y).rank ≤ (M (point i)).rank)

/-- Explicit textbook finite-type AG input.  Every degree must be positive,
so the zero set is an affine cone through the origin. -/
structure FiniteHomogeneousConeCoverInput : Prop where
  cover : ∀ {n e a b : ℕ} (q : Fin e → GeometricPolynomial n)
    (degree : Fin e → ℕ),
    (∀ j, 0 < degree j) →
    (∀ j, (q j).IsHomogeneous (degree j)) →
    (M : GeometricPoint n →ₗ[GeometricField] Matrix (Fin a) (Fin b) GeometricField) →
    Nonempty (HomogeneousConeComponentCover q M)

/-- The quadratic specialization can be supplied independently if only
quadrics are wanted.  It remains a general statement about arbitrary quadrics
and arbitrary linear matrix pencils. -/
structure FiniteQuadraticConeCoverInput : Prop where
  cover : ∀ {n e a b : ℕ} (q : Fin e → GeometricPolynomial n),
    (∀ j, (q j).IsHomogeneous 2) →
    (M : GeometricPoint n →ₗ[GeometricField] Matrix (Fin a) (Fin b) GeometricField) →
    Nonempty (HomogeneousConeComponentCover q M)

theorem FiniteHomogeneousConeCoverInput.toQuadratic
    (input : FiniteHomogeneousConeCoverInput) : FiniteQuadraticConeCoverInput where
  cover q homogeneous M :=
    input.cover q (fun _ => 2) (fun _ => by norm_num) homogeneous M

/-- The general determinantal tangent theorem, for square symmetric linear
matrix pencils of any size and an independently sized affine source. -/
structure SymmetricDeterminantalTangentInput : Prop where
  tangent_kernel_pairing : ∀ {n m : ℕ}
    (M : GeometricPoint n →ₗ[GeometricField] Matrix (Fin m) (Fin m) GeometricField),
    (∀ z, (M z).transpose = M z) →
    ∀ (Z : Set (GeometricPoint n)) (x : GeometricPoint n), x ∈ Z →
      (∀ y ∈ Z, (M y).rank ≤ (M x).rank) →
      ∀ t ∈ affineTangentSpace Z x,
      ∀ u ∈ LinearMap.ker (M x).mulVecLin,
      ∀ v ∈ LinearMap.ker (M x).mulVecLin,
        dotProduct u ((M t).mulVec v) = 0

/-- An optional aggregate containing exactly the two general textbook inputs. -/
structure TextbookGeometryInputs : Prop extends
    FiniteHomogeneousConeCoverInput, SymmetricDeterminantalTangentInput

namespace HomogeneousConeComponentCover

variable {n e a b : ℕ} {q : Fin e → GeometricPolynomial n}
    {M : GeometricPoint n →ₗ[GeometricField] Matrix (Fin a) (Fin b) GeometricField}

theorem component_subset (cover : HomogeneousConeComponentCover q M) (i : Fin cover.count) :
    cover.component i ⊆ finiteEquationZeroSet q := by
  intro y hy
  rw [cover.covers]
  exact Set.mem_iUnion.mpr ⟨i, hy⟩

theorem equations_vanish (cover : HomogeneousConeComponentCover q M)
    (i : Fin cover.count) (y : GeometricPoint n) (hy : y ∈ cover.component i)
    (j : Fin e) : eval y (q j) = 0 :=
  cover.component_subset i hy j

theorem nonorigin_point_properties (cover : HomogeneousConeComponentCover q M)
    (i : Fin cover.count) (nonorigin : ¬ cover.component i ⊆ {0}) :
    cover.point i ≠ 0 ∧ cover.point i ∈ cover.component i ∧
      affineDimension (cover.component i) =
        (finrank GeometricField
          (affineTangentSpace (cover.component i) (cover.point i)) : Dimension) ∧
      cover.point i ∈ affineTangentSpace (cover.component i) (cover.point i) ∧
      ∀ y ∈ cover.component i, (M y).rank ≤ (M (cover.point i)).rank :=
  (cover.component_property i).resolve_left nonorigin

/-- Apply the separate determinantal input on a non-origin component. -/
theorem tangent_kernel_pairing {n e m : ℕ} {q : Fin e → GeometricPolynomial n}
    {M : GeometricPoint n →ₗ[GeometricField] Matrix (Fin m) (Fin m) GeometricField}
    (cover : HomogeneousConeComponentCover q M)
    (input : SymmetricDeterminantalTangentInput)
    (symmetric : ∀ z, (M z).transpose = M z)
    (i : Fin cover.count) (nonorigin : ¬ cover.component i ⊆ {0}) :
    ∀ t ∈ affineTangentSpace (cover.component i) (cover.point i),
      ∀ u ∈ LinearMap.ker (M (cover.point i)).mulVecLin,
      ∀ v ∈ LinearMap.ker (M (cover.point i)).mulVecLin,
        dotProduct u ((M t).mulVec v) = 0 := by
  obtain ⟨_, member, _, _, maximal⟩ := cover.nonorigin_point_properties i nonorigin
  exact input.tangent_kernel_pairing M symmetric (cover.component i) (cover.point i)
    member maximal

end HomogeneousConeComponentCover

/-- Choose cover data from a supplied quadratic-cover theorem. -/
def FiniteQuadraticConeCoverInput.chooseCover
    (input : FiniteQuadraticConeCoverInput) {n e a b : ℕ}
    (q : Fin e → GeometricPolynomial n) (homogeneous : ∀ j, (q j).IsHomogeneous 2)
    (M : GeometricPoint n →ₗ[GeometricField] Matrix (Fin a) (Fin b) GeometricField) :
    HomogeneousConeComponentCover q M :=
  Classical.choice (input.cover q homogeneous M)

end

end HessianTheorem11
