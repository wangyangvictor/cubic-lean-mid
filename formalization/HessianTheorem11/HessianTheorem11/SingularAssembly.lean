import HessianTheorem11.AffineDimension
import HessianTheorem11.SingularLinearAlgebra
import HessianTheorem11.SingularNumerics

/-!+# Conditional assembly on actual singular loci

These theorems refer to the actual polynomial, the actual singular set, and its
actual vanishing-ideal quotient dimension.  They isolate the precise remaining
geometric inputs.  They are not unconditional versions of Theorem 1.1.

`dimension_at_point` is the standard AG comparison at a smooth point of each
component.  `radial` and the exceptional-rank savings are bespoke statements
whose proofs from anisotropy are still required.  A component supported at the
origin is handled separately because the radial inequality does not apply to it.
-/

namespace HessianTheorem11

open Module

noncomputable section

theorem singularDimension_le_of_component_inputs {n d : ℕ}
    (F : RationalPolynomial n) {ι : Type*} [Fintype ι]
    (Z : ι → Set (GeometricPoint n)) (point : ι → GeometricPoint n)
    (cover : singularLocus F = ⋃ i, Z i)
    (component_inputs : ∀ i, Z i ⊆ {0} ∨
      (affineDimension (Z i) =
        (finrank GeometricField (affineTangentSpace (Z i) (point i)) : Dimension) ∧
      finrank GeometricField (affineTangentSpace (Z i) (point i)) + 3 ≤
        2 * (hessian (geometricPolynomial F) (point i)).rank))
    (component_numerics : ∀ i,
      (hessian (geometricPolynomial F) (point i)).rank +
          finrank GeometricField (affineTangentSpace (Z i) (point i)) ≤ n →
      finrank GeometricField (affineTangentSpace (Z i) (point i)) + 3 ≤
          2 * (hessian (geometricPolynomial F) (point i)).rank →
      finrank GeometricField (affineTangentSpace (Z i) (point i)) ≤ d) :
    singularDimension F ≤ d := by
  rw [singularDimension, cover]
  apply affineDimension_fintype_union_le
  intro i
  rcases component_inputs i with origin | ⟨dimension_at_point, radial_bound⟩
  · have hz := affineDimension_mono origin
    rw [affineDimension_singleton] at hz
    exact hz.trans (by simp)
  · have singular : ∀ y ∈ Z i, gradient (geometricPolynomial F) y = 0 := by
      intro y hy
      have hmem : y ∈ singularLocus F := by
        rw [cover]
        exact Set.mem_iUnion.mpr ⟨i, hy⟩
      exact hmem
    have tangent := hessian_rank_add_tangent_finrank_le
      (geometricPolynomial F) (Z i) singular (point i)
    have hd := component_numerics i tangent radial_bound
    rw [dimension_at_point]
    exact_mod_cast hd

theorem singularDimension_thirteen_le_seven_of_radial_component_inputs
    (F : RationalPolynomial 13) {ι : Type*} [Fintype ι]
    (Z : ι → Set (GeometricPoint 13)) (point : ι → GeometricPoint 13)
    (cover : singularLocus F = ⋃ i, Z i)
    (component_inputs : ∀ i, Z i ⊆ {0} ∨
      (affineDimension (Z i) =
        (finrank GeometricField (affineTangentSpace (Z i) (point i)) : Dimension) ∧
      finrank GeometricField (affineTangentSpace (Z i) (point i)) + 3 ≤
        2 * (hessian (geometricPolynomial F) (point i)).rank)) :
    singularDimension F ≤ 7 := by
  apply singularDimension_le_of_component_inputs F Z point cover component_inputs
  intro i tangent radial_bound
  exact SingularNumerics.component_le_seven_in_thirteen (by omega) radial_bound

theorem singularDimension_twelve_le_six_of_rank_five_component_inputs
    (F : RationalPolynomial 12) {ι : Type*} [Fintype ι]
    (Z : ι → Set (GeometricPoint 12)) (point : ι → GeometricPoint 12)
    (cover : singularLocus F = ⋃ i, Z i)
    (component_inputs : ∀ i, Z i ⊆ {0} ∨
      (affineDimension (Z i) =
        (finrank GeometricField (affineTangentSpace (Z i) (point i)) : Dimension) ∧
      finrank GeometricField (affineTangentSpace (Z i) (point i)) + 3 ≤
        2 * (hessian (geometricPolynomial F) (point i)).rank))
    (rank_five_saving : ∀ i, (hessian (geometricPolynomial F) (point i)).rank = 5 →
      finrank GeometricField (affineTangentSpace (Z i) (point i)) ≤ 6) :
    singularDimension F ≤ 6 := by
  apply singularDimension_le_of_component_inputs F Z point cover component_inputs
  intro i tangent radial_bound
  exact SingularNumerics.component_le_six_in_twelve (by omega) radial_bound (rank_five_saving i)

theorem singularDimension_eleven_le_five_of_exception_component_inputs
    (F : RationalPolynomial 11) {ι : Type*} [Fintype ι]
    (Z : ι → Set (GeometricPoint 11)) (point : ι → GeometricPoint 11)
    (cover : singularLocus F = ⋃ i, Z i)
    (component_inputs : ∀ i, Z i ⊆ {0} ∨
      (affineDimension (Z i) =
        (finrank GeometricField (affineTangentSpace (Z i) (point i)) : Dimension) ∧
      finrank GeometricField (affineTangentSpace (Z i) (point i)) + 3 ≤
        2 * (hessian (geometricPolynomial F) (point i)).rank))
    (exception_excluded : ∀ i,
      ¬ (finrank GeometricField (affineTangentSpace (Z i) (point i)) = 6 ∧
        (hessian (geometricPolynomial F) (point i)).rank = 5)) :
    singularDimension F ≤ 5 := by
  apply singularDimension_le_of_component_inputs F Z point cover component_inputs
  intro i tangent radial_bound
  exact SingularNumerics.component_le_five_in_eleven (by omega) radial_bound (exception_excluded i)

end

end HessianTheorem11
