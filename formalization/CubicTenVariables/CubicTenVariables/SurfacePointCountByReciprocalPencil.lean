import CubicTenVariables.SurfacePointCountByFiniteExceptionalSlices
import CubicTenVariables.FixedIntegralSurfacePointCount

/-!
# The reciprocal parameter in the actual affine surface count

The fixed projective pencil has parameter t and the affine slices have
third coordinate u=1/t. The exceptional affine slices are u=0 and the
reciprocals of the roots of its certificate. Their number is at most D+1,
with no dependence on the coefficients or on the finite field.
-/

set_option autoImplicit false
set_option maxHeartbeats 1500000
noncomputable section

namespace CubicTenVariables.SurfacePointCountByReciprocalPencil

open MvPolynomial
open BinarySliceCounting BinarySliceGeometry
open FixedIntegralSurfacePointCount
open SurfacePointCountByPlaneSlices SurfacePointCountByFiniteExceptionalSlices
open scoped Classical

def exceptionalAssignments {K : Type} [Field K] [Fintype K]
    (Δ : MvPolynomial (Fin 1) K) : Finset (Complement planeCoordinates → K) :=
  (inverseExceptionalParameters Δ).image (fun u _ => u)

theorem card_exceptionalAssignments_le
    {K : Type} [Field K] [Fintype K]
    (Δ : MvPolynomial (Fin 1) K) (hΔ : Δ ≠ 0) :
    (exceptionalAssignments Δ).card ≤ Δ.totalDegree + 1 :=
  Finset.card_image_le.trans (card_inverseExceptionalParameters_le Δ hΔ)

theorem good_of_not_mem_exceptionalAssignments
    {K : Type} [Field K] [Fintype K]
    (Δ : MvPolynomial (Fin 1) K) (w : Complement planeCoordinates → K)
    (hw : w ∉ exceptionalAssignments Δ) :
    parameterValue w ≠ 0 ∧ eval (fun _ : Fin 1 => (parameterValue w)⁻¹) Δ ≠ 0 := by
  apply good_of_not_mem_inverseExceptionalParameters
  intro hu
  apply hw
  apply Finset.mem_image.mpr
  refine ⟨parameterValue w, hu, ?_⟩
  funext i
  rw [complement_eq_parameterIndex i]
  rfl

/-- A literal good-projective-pencil certificate supplies the sharp leading
constant in the affine point count once its affine curve maps are identified.
The all-slices-nonzero condition is retained, including u=0. -/
theorem surface_zero_count_le_of_reciprocal_certificate
    (curveWeil : Literature.AffinePlaneCurveWeil)
    {K : Type} [Field K] [Fintype K]
    (d : ℕ) (hd : 1 ≤ d) (f : MvPolynomial (Fin 3) K)
    (Δ : MvPolynomial (Fin 1) K) (hΔ : Δ ≠ 0)
    (D : ℕ) (hD : Δ.totalDegree ≤ D)
    (hfdeg : f.totalDegree ≤ d)
    (hall : ∀ w : Complement planeCoordinates → K, slice planeCoordinates f w ≠ 0)
    (hgood : ∀ w : Complement planeCoordinates → K,
      parameterValue w ≠ 0 → eval (fun _ : Fin 1 => (parameterValue w)⁻¹) Δ ≠ 0 →
      1 ≤ (slice planeCoordinates f w).totalDegree ∧
      IsDomain (MvPolynomial (Fin 2) (AlgebraicClosure K) ⧸
        Ideal.span {map (algebraMap K (AlgebraicClosure K)) (slice planeCoordinates f w)}))
    (K₀ : ℝ) (hK₀ : 1 < K₀)
    (hcard : surfaceSliceThreshold curveWeil d hd (D + 1) K₀ ≤ (Fintype.card K : ℝ)) :
    (Nat.card {x : Fin 3 → K // eval x f = 0} : ℝ) ≤ K₀ * (Fintype.card K : ℝ) ^ 2 := by
  apply surface_zero_count_le_K_mul_sq_of_finite_exceptional_slices_card_ge
    curveWeil d hd planeCoordinates f (exceptionalAssignments Δ) (D + 1)
    ((card_exceptionalAssignments_le Δ hΔ).trans (Nat.add_le_add_right hD 1))
    hfdeg hall
  · intro w hw
    obtain ⟨hu, hΔu⟩ := good_of_not_mem_exceptionalAssignments Δ w hw
    exact (hgood w hu hΔu).1
  · intro w hw
    obtain ⟨hu, hΔu⟩ := good_of_not_mem_exceptionalAssignments Δ w hw
    exact (hgood w hu hΔu).2
  · exact hK₀
  · exact hcard

end CubicTenVariables.SurfacePointCountByReciprocalPencil
