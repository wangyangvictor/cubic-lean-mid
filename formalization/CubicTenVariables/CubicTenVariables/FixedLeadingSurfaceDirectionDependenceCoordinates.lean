import CubicTenVariables.FixedLeadingSurfaceDirectionDependence
import CubicTenVariables.FrameRestrictionIrreducibility
import HessianTheorem11.PolynomialWeightTransport
import TranslatedDepthSeven.GradedLinearSubstitution

/-!
# Directional dependence after invertible linear substitution

Linear substitution commutes with homogeneous components. A matrix with
a displayed inverse remains invertible after extending the coefficient
field, so geometric irreducibility of the top component is preserved.
The preceding noncylindrical-form theorem then supplies the directional
degree hypothesis needed by the parallel-line count, in any invertible
system of rational coordinates.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section

namespace CubicTenVariables.FixedLeadingSurfaceDirectionDependence

open MvPolynomial HessianTheorem11.PolynomialRestriction
open HessianTheorem11.PolynomialWeightTransport
open CubicTenVariables.FrameRestrictionIrreducibility

/-- Literal invertible matrix substitution is an algebra equivalence.
This construction uses polynomial substitution identities, so it works
over finite fields as well. -/
def restrictionAlgEquivOfInverseMatrices
    {R : Type*} [CommRing R] {n : ℕ}
    (A B : Matrix (Fin n) (Fin n) R) (hAB : A * B = 1) (hBA : B * A = 1) :
    MvPolynomial (Fin n) R ≃ₐ[R] MvPolynomial (Fin n) R :=
  AlgEquiv.ofAlgHom (aeval (linearForms A)) (aeval (linearForms B))
    (by
      apply MvPolynomial.algHom_ext
      intro i
      change restrict A (restrict B (X i)) = X i
      rw [restrict_restrict, hBA, restrict_one])
    (by
      apply MvPolynomial.algHom_ext
      intro i
      change restrict B (restrict A (X i)) = X i
      rw [restrict_restrict, hAB, restrict_one])

theorem homogeneousComponent_restrict
    {K : Type*} [Field K] {m n : ℕ}
    (A : Matrix (Fin n) (Fin m) K) (g : MvPolynomial (Fin n) K) (d : ℕ) :
    homogeneousComponent d (restrict A g) = restrict A (homogeneousComponent d g) :=
  TranslatedDepthSeven.homogeneousComponent_aeval_linear
    (linearForms A) (homogeneous_linearForms A) d g

/-- Irreducibility of a displayed homogeneous component after coefficient
extension survives an invertible coordinate substitution. -/
theorem irreducible_map_topComponent_restrict_of_inverse
    {K L : Type*} [Field K] [Field L] {n d : ℕ}
    (ρ : K →+* L) (A B : Matrix (Fin n) (Fin n) K)
    (hAB : A * B = 1) (hBA : B * A = 1)
    (g : MvPolynomial (Fin n) K)
    (hirr : Irreducible (map ρ (homogeneousComponent d g))) :
    Irreducible (map ρ (homogeneousComponent d (restrict A g))) := by
  rw [homogeneousComponent_restrict, map_restrict]
  have hAB' : A.map ρ * B.map ρ = 1 := by
    rw [← Matrix.map_mul, hAB]
    simp
  have hBA' : B.map ρ * A.map ρ = 1 := by
    rw [← Matrix.map_mul, hBA]
    simp
  exact hirr.map (restrictionAlgEquivOfInverseMatrices
    (A.map ρ) (B.map ρ) hAB' hBA').toMulEquiv

theorem coordinateMatrix_mul_symm
    {K : Type*} [Field K] {n : ℕ}
    (e : (Fin n → K) ≃ₗ[K] (Fin n → K)) :
    coordinateMatrix e * coordinateMatrix e.symm = 1 := by
  change LinearMap.toMatrix' e.toLinearMap * LinearMap.toMatrix' e.symm.toLinearMap = 1
  rw [← LinearMap.toMatrix'_comp]
  have he : e.toLinearMap.comp e.symm.toLinearMap = LinearMap.id := by
    ext x i
    simp
  rw [he, LinearMap.toMatrix'_id]

/-- The exact directional-degree conclusion for the coordinate matrix of
an arbitrary invertible linear change of variables. In particular it
applies to every nonzero rational direction presented as the first column
of a rational basis. -/
theorem degreeOf_zero_pos_restrict_coordinateMatrix
    {K : Type*} [Field K] {d : ℕ} (hd : 2 ≤ d)
    (e : (Fin 3 → K) ≃ₗ[K] (Fin 3 → K)) (g : MvPolynomial (Fin 3) K)
    (hirr : Irreducible (map (algebraMap K (AlgebraicClosure K))
      (homogeneousComponent d g))) :
    0 < (restrict (coordinateMatrix e) g).degreeOf 0 := by
  apply degreeOf_zero_pos_of_geometrically_irreducible_topComponent hd
  exact irreducible_map_topComponent_restrict_of_inverse
    (algebraMap K (AlgebraicClosure K)) (coordinateMatrix e) (coordinateMatrix e.symm)
    (coordinateMatrix_mul_symm e) (by simpa using coordinateMatrix_mul_symm e.symm)
    g hirr

end CubicTenVariables.FixedLeadingSurfaceDirectionDependence
