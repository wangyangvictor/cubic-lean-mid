import CubicTenVariables.FixedBoundaryUniversalPencil
import CubicTenVariables.FixedBoundaryPencilAffineSlices
import CubicTenVariables.SurfacePointCountByReciprocalPencil

/-!
# Uniform finite-field counts for one fixed leading form

The exceptional integer and the field-cardinality threshold are chosen
before every homogeneous surface equation and every nonzero boundary
scalar. Only the fixed ternary form, its degree, the desired leading
constant, and the two explicitly stated literature propositions enter
these choices. Lower coefficients have no effect on the constants.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section

namespace CubicTenVariables.FixedLeadingSurfaceFiniteFieldCount

open MvPolynomial TranslatedDepthSeven
open HessianTheorem11.PolynomialRestriction
open FixedBoundaryPencilUniformity FixedBoundaryPencilAffineSlices
open FixedLeadingFormGoodReduction FixedIntegralSurfacePointCount
open SurfacePointCountByPlaneSlices SurfacePointCountByReciprocalPencil

/-- Setting one variable equal to one cannot increase total degree. -/
theorem totalDegree_standardDehomogenization_le
    {R : Type*} [CommRing R] {n : ℕ}
    (F : MvPolynomial (Fin (n + 1)) R) :
    (standardDehomogenizationHom R n F).totalDegree ≤ F.totalDegree := by
  apply totalDegree_aeval_le_of_totalDegree_le_one
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp
  · exact (isHomogeneous_X (R := R) _).totalDegree_le

private theorem intCast_ne_zero_of_natAbsCast_ne_zero
    {K : Type*} [Field K] (s : ℤ) (hs : (s.natAbs : K) ≠ 0) :
    (s : K) ≠ 0 := by
  intro hz
  apply hs
  cases s with
  | ofNat n => simpa using hz
  | negSucc n => simpa [Int.cast_negSucc, add_comm] using congrArg Neg.neg hz

/-- The literal affine surface count has any prescribed leading constant
greater than one, uniformly over all remaining coefficients and fields
outside one fixed integer and above one fixed cardinality threshold. -/
theorem exists_uniform_count
    (integralityOpen : Literature.HomogeneousHypersurfaceIntegralityOpen)
    (curveWeil : Literature.AffinePlaneCurveWeil)
    {d : ℕ} (hd : 2 ≤ d)
    (k : MvPolynomial (Fin 3) ℤ) (hk : k.IsHomogeneous d)
    (hirr : Published.IsAbsolutelyIrreducible (map (Int.castRingHom ℚ) k))
    (K₀ : ℝ) (hK₀ : 1 < K₀) :
    ∃ N : ℕ, 0 < N ∧ ∃ T : ℝ, 0 ≤ T ∧
      ∀ (K : Type) [Field K] [Fintype K]
        (F : MvPolynomial (Fin 4) K) (b : K),
        F.IsHomogeneous d →
        restrict (pencilFrame (0 : K)) F = C b * map (Int.castRingHom K) k →
        (N : K) ≠ 0 → b ≠ 0 → T ≤ (Fintype.card K : ℝ) →
        (Nat.card {x : Fin 3 → K //
          eval x (standardDehomogenizationHom K 3 F) = 0} : ℝ) ≤
          K₀ * (Fintype.card K : ℝ) ^ 2 := by
  have hd1 : 1 ≤ d := by omega
  obtain ⟨Np, hNp, D, hcert⟩ := FixedBoundaryUniversalPencil.exists_uniform_certificate
    integralityOpen hd1 k hk hirr
  obtain ⟨s, hs, hred⟩ := exists_fixed_irreducible_reduction_certificate
    integralityOpen hd1 k hk hirr
  refine ⟨Np * s.natAbs, Nat.mul_pos hNp (Int.natAbs_pos.mpr hs),
    surfaceSliceThreshold curveWeil d hd1 (D + 1) K₀,
    surfaceSliceThreshold_nonneg curveWeil d hd1 (D + 1) K₀ hK₀, ?_⟩
  intro K _ _ F b hF hboundary hNK hb hcard
  have hNprod : (Np : K) * (s.natAbs : K) ≠ 0 := by
    simpa only [Nat.cast_mul] using hNK
  have hNpK : (Np : K) ≠ 0 := (mul_ne_zero_iff.mp hNprod).1
  have hsK : (s : K) ≠ 0 :=
    intCast_ne_zero_of_natAbsCast_ne_zero s (mul_ne_zero_iff.mp hNprod).2
  obtain ⟨Δ, hΔ, hD, hgood⟩ := hcert K F b hF hboundary hNpK hb
  have hkirr := (hred K hsK).2
  apply surface_zero_count_le_of_reciprocal_certificate curveWeil d hd1
    (standardDehomogenizationHom K 3 F) Δ hΔ D hD
    ((totalDegree_standardDehomogenization_le F).trans hF.totalDegree_le)
  · intro w
    rw [binarySlice_standardDehom_eq]
    exact affinePlaneSlice_ne_zero_of_boundary hd F hF b
      (map (Int.castRingHom K) k) hboundary hb hkirr (parameterValue w)
  · intro w hu hΔu
    have hprojective := hgood (fun _ : Fin 1 => (parameterValue w)⁻¹) hΔu
    have haffine := affinePlaneSlice_good_of_pencil hd F hF (parameterValue w) hu
      hprojective.1 hprojective.2
    constructor
    · rw [binarySlice_standardDehom_eq]
      exact haffine.1
    · rw [binarySlice_standardDehom_eq]
      exact haffine.2
  · exact hK₀
  · exact hcard

end CubicTenVariables.FixedLeadingSurfaceFiniteFieldCount
