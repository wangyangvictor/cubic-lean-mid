import TranslatedDepthSeven.ProjectiveConeAffineChartInternal
import TranslatedDepthSeven.ProjectiveDegreeBoundedJacobianMinorInternal
import TranslatedDepthSeven.PrimeIdealJacobianSmoothPointInternal

/-! # One proper hypersurface contains the rational points of a nongeometric prime

For a homogeneous rational prime of projective dimension r and degree d,
a Jacobian minor of degree at most (N-r)(d-1) is nonzero in its coordinate
domain. A rational zero where that minor is nonzero would be smooth,
and hence would force geometric integrality. Thus every rational zero of
a nongeometrically integral prime belongs to this one proper section.

Only the already displayed smooth-point geometric-integrality input is
used. There is no assumption about Galois-orbit intersection degrees.
-/

namespace TranslatedDepthSeven
noncomputable section
open MvPolynomial Published
attribute [local instance] MvPolynomial.gradedAlgebra
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 400000

theorem exists_homogeneous_proper_divisor_of_nongeometric_rational_points
    (hSmooth : StandardAG.RationalProjectiveSmoothPointGeometricIntegrality)
    {N r d : ℕ} (hrN : r ≤ N)
    (I : Ideal (MvPolynomial (Fin (N + 1)) ℚ))
    (hprime : I.IsPrime)
    (hhom : I.IsHomogeneous (homogeneousSubmodule (Fin (N + 1)) ℚ))
    (hdegree : HasProjectiveDimensionDegree I r d)
    (hnot : ¬ GeometricallyPrimeMvPolynomialIdeal I) :
    ∃ (G : MvPolynomial (Fin (N + 1)) ℚ) (e : ℕ),
      e ≤ (N - r) * (d - 1) ∧ G.IsHomogeneous e ∧ G ∉ I ∧
      ∀ z : Fin (N + 1) → ℚ, z ∈ affineIdealZeroLocus I → eval z G = 0 := by
  classical
  letI : I.IsPrime := hprime
  obtain ⟨F, degrees, cols, hcols, _hdegrees, hFhom, hFmem, hminor,
      hminorhom, hminorDegree⟩ :=
    exists_projectiveDegree_bounded_homogeneous_jacobian_minor I hprime hhom hdegree
  let G := (Matrix.of (fun i j ↦ pderiv (cols j) (F i))).det
  refine ⟨G, ∑ j, (degrees j - 1), hminorDegree, hminorhom, hminor, ?_⟩
  intro z hz
  by_contra hGzero
  have hminor' : aeval z (selectedJacobianDeterminant F cols) ≠ 0 := by
    change eval z (selectedJacobianDeterminant F cols) ≠ 0
    have htranspose : selectedJacobianDeterminant F cols = G := by
      change (Matrix.of (fun i j ↦ pderiv (cols i) (F j))).det = G
      change ((Matrix.of (fun i j ↦ pderiv (cols j) (F i)))).transpose.det = G
      exact Matrix.det_transpose _
    rwa [htranspose]
  have hdim : ringKrullDim (MvPolynomial (Fin (N + 1)) ℚ ⧸ I) =
      ((N + 1 - (N - r) : ℕ) : WithBot ℕ∞) := by
    rw [show N + 1 - (N - r) = r + 1 by omega]
    exact hdegree.1
  have hsmooth : IsSmoothAffineIdealRationalPoint I z := by
    refine ⟨hz, ?_⟩
    exact rationalPoint_mem_smoothLocus_of_codimension_jacobian_minor
      I F hFmem cols hcols z
      ((mem_affineIdealZeroLocus_iff_le_ker_aeval I z).mp hz) hminor' hdim
  exact hnot (geometricallyPrime_of_smoothRationalPoint_on_homogeneous_affineCone
    hSmooth I hprime hhom z hsmooth)

end
end TranslatedDepthSeven
