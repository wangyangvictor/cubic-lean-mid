import CubicTenVariables.ProjectiveFourierIdentity

/-! Scalar invariance of the actual finite-field Fourier sum of a
homogeneous zero set, including the normalized correction at frequency zero.
No character nontriviality, positive degree or literature input is needed. -/

set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.FourierScalarInvariance
open MvPolynomial FiniteFieldFourier ProjectiveFourierIdentity

variable {K : Type*} [Field K] [Fintype K] {n d : ℕ}

/-- Reindexing the homogeneous zero set proves exact scalar invariance
of its Fourier sum, with the project's positive character phase. -/
theorem zeroFiberSum_smul (ψ : AddChar K ℂ)
    (F : MvPolynomial (Fin n) K) (hF : F.IsHomogeneous d)
    (v : Fin n → K) (a : K) (ha : a ≠ 0) :
    zeroFiberSum ψ F (a • v) = zeroFiberSum ψ F v := by
  classical
  simpa only [zeroFiberSum,smul_dotProduct,smul_eq_mul] using
    PrimeScalarAveraging.zeroFiberSum_scalar_phase ψ F hF v a ha

/-- The complete normalized T is invariant, including at frequency zero:
the correction is unchanged because a nonzero scalar cannot annihilate v. -/
theorem normalizedFourierSum_smul (ψ : AddChar K ℂ)
    (F : MvPolynomial (Fin n) K) (hF : F.IsHomogeneous d)
    (v : Fin n → K) (a : K) (ha : a ≠ 0) :
    normalizedFourierSum ψ F (a • v) = normalizedFourierSum ψ F v := by
  classical
  have hz : a • v = 0 ↔ v = 0 := by simp [ha]
  simp only [normalizedFourierSum,zeroFiberSum_smul ψ F hF v a ha,hz]

/-- The same literal identity for an integral homogeneous polynomial
reduced to any finite field; degree three is an immediate specialization. -/
theorem normalizedFourierSum_map_smul (ψ : AddChar K ℂ)
    (F : MvPolynomial (Fin n) ℤ) (hF : F.IsHomogeneous d)
    (v : Fin n → K) (a : K) (ha : a ≠ 0) :
    normalizedFourierSum ψ (map (Int.castRingHom K) F) (a • v) =
      normalizedFourierSum ψ (map (Int.castRingHom K) F) v :=
  normalizedFourierSum_smul ψ _ (hF.map _) v a ha

end CubicTenVariables.FourierScalarInvariance
