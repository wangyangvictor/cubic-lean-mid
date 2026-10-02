import CubicTenVariables.FourierLinearChange
import Mathlib.Algebra.CharP.Basic

/-! Integral coordinate changes keep the actual polynomial and dual
Fourier transformation, uniformly outside the determinant's prime divisors. -/

set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.IntegralFourierCoordinates
open MvPolynomial Matrix HessianTheorem11 PolynomialRestriction
open scoped BigOperators

theorem rational_isUnit {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) (hA : A.det ≠ 0) :
    IsUnit (A.map (Int.castRingHom ℚ)) := by
  apply (Matrix.isUnit_iff_isUnit_det _).mpr
  apply isUnit_iff_ne_zero.mpr
  have hdet := (Int.castRingHom ℚ).map_det A
  change (A.det : ℚ) = (A.map (Int.castRingHom ℚ)).det at hdet
  rw [← hdet]
  exact_mod_cast hA

theorem residue_isUnit {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ)
    (p : ℕ) (hp : ¬ p ∣ A.det.natAbs) (K : Type*) [Field K] [CharP K p] :
    IsUnit (A.map (Int.castRingHom K)) := by
  apply (Matrix.isUnit_iff_isUnit_det _).mpr
  apply isUnit_iff_ne_zero.mpr
  have hdet := (Int.castRingHom K).map_det A
  change (A.det : K) = (A.map (Int.castRingHom K)).det at hdet
  rw [← hdet]
  intro hz
  have hd := (CharP.intCast_eq_zero_iff K p A.det).mp hz
  exact hp (by simpa only [Int.natAbs_natCast] using Int.natAbs_dvd_natAbs.mpr hd)

theorem anisotropic_restrict_integral {n : ℕ} (F : MvPolynomial (Fin n) ℤ)
    (hF : Anisotropic (map (Int.castRingHom ℚ) F))
    (A : Matrix (Fin n) (Fin n) ℤ) (hA : A.det ≠ 0) :
    Anisotropic (map (Int.castRingHom ℚ) (restrict A F)) := by
  rw [map_restrict]
  exact anisotropic_restrict _ _ hF
    (mulVec_injective_iff_isUnit.mpr (rational_isUnit A hA))

theorem normalized_restrict_integral {n : ℕ} (F : MvPolynomial (Fin n) ℤ)
    (A : Matrix (Fin n) (Fin n) ℤ) (p : ℕ) (hp : ¬ p ∣ A.det.natAbs)
    (K : Type*) [Field K] [Fintype K] [CharP K p]
    (ψ : AddChar K ℂ) (v : Fin n → K) :
    ProjectiveFourierIdentity.normalizedFourierSum ψ (map (Int.castRingHom K) (restrict A F))
      ((A.map (Int.castRingHom K)).transpose.mulVec v) =
      ProjectiveFourierIdentity.normalizedFourierSum ψ (map (Int.castRingHom K) F) v := by
  rw [map_restrict]
  exact FourierLinearChange.normalized_restrict_transpose ψ _ _ (residue_isUnit A p hp K) v

end CubicTenVariables.IntegralFourierCoordinates
