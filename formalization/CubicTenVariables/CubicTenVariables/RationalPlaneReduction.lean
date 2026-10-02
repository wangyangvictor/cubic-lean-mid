import CubicTenVariables.RationalCodimensionTwoCoordinates
import CubicTenVariables.IntegralFourierCoordinates

/-! An actual integral two-equation model of a rational frequency plane,
and its exact reductions over fields. Outside the determinant's primes it
has the expected dimension and the Fourier second moment transports exactly. -/

set_option autoImplicit false
set_option maxHeartbeats 600000
noncomputable section
namespace CubicTenVariables.RationalPlaneReduction
open Matrix MvPolynomial RationalCodimensionTwoCoordinates IntegralFourierCoordinates
open HessianTheorem11 PolynomialRestriction ProjectiveFourierIdentity
open scoped BigOperators Classical

def plane {n : ℕ} (e : Fin 2 ↪ Fin n) (A : Matrix (Fin n) (Fin n) ℤ)
    (K : Type*) [CommRing K] : Submodule K (Fin n → K) :=
  (coordinatePlane e).comap (A.map (Int.castRingHom K)).transpose.mulVecLin

@[simp] theorem mem_plane {n : ℕ} (e : Fin 2 ↪ Fin n) (A : Matrix (Fin n) (Fin n) ℤ)
    (K : Type*) [CommRing K] (v : Fin n → K) :
    v ∈ plane e A K ↔ ∀ j, (A.map (Int.castRingHom K)).transpose.mulVec v (e j) = 0 :=
  Iff.rfl

theorem rational_eq {n : ℕ} (L : Submodule ℚ (Fin n → ℚ))
    (e : Fin 2 ↪ Fin n) (A : Matrix (Fin n) (Fin n) ℤ) (hA : A.det ≠ 0)
    (hL : L.map (A.map (Int.castRingHom ℚ)).transpose.mulVecLin = coordinatePlane e) :
    plane e A ℚ = L := by
  unfold plane
  rw [← hL]
  apply Submodule.comap_map_eq_of_injective
  exact mulVec_injective_iff_isUnit.mpr
    ((isUnit_transpose _).mpr (rational_isUnit A hA))

theorem image_eq {n : ℕ} (e : Fin 2 ↪ Fin n) (A : Matrix (Fin n) (Fin n) ℤ)
    (K : Type*) [Field K] (hA : IsUnit (A.map (Int.castRingHom K))) :
    (plane e A K).map (A.map (Int.castRingHom K)).transpose.mulVecLin = coordinatePlane e := by
  apply Submodule.map_comap_eq_of_surjective
  exact mulVec_surjective_iff_isUnit.mpr ((isUnit_transpose _).mpr hA)

theorem finrank_plane {n : ℕ} (e : Fin 2 ↪ Fin n) (A : Matrix (Fin n) (Fin n) ℤ)
    (K : Type*) [Field K] (hA : IsUnit (A.map (Int.castRingHom K))) :
    Module.finrank K (plane e A K) = n-2 := by
  let E := Submodule.equivMapOfInjective (A.map (Int.castRingHom K)).transpose.mulVecLin
    (mulVec_injective_iff_isUnit.mpr ((isUnit_transpose _).mpr hA)) (plane e A K)
  have h := E.finrank_eq
  rw [image_eq e A K hA] at h
  exact h.trans (finrank_coordinatePlane e)

theorem second_moment_eq {n : ℕ} (e : Fin 2 ↪ Fin n) (A : Matrix (Fin n) (Fin n) ℤ)
    (K : Type*) [Field K] [Fintype K] (hA : IsUnit (A.map (Int.castRingHom K)))
    (F : MvPolynomial (Fin n) ℤ) (ψ : AddChar K ℂ) :
    (∑ v : plane e A K, ‖normalizedFourierSum ψ (map (Int.castRingHom K) F) v.val‖^2) =
      ∑ v ∈ Finset.univ.filter (fun v : Fin n → K => ∀ j : Fin 2, v (e j) = 0),
        ‖normalizedFourierSum ψ (map (Int.castRingHom K) (restrict A F)) v‖^2 := by
  rw [map_restrict]
  have h := FourierLinearChange.submodule_second_moment ψ (map (Int.castRingHom K) F)
    (A.map (Int.castRingHom K)) hA (plane e A K)
  rw [image_eq e A K hA] at h
  rw [← h]
  symm
  exact Finset.sum_subtype _ (by simp [mem_coordinatePlane]) _

end CubicTenVariables.RationalPlaneReduction
