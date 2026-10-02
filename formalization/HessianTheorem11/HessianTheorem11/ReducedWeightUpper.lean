import HessianTheorem11.NonzeroLimitTransport
import Mathlib.LinearAlgebra.Matrix.Block

/-! Determinants and inverses of actual strictly weighted unitriangular matrices. -/
noncomputable section
namespace HessianTheorem11.ReducedOrdinaryBigCell
open Matrix NonzeroLimitTransport
variable {K : Type*} [Field K] {n : ℕ}

theorem upper_blockTriangular (w : Fin n → ℤ)
    (V : Matrix (Fin n) (Fin n) K) (hV : WeightUpperUnipotent w V) :
    V.BlockTriangular w := by
  intro i j hij
  exact hV.2 i j (by rintro rfl; omega) hij.le

theorem upper_same_block (w : Fin n → ℤ)
    (V : Matrix (Fin n) (Fin n) K) (hV : WeightUpperUnipotent w V) (a : ℤ) :
    V.toSquareBlock w a = 1 := by
  classical
  ext i j
  change V i.val j.val = if i = j then 1 else 0
  by_cases hij : i = j
  · subst j
    simp [hV.1]
  · rw [if_neg hij]
    exact hV.2 _ _ (fun h => hij (Subtype.ext h)) (by rw [i.property,j.property])

theorem upper_det_one (w : Fin n → ℤ)
    (V : Matrix (Fin n) (Fin n) K) (hV : WeightUpperUnipotent w V) : V.det = 1 := by
  rw [(upper_blockTriangular w V hV).det]
  simp [upper_same_block w V hV]

theorem upper_inverse (w : Fin n → ℤ)
    (V : Matrix (Fin n) (Fin n) K) (hV : WeightUpperUnipotent w V) :
    WeightUpperUnipotent w V⁻¹ := by
  classical
  have hu : IsUnit V.det := by rw [upper_det_one w V hV]; exact isUnit_one
  letI := V.invertibleOfIsUnitDet hu
  have ht := Matrix.blockTriangular_inv_of_blockTriangular (upper_blockTriangular w V hV)
  have heq (i j : Fin n) (hij : w i = w j) : V⁻¹ i j = (1 : Matrix (Fin n) (Fin n) K) i j := by
    have hm := congrArg (fun A : Matrix (Fin n) (Fin n) K => A i j)
      (Matrix.mul_nonsing_inv V hu)
    change (∑ k, V i k * V⁻¹ k j) = _ at hm
    rw [Finset.sum_eq_single i] at hm
    · simpa only [hV.1, one_mul] using hm
    · intro k hk hki
      by_cases hw : w i < w k
      · rw [ht (by omega), mul_zero]
      · rw [hV.2 i k (Ne.symm hki) (by omega), zero_mul]
    · simp
  constructor
  · intro i
    simpa using heq i i rfl
  · intro i j hij hw
    by_cases hlt : w j < w i
    · exact ht hlt
    · rw [heq i j (by omega)]
      simp [hij]

end HessianTheorem11.ReducedOrdinaryBigCell
