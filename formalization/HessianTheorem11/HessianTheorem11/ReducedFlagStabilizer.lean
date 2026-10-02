import HessianTheorem11.ReducedRationalFlagDescent
import Mathlib.LinearAlgebra.Matrix.Transvection

/-! Recovering an indexed weighted flag from its actual special-linear
stabilizer and its weight multiplicities. This is finite linear algebra,
with no algebraic-group or invariant-theory input. -/
noncomputable section
namespace HessianTheorem11.ReducedFlagStabilizer
open Matrix Module
variable {K : Type*} [Field K] {n : ℕ}

def flagStabilizer (B : Matrix (Fin n) (Fin n) K) (w : Fin n → ℤ) :
    Set (Matrix (Fin n) (Fin n) K) :=
  {A | A.det = 1 ∧ ∀ a v, v ∈ weightFlag B w a → A.mulVec v ∈ weightFlag B w a}

theorem frame_expansion (B : Matrix (Fin n) (Fin n) K)
    (hB : Function.Injective B.mulVec) (v : Fin n → K) :
    v = ∑ i, ((frameEquiv B hB).symm v i) • (fun j => B j i) := by
  have h := (frameEquiv B hB).apply_symm_apply v
  rw [frameEquiv_apply] at h
  calc
    v = B.mulVec ((frameEquiv B hB).symm v) := h.symm
    _ = _ := by
      ext j
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct]
      congr 1
      ext i
      rw [mul_comm]

theorem mem_weightFlag_of_inverse_coordinates (B : Matrix (Fin n) (Fin n) K)
    (hB : Function.Injective B.mulVec) (w : Fin n → ℤ) (a : ℤ) (v : Fin n → K)
    (hv : ∀ i, a < w i → (frameEquiv B hB).symm v i = 0) :
    v ∈ weightFlag B w a := by
  classical
  rw [frame_expansion B hB v]
  apply Submodule.sum_mem
  intro i hi
  by_cases hw : w i ≤ a
  · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i,hw,rfl⟩)
  · rw [hv i (by omega), zero_smul]
    exact Submodule.zero_mem _

theorem inverse_mulVec_eq (B : Matrix (Fin n) (Fin n) K)
    (hB : Function.Injective B.mulVec) (v : Fin n → K) :
    B⁻¹.mulVec v = (frameEquiv B hB).symm v := by
  apply hB
  rw [Matrix.mulVec_mulVec]
  rw [Matrix.mul_nonsing_inv B ((Matrix.isUnit_iff_isUnit_det B).mp
    (Matrix.mulVec_injective_iff_isUnit.mp hB)), Matrix.one_mulVec]
  exact ((frameEquiv B hB).apply_symm_apply v).symm

def frameTransvection (B : Matrix (Fin n) (Fin n) K) (i j : Fin n) :
    Matrix (Fin n) (Fin n) K := B * Matrix.transvection j i 1 * B⁻¹

theorem frameTransvection_apply (B : Matrix (Fin n) (Fin n) K)
    (hB : Function.Injective B.mulVec) (i j : Fin n) (v : Fin n → K) :
    (frameTransvection B i j).mulVec v =
      v + ((frameEquiv B hB).symm v i) • (fun k => B k j) := by
  rw [frameTransvection, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, inverse_mulVec_eq B hB]
  have ht (u : Fin n → K) : (Matrix.transvection j i (1 : K)).mulVec u =
      u + u i • (Pi.single j (1 : K) : Fin n → K) := by
    simp only [Matrix.transvection, Matrix.add_mulVec, Matrix.one_mulVec, Matrix.single_mulVec, one_mul]
    congr 1
    ext k
    by_cases hk : k = j <;> simp [Function.update_apply, Pi.single_apply, hk]
  rw [ht, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_single_one]
  congr 1
  exact (frameEquiv B hB).apply_symm_apply v

theorem frameTransvection_mem (B : Matrix (Fin n) (Fin n) K)
    (hB : Function.Injective B.mulVec) (w : Fin n → ℤ) (i j : Fin n)
    (hji : w j < w i) : frameTransvection B i j ∈ flagStabilizer B w := by
  classical
  have hne : j ≠ i := by rintro rfl; omega
  have hdet := (Matrix.isUnit_iff_isUnit_det B).mp (Matrix.mulVec_injective_iff_isUnit.mp hB)
  refine ⟨?_,?_⟩
  · rw [frameTransvection, Matrix.det_mul, Matrix.det_mul,
      Matrix.det_transvection_of_ne j i hne, mul_one, Matrix.det_nonsing_inv, Ring.inverse_eq_inv]
    exact mul_inv_cancel₀ (isUnit_iff_ne_zero.mp hdet)
  · intro a v hv
    rw [frameTransvection_apply B hB]
    apply Submodule.add_mem _ hv
    by_cases hi : w i ≤ a
    · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j,by omega,rfl⟩)
    · rw [inverse_coordinate_zero_of_mem_weightFlag B hB w a v hv i (by omega), zero_smul]
      exact Submodule.zero_mem _

/-- Equality of the actual SL parabolics, together with the unchanged weight
list, determines every integer-indexed filtration step. -/
theorem weightFlag_eq_of_stabilizer_eq
    (B C : Matrix (Fin n) (Fin n) K)
    (hB : Function.Injective B.mulVec) (hC : Function.Injective C.mulVec)
    (w : Fin n → ℤ) (he : flagStabilizer B w = flagStabilizer C w) :
    weightFlag B w = weightFlag C w := by
  classical
  funext a
  have hdim : finrank K (weightFlag B w a) = finrank K (weightFlag C w a) := by
    rw [ReducedRationalDescent.weightFlag_finrank B hB,
      ReducedRationalDescent.weightFlag_finrank C hC]
  apply (Submodule.eq_of_le_of_finrank_eq ?_ hdim.symm).symm
  intro v hv
  by_contra hn
  have hex : ∃ i, a < w i ∧ (frameEquiv B hB).symm v i ≠ 0 := by
    by_contra hnot
    push_neg at hnot
    exact hn (mem_weightFlag_of_inverse_coordinates B hB w a v hnot)
  obtain ⟨i,hi,hvi⟩ := hex
  have hle : weightFlag B w a ≤ weightFlag C w a := by
    apply Submodule.span_le.mpr
    rintro x ⟨j,hj,rfl⟩
    have ht := frameTransvection_mem B hB w i j (by omega)
    rw [he] at ht
    have htmem := ht.2 a v hv
    rw [frameTransvection_apply B hB] at htmem
    have hs := (weightFlag C w a).sub_mem htmem hv
    have hs' : ((frameEquiv B hB).symm v i) • (fun k => B k j) ∈
        weightFlag C w a := by simpa using hs
    have h := (weightFlag C w a).smul_mem (((frameEquiv B hB).symm v i)⁻¹) hs'
    simpa [smul_smul, hvi] using h
  have heq := Submodule.eq_of_le_of_finrank_eq hle hdim
  exact hn (heq.symm ▸ hv)

end HessianTheorem11.ReducedFlagStabilizer
