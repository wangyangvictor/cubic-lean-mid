import CubicTenVariables.RationalCodimensionTwoCoordinates
import Mathlib.LinearAlgebra.Dual.Lemmas

/-! A containment of rational kernels of two fixed integer matrices
persists over every field outside finitely many characteristics. The proof
constructs a rational row relation and clears its denominators. -/

set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.IntegralLinearKernelContainment
open Matrix LinearMap
open scoped BigOperators Classical

theorem exists_row_factor {n r s : ℕ} (B : Matrix (Fin r) (Fin n) ℚ)
    (C : Matrix (Fin s) (Fin n) ℚ)
    (h : LinearMap.ker B.mulVecLin ≤ LinearMap.ker C.mulVecLin) :
    ∃ R : Matrix (Fin s) (Fin r) ℚ, C = R*B := by
  let b (i : Fin r) := (LinearMap.proj i).comp B.mulVecLin
  let c (j : Fin s) := (LinearMap.proj j).comp C.mulVecLin
  have hrow (j : Fin s) : c j ∈ Submodule.span ℚ (Set.range b) := by
    apply mem_span_of_iInf_ker_le_ker
    intro x hx
    have hb : x ∈ LinearMap.ker B.mulVecLin := by
      change B.mulVec x = 0
      ext i
      exact (Submodule.mem_iInf _).mp hx i
    exact congrFun (h hb) j
  choose R hR using fun j => (Submodule.mem_span_range_iff_exists_fun ℚ).mp (hrow j)
  refine ⟨R,?_⟩
  ext j k
  have hr := congrArg (fun f : (Fin n → ℚ) →ₗ[ℚ] ℚ => f (Pi.single k 1)) (hR j)
  simpa [b,c,Matrix.mul_apply,Matrix.mulVec_single_one] using hr.symm

theorem exists_integral_row_relation {n r s : ℕ}
    (B : Matrix (Fin r) (Fin n) ℤ) (C : Matrix (Fin s) (Fin n) ℤ)
    (h : LinearMap.ker (B.map (Int.castRingHom ℚ)).mulVecLin ≤
      LinearMap.ker (C.map (Int.castRingHom ℚ)).mulVecLin) :
    ∃ (D : ℕ) (R : Matrix (Fin s) (Fin r) ℤ), 1 ≤ D ∧ (D : ℤ) • C = R*B := by
  obtain ⟨R,hR⟩ := exists_row_factor _ _ h
  have hden : (R.den : ℚ) ≠ 0 := by exact_mod_cast R.den_ne_zero
  have hnum : R.num.map (Int.castRingHom ℚ) = (R.den : ℚ) • R := by
    ext i j
    exact (div_eq_iff hden).mp (R.num_div_den i j) |>.trans (mul_comm _ _)
  refine ⟨R.den,R.num,Nat.one_le_iff_ne_zero.mpr R.den_ne_zero,?_⟩
  have he : ((R.den : ℚ) • C.map (Int.castRingHom ℚ)) =
      R.num.map (Int.castRingHom ℚ) * B.map (Int.castRingHom ℚ) := by
    rw [hnum,hR,Matrix.smul_mul]
  ext i j
  have hij := congrFun (congrFun he i) j
  simp only [Matrix.smul_apply, smul_eq_mul, Matrix.map_apply, Int.coe_castRingHom,
    Matrix.mul_apply] at hij ⊢
  exact_mod_cast hij

theorem exists_uniform_containment {n r s : ℕ}
    (B : Matrix (Fin r) (Fin n) ℤ) (C : Matrix (Fin s) (Fin n) ℤ)
    (h : LinearMap.ker (B.map (Int.castRingHom ℚ)).mulVecLin ≤
      LinearMap.ker (C.map (Int.castRingHom ℚ)).mulVecLin) :
    ∃ D : ℕ, 1 ≤ D ∧ ∀ p : ℕ, ¬ p ∣ D →
      ∀ (K : Type*) [Field K] [CharP K p],
        LinearMap.ker (B.map (Int.castRingHom K)).mulVecLin ≤
          LinearMap.ker (C.map (Int.castRingHom K)).mulVecLin := by
  obtain ⟨D,R,hD,he⟩ := exists_integral_row_relation B C h
  refine ⟨D,hD,?_⟩
  intro p hp K _ _ x hx
  have hD0 : (D : K) ≠ 0 := (CharP.cast_eq_zero_iff K p D).not.mpr hp
  have hm : (D : K) • C.map (Int.castRingHom K) =
      R.map (Int.castRingHom K) * B.map (Int.castRingHom K) := by
    ext i j
    have he' := congrArg (fun M : Matrix (Fin s) (Fin n) ℤ => (M i j : K)) he
    simpa only [Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply, Int.cast_mul,
      Int.cast_sum, Matrix.map_apply, Int.coe_castRingHom, Int.cast_natCast] using he'
  have hz := congrArg (fun M : Matrix (Fin s) (Fin n) K => M.mulVec x) hm
  dsimp only at hz
  rw [Matrix.smul_mulVec, ← Matrix.mulVec_mulVec, show (B.map (Int.castRingHom K)).mulVec x = 0 from hx,
    Matrix.mulVec_zero] at hz
  change (C.map (Int.castRingHom K)).mulVec x = 0
  exact (smul_eq_zero.mp hz).resolve_left hD0

end CubicTenVariables.IntegralLinearKernelContainment
