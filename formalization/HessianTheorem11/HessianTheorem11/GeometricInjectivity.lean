import HessianTheorem11.HessianLinearity
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
The rational Hessian pencil remains injective after extending scalars.
The proof applies rational linear functionals to its rational coefficient
expansion, then uses algebraic dual separation. No determinant hypothesis
or source-specific geometric input is assumed.
-/

noncomputable section

namespace HessianTheorem11

open MvPolynomial

/-- Applying a rational linear functional to each extended coefficient
commutes with evaluation of the rational Hessian pencil. -/
theorem linearFunctional_hessian_entry
    {L : Type*} [Field L] [Algebra ℚ L] {n : ℕ}
    (F : RationalPolynomial n) (hF : F.IsHomogeneous 3)
    (φ : L →ₗ[ℚ] ℚ) (x : Fin n → L) (i j : Fin n) :
    φ (hessian (map (algebraMap ℚ L) F) x i j) =
      hessian F (fun k => φ (x k)) i j := by
  rw [hessian_entry_expansion (hF.map _), hessian_entry_expansion hF]
  simp only [pderiv_map, coeff_map, map_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [mul_comm, ← Algebra.smul_def, φ.map_smul]
  simp [smul_eq_mul, mul_comm]

/-- An anisotropic rational cubic has no nonzero Hessian-zero vector
over any extension field. -/
theorem baseChange_hessian_zero_iff
    {L : Type*} [Field L] [Algebra ℚ L] {n : ℕ}
    (F : AnisotropicCubic n) (x : Fin n → L) :
    hessian (map (algebraMap ℚ L) F.polynomial) x = 0 ↔ x = 0 := by
  constructor
  · intro hx
    ext k
    apply (Module.forall_dual_apply_eq_zero_iff ℚ (x k)).mp
    intro φ
    have hr : hessian F.polynomial (fun l => φ (x l)) = 0 := by
      ext i j
      rw [← linearFunctional_hessian_entry F.polynomial F.homogeneous φ x i j, hx]
      simp
    exact congrFun (anisotropic_hessian_zero_iff F _ hr) k
  · rintro rfl
    exact hessian_zero (F.homogeneous.map _)

theorem geometric_hessian_zero_iff
    {n : ℕ} (F : AnisotropicCubic n) (x : GeometricPoint n) :
    hessian (geometricPolynomial F.polynomial) x = 0 ↔ x = 0 :=
  baseChange_hessian_zero_iff F x

/-- Hessian-map injectivity is preserved by arbitrary extension of the
rational ground field, proved for the actual polynomial Hessian. -/
theorem baseChange_hessian_injective
    {L : Type*} [Field L] [Algebra ℚ L] {n : ℕ}
    (F : AnisotropicCubic n) :
    Function.Injective (hessian (map (algebraMap ℚ L) F.polynomial)) := by
  intro x y hxy
  apply sub_eq_zero.mp
  apply (baseChange_hessian_zero_iff F (x - y)).mp
  rw [hessian_sub (F.homogeneous.map _), hxy, sub_self]

theorem geometric_hessian_injective {n : ℕ} (F : AnisotropicCubic n) :
    Function.Injective (hessian (geometricPolynomial F.polynomial)) :=
  baseChange_hessian_injective F

theorem matrix_eq_zero_of_rank_eq_zero
    {K m n : Type*} [Field K] [Fintype m] [Fintype n]
    (A : Matrix m n K) (hA : A.rank = 0) : A = 0 := by
  classical
  have hr : LinearMap.range A.mulVecLin = ⊥ :=
    Submodule.finrank_eq_zero.mp hA
  have hz : A.mulVecLin = 0 := LinearMap.range_eq_bot.mp hr
  ext i j
  have he := congrFun (LinearMap.congr_fun hz (Pi.single j 1)) i
  simpa [Matrix.mulVecLin, Matrix.mulVec, dotProduct, Pi.single_apply, mul_ite] using he

/-- The actual geometric Hessian rank-zero locus consists exactly of the
origin. This closes the base stratum in the source's rank-locus arguments. -/
theorem rankAtMost_zero_locus {n : ℕ} (F : AnisotropicCubic n) :
    rankAtMostLocus F.polynomial 0 = {0} := by
  ext x
  constructor
  · intro hx
    apply (geometric_hessian_zero_iff F x).mp
    apply matrix_eq_zero_of_rank_eq_zero
    exact Nat.eq_zero_of_le_zero hx
  · intro hx
    have hx' : x = 0 := hx
    subst x
    simp [rankAtMostLocus, hessian_zero (geometric_homogeneous F.homogeneous)]

end HessianTheorem11
