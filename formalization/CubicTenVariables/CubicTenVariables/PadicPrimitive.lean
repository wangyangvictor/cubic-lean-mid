import Mathlib.NumberTheory.Padics.PadicIntegers
import HessianTheorem11.HessianLinearity
import HessianTheorem11.LocalCubicNormalForm

/-!
# Primitive integral representatives of p-adic vectors

Divide by a nonzero coordinate of maximal norm. Every resulting coordinate
is an actual p-adic integer, and the chosen coordinate is exactly one.
For homogeneous polynomials this preserves being a zero, and for cubics it
preserves the exact rank of the actual Hessian. These are normalization
theorems for a supplied nonzero vector, not local existence assertions.
-/

noncomputable section

namespace CubicTenVariables.PadicPrimitive

open MvPolynomial HessianTheorem11

/-- Normalize by a maximal-norm coordinate, obtaining actual p-adic integer
coordinates and a coordinate equal to one. -/
theorem exists_integral_multiple_with_coordinate_one (p : ℕ) [Fact p.Prime]
    {n : ℕ} (x : Fin n → ℚ_[p]) (hx : x ≠ 0) :
    ∃ c : ℚ_[p], c ≠ 0 ∧ ∃ y : Fin n → ℤ_[p],
      (∀ i, (y i : ℚ_[p]) = c * x i) ∧ ∃ j, y j = 1 := by
  classical
  obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := by
    by_contra! h
    exact hx (funext h)
  obtain ⟨j, _, hjmax⟩ := Finset.exists_max_image Finset.univ (fun i => ‖x i‖)
    ⟨i, Finset.mem_univ i⟩
  have hj : x j ≠ 0 := by
    intro hz
    have hle := hjmax i (Finset.mem_univ i)
    rw [hz, norm_zero] at hle
    exact (not_le_of_gt (norm_pos_iff.mpr hi)) hle
  let c := (x j)⁻¹
  have hc : c ≠ 0 := inv_ne_zero hj
  have hbound (k : Fin n) : ‖c * x k‖ ≤ 1 := by
    calc
      ‖c * x k‖ = ‖x k‖ / ‖x j‖ := by
        simp only [c, norm_mul, norm_inv, div_eq_mul_inv, mul_comm]
      _ ≤ 1 := (div_le_one (norm_pos_iff.mpr hj)).mpr
        (hjmax k (Finset.mem_univ k))
  let y : Fin n → ℤ_[p] := fun k => ⟨c * x k, hbound k⟩
  refine ⟨c, hc, y, fun _ => rfl, j, ?_⟩
  apply PadicInt.ext
  change (x j)⁻¹ * x j = 1
  exact inv_mul_cancel₀ hj

/-- The normalized vector is primitive in the literal sense that one
p-adic integer coordinate is a unit. -/
theorem exists_primitive_integral_multiple (p : ℕ) [Fact p.Prime]
    {n : ℕ} (x : Fin n → ℚ_[p]) (hx : x ≠ 0) :
    ∃ c : ℚ_[p], c ≠ 0 ∧ ∃ y : Fin n → ℤ_[p],
      (∀ i, (y i : ℚ_[p]) = c * x i) ∧ ∃ j, IsUnit (y j) := by
  obtain ⟨c, hc, y, hy, j, hj⟩ := exists_integral_multiple_with_coordinate_one p x hx
  exact ⟨c, hc, y, hy, j, hj ▸ isUnit_one⟩

/-- Nonzero scalar multiplication preserves precisely the zeros of an
actual homogeneous polynomial, in every degree. -/
theorem eval_smul_eq_zero_iff {K : Type*} [Field K] {n d : ℕ}
    (F : MvPolynomial (Fin n) K) (hF : F.IsHomogeneous d)
    (c : K) (hc : c ≠ 0) (x : Fin n → K) :
    eval (c • x) F = 0 ↔ eval x F = 0 := by
  have hscale := LocalCubicNormalForm.homogeneous_eval₂_common_scalar
    F hF (RingHom.id K) x c
  change eval₂ (RingHom.id K) (fun i => c * x i) F = 0 ↔ eval x F = 0
  rw [hscale, eval₂_id]
  exact mul_eq_zero.trans (or_iff_right (pow_ne_zero d hc))

/-- A nonzero scalar preserves the exact rank of the cubic Hessian pencil.
This holds over every field and uses the actual polynomial Hessian. -/
theorem hessian_rank_smul_eq {K : Type*} [Field K] {n : ℕ}
    (F : MvPolynomial (Fin n) K) (hF : F.IsHomogeneous 3)
    (c : K) (hc : c ≠ 0) (x : Fin n → K) :
    (hessian F (c • x)).rank = (hessian F x).rank := by
  classical
  rw [hessian_smul hF, Matrix.smul_eq_diagonal_mul]
  apply Matrix.rank_mul_eq_right_of_isUnit_det
  rw [Matrix.det_diagonal]
  exact isUnit_iff_ne_zero.mpr (Finset.prod_ne_zero_iff.mpr fun _ _ => hc)

/-- For the actual first partial of a rational cubic, a nonzero scalar
preserves nonvanishing after every extension of the rational field. -/
theorem eval₂_partial_smul_ne_zero_iff {K : Type*} [Field K] [Algebra ℚ K]
    {n : ℕ} (F : MvPolynomial (Fin n) ℚ) (hF : F.IsHomogeneous 3)
    (i : Fin n) (c : K) (hc : c ≠ 0) (x : Fin n → K) :
    eval₂ (algebraMap ℚ K) (c • x) (pderiv i F) ≠ 0 ↔
      eval₂ (algebraMap ℚ K) x (pderiv i F) ≠ 0 := by
  simpa only [eval_map] using not_congr
    (eval_smul_eq_zero_iff (map (algebraMap ℚ K) (pderiv i F))
      (hF.pderiv.map _) c hc x)

/-- The same normalization preserves a supplied homogeneous p-adic zero. -/
theorem exists_integral_zero_with_coordinate_one (p : ℕ) [Fact p.Prime]
    {n d : ℕ} (F : MvPolynomial (Fin n) ℚ_[p]) (hF : F.IsHomogeneous d)
    (x : Fin n → ℚ_[p]) (hx : x ≠ 0) (hFx : eval x F = 0) :
    ∃ c : ℚ_[p], c ≠ 0 ∧ ∃ y : Fin n → ℤ_[p],
      (∀ i, (y i : ℚ_[p]) = c * x i) ∧ (∃ j, y j = 1) ∧
      eval (fun i => (y i : ℚ_[p])) F = 0 := by
  obtain ⟨c, hc, y, hy, hj⟩ := exists_integral_multiple_with_coordinate_one p x hx
  have hvec : (fun i => (y i : ℚ_[p])) = c • x := funext hy
  refine ⟨c, hc, y, hy, hj, ?_⟩
  rw [hvec]
  exact (eval_smul_eq_zero_iff F hF c hc x).mpr hFx

/-- For an actual rational homogeneous cubic, normalize a supplied p-adic
zero while preserving the exact rank of its scalar-extended Hessian. -/
theorem exists_integral_zero_preserving_hessian_rank (p : ℕ) [Fact p.Prime]
    {n : ℕ} (F : MvPolynomial (Fin n) ℚ) (hF : F.IsHomogeneous 3)
    (x : Fin n → ℚ_[p]) (hx : x ≠ 0)
    (hFx : eval₂ (algebraMap ℚ ℚ_[p]) x F = 0) :
    ∃ c : ℚ_[p], c ≠ 0 ∧ ∃ y : Fin n → ℤ_[p],
      (∀ i, (y i : ℚ_[p]) = c * x i) ∧ (∃ j, y j = 1) ∧
      eval₂ (algebraMap ℚ ℚ_[p]) (fun i => (y i : ℚ_[p])) F = 0 ∧
      (hessian (map (algebraMap ℚ ℚ_[p]) F) (fun i => (y i : ℚ_[p]))).rank =
        (hessian (map (algebraMap ℚ ℚ_[p]) F) x).rank := by
  have hFx' : eval x (map (algebraMap ℚ ℚ_[p]) F) = 0 := by
    simpa only [eval_map] using hFx
  obtain ⟨c, hc, y, hy, hj, hFy⟩ := exists_integral_zero_with_coordinate_one p
    (map (algebraMap ℚ ℚ_[p]) F) (hF.map _) x hx hFx'
  have hvec : (fun i => (y i : ℚ_[p])) = c • x := funext hy
  refine ⟨c, hc, y, hy, hj, ?_, ?_⟩
  · simpa only [eval_map] using hFy
  · rw [hvec]
    exact hessian_rank_smul_eq _ (hF.map _) c hc x

/-- Normalize a supplied nonsingular p-adic zero of a rational cubic,
retaining its nonzero partial and the exact rank of its Hessian. -/
theorem exists_integral_smooth_zero_preserving_hessian_rank (p : ℕ) [Fact p.Prime]
    {n : ℕ} (F : MvPolynomial (Fin n) ℚ) (hF : F.IsHomogeneous 3)
    (x : Fin n → ℚ_[p]) (hx : x ≠ 0)
    (hFx : eval₂ (algebraMap ℚ ℚ_[p]) x F = 0)
    (hsmooth : ∃ i, eval₂ (algebraMap ℚ ℚ_[p]) x (pderiv i F) ≠ 0) :
    ∃ c : ℚ_[p], c ≠ 0 ∧ ∃ y : Fin n → ℤ_[p],
      (∀ i, (y i : ℚ_[p]) = c * x i) ∧ (∃ j, y j = 1) ∧
      eval₂ (algebraMap ℚ ℚ_[p]) (fun i => (y i : ℚ_[p])) F = 0 ∧
      (∃ i, eval₂ (algebraMap ℚ ℚ_[p]) (fun j => (y j : ℚ_[p])) (pderiv i F) ≠ 0) ∧
      (hessian (map (algebraMap ℚ ℚ_[p]) F) (fun i => (y i : ℚ_[p]))).rank =
        (hessian (map (algebraMap ℚ ℚ_[p]) F) x).rank := by
  obtain ⟨c, hc, y, hy, hj, hFy, hrank⟩ :=
    exists_integral_zero_preserving_hessian_rank p F hF x hx hFx
  have hvec : (fun i => (y i : ℚ_[p])) = c • x := funext hy
  refine ⟨c, hc, y, hy, hj, hFy, ?_, hrank⟩
  obtain ⟨i, hi⟩ := hsmooth
  refine ⟨i, ?_⟩
  rw [hvec]
  exact (eval₂_partial_smul_ne_zero_iff F hF i c hc x).mpr hi

end CubicTenVariables.PadicPrimitive
