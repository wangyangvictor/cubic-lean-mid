import CubicTenVariables.BinaryQuadraticLifting
import CubicTenVariables.AffinePolynomialSlice
import CubicTenVariables.QuadraticHessianConstant
import CubicTenVariables.QuadraticRankTwoCoordinates
import CubicTenVariables.BinarySliceCounting

/-!
# Root counting after a nondegenerate binary affine restriction

The binary slices are actual substitutions into the original polynomial.
Their degree, reduced degree, and nonzero quadratic determinant are derived
from the displayed data, before applying the proved binary lifting bound.
-/

noncomputable section
namespace CubicTenVariables.RankTwoPolynomialLifting
open MvPolynomial HessianTheorem11
open AffinePolynomialSlice QuadraticHessianConstant

/-- Every translate of the same nondegenerate binary direction has the
proved root-count bound, since the reduced Hessian is constant. -/
theorem card_affine_binary_slice_zeros_le {n : ℕ}
    (F : MvPolynomial (Fin n) ℤ) (p : ℕ) [Fact p.Prime]
    (hF : F.totalDegree ≤ 3)
    (hred : (map (Int.castRingHom (ZMod p)) F).totalDegree ≤ 2)
    (B : Matrix (Fin n) (Fin 2) ℤ)
    (hB : ((B.transpose * hessian F 0 * B).det : ZMod p) ≠ 0)
    (b : Fin n → ℤ) (s : ℕ) :
    (Finset.univ.filter fun z : Fin 2 → ZMod (p^s) =>
      eval₂ (Int.castRingHom (ZMod (p^s))) z (affineSlice F B b) = 0).card ≤
        (s+1)*p^s := by
  apply BinaryCubicPerturbation.card_polynomial_zeros_le_succ_mul_pow
  · exact (totalDegree_affineSlice_le F B b).trans hF
  · rw [map_affineSlice]
    exact (totalDegree_affineSlice_le _ _ _).trans hred
  · rw [map_affineSlice, hessian_affineSlice_origin,
      hessian_eq_origin _ hred, hessian_map_origin]
    let φ := Int.castRingHom (ZMod p)
    have hmap : (B.transpose * hessian F 0 * B).map φ =
        (B.map φ).transpose * (hessian F 0).map φ * B.map φ := by
      rw [Matrix.map_mul, Matrix.map_mul]
      rfl
    change ((B.map φ).transpose * (hessian F 0).map φ * B.map φ).det ≠ 0
    rw [← hmap]
    change (φ.mapMatrix (B.transpose * hessian F 0 * B)).det ≠ 0
    rw [← RingHom.map_det]
    exact hB

/-- The full integral rank-two lifting bound. Its hypotheses concern only
the actual polynomial, its reduction, and the rank of its actual Hessian.
All coordinate choices and all binary slice estimates are proved internally. -/
theorem card_zeros_le_succ_mul_pow {n : ℕ}
    (F : MvPolynomial (Fin n) ℤ) (p : ℕ) [Fact p.Prime] (hp : p ≠ 2)
    (hF : F.totalDegree ≤ 3)
    (hred : (map (Int.castRingHom (ZMod p)) F).totalDegree ≤ 2)
    (hrank : 2 ≤ (hessian (map (Int.castRingHom (ZMod p)) F)
      (0 : Fin n → ZMod p)).rank) (s : ℕ) :
    (Finset.univ.filter fun z : Fin n → ZMod (p^s) =>
      eval₂ (Int.castRingHom (ZMod (p^s))) z F = 0).card ≤
        (s+1)*p^(s*(n-1)) := by
  classical
  have hrank' : 2 ≤ ((hessian F 0).map (Int.castRingHom (ZMod p))).rank := by
    rwa [← hessian_map_origin]
  obtain ⟨A,e,hA,hblock⟩ := QuadraticRankTwoCoordinates.integral_coordinates
    p hp (hessian F 0) (hessian_symmetric F 0) hrank'
  have hn : 2 ≤ n := by
    simpa only [Fintype.card_fin] using Fintype.card_le_of_injective e e.injective
  let B : Matrix (Fin n) (Fin 2) ℤ := fun i j => A i (e j)
  have hB : ((B.transpose * hessian F 0 * B).det : ZMod p) ≠ 0 := hblock
  apply BinarySliceCounting.residue_count_le_after_matrix hn p s A hA e
    (fun z => eval₂ (Int.castRingHom (ZMod (p^s))) z F = 0)
  intro w
  let wInt : BinarySliceCounting.Complement e → ℤ := fun i => (w i).val
  let b : Fin n → ℤ := A.mulVec (BinarySliceCounting.combine e 0 wInt)
  have hw (i : Fin n) :
      ((BinarySliceCounting.combine e (0 : Fin 2 → ℤ) wInt i : ℤ) : ZMod (p^s)) =
        BinarySliceCounting.combine e 0 w i := by
    by_cases hi : i ∈ Set.range e
    · obtain ⟨j,rfl⟩ := hi
      simp only [BinarySliceCounting.combine_selected, Pi.zero_apply, Int.cast_zero]
    · simp only [BinarySliceCounting.combine_complement e _ _ i hi,
        wInt, Int.cast_natCast, ZMod.natCast_zmod_val]
  have hb : (fun i => (b i : ZMod (p^s))) =
      (A.map (Int.castRingHom (ZMod (p^s)))).mulVec
        (BinarySliceCounting.combine e 0 w) := by
    ext i
    simp only [b, Matrix.mulVec, dotProduct, Int.cast_sum, Int.cast_mul,
      Matrix.map_apply, Int.coe_castRingHom, hw]
  have hpoint (z : Fin 2 → ZMod (p^s)) :
      eval₂ (Int.castRingHom (ZMod (p^s))) z (affineSlice F B b) =
        eval₂ (Int.castRingHom (ZMod (p^s)))
          ((A.map (Int.castRingHom (ZMod (p^s)))).mulVec
            (BinarySliceCounting.combine e z w)) F := by
    rw [eval₂_affineSlice, BinarySliceCounting.mulVec_combine]
    congr 1
    change (fun i => (b i : ZMod (p^s))) + _ = _
    rw [hb]
    rfl
  simpa only [hpoint] using card_affine_binary_slice_zeros_le F p hF hred B hB b s

/-- The numerical exponent used by the manuscript's ten-variable proof. -/
theorem card_ten_variable_zeros_le
    (F : MvPolynomial (Fin 10) ℤ) (p : ℕ) [Fact p.Prime] (hp : p ≠ 2)
    (hF : F.totalDegree ≤ 3)
    (hred : (map (Int.castRingHom (ZMod p)) F).totalDegree ≤ 2)
    (hrank : 2 ≤ (hessian (map (Int.castRingHom (ZMod p)) F)
      (0 : Fin 10 → ZMod p)).rank) (s : ℕ) :
    (Finset.univ.filter fun z : Fin 10 → ZMod (p^s) =>
      eval₂ (Int.castRingHom (ZMod (p^s))) z F = 0).card ≤ (s+1)*p^(9*s) := by
  simpa only [Nat.reduceSub, Nat.mul_comm s 9] using
    card_zeros_le_succ_mul_pow F p hp hF hred hrank s

end CubicTenVariables.RankTwoPolynomialLifting
