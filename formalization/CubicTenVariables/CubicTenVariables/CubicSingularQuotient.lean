import CubicTenVariables.CubicTaylorExpansion
import CubicTenVariables.QuadraticHessianConstant

/-!
# The actual integral quotient at a singular cubic residue class

For an integral homogeneous cubic, the quotient after translating by `p*y`
and dividing by `p^2` is an actual integral polynomial whenever the constant
and first derivative values have the required divisibilities. Its quadratic
term is written without division by two. Its reduced Hessian is exactly the
original cubic Hessian at the translation center.
-/

noncomputable section
namespace CubicTenVariables.CubicSingularQuotient
open MvPolynomial HessianTheorem11
open scoped BigOperators

/-- The division-free quadratic term in the cubic Taylor expansion. -/
def quadraticPolynomial {R : Type*} [CommRing R] {n : ℕ}
    (F : MvPolynomial (Fin n) R) (k : Fin n → R) : MvPolynomial (Fin n) R :=
  ∑ i, C (k i) * pderiv i F

@[simp] theorem eval_quadraticPolynomial {R : Type*} [CommRing R] {n : ℕ}
    (F : MvPolynomial (Fin n) R) (k y : Fin n → R) :
    eval y (quadraticPolynomial F k) = CubicTaylorExpansion.quadraticAt F k y := by
  simp only [quadraticPolynomial, map_sum, map_mul, eval_C,
    CubicTaylorExpansion.quadraticAt, CubicTaylorExpansion.directional,
    dotProduct, gradient]

theorem homogeneous_quadraticPolynomial {R : Type*} [CommRing R] {n : ℕ}
    (F : MvPolynomial (Fin n) R) (hF : F.IsHomogeneous 3) (k : Fin n → R) :
    (quadraticPolynomial F k).IsHomogeneous 2 := by
  apply IsHomogeneous.sum
  intro i hi
  exact hF.pderiv.C_mul _

/-- All divisions occur in the integer coefficients, not in a residue ring. -/
def quotientPolynomial {n : ℕ} (F : MvPolynomial (Fin n) ℤ)
    (k : Fin n → ℤ) (p : ℤ) : MvPolynomial (Fin n) ℤ :=
  C (eval k F / p^2) +
    (∑ i, C (eval k (pderiv i F) / p) * X i) +
    quadraticPolynomial F k + C p * F

/-- Exact integer evaluation of the translated cubic as `p^2` times the
constructed quotient. Divisibility hypotheses concern literal evaluations. -/
theorem eval_translate_eq_sq_mul_quotient {n : ℕ}
    (F : MvPolynomial (Fin n) ℤ) (hF : F.IsHomogeneous 3)
    (k : Fin n → ℤ) (p : ℤ)
    (h0 : p^2 ∣ eval k F) (hg : ∀ i, p ∣ eval k (pderiv i F))
    (y : Fin n → ℤ) :
    eval (k + p • y) F = p^2 * eval y (quotientPolynomial F k p) := by
  have hc : p^2 * (eval k F / p^2) = eval k F := Int.mul_ediv_cancel' h0
  have hl : p * (∑ i, (eval k (pderiv i F) / p) * y i) =
      CubicTaylorExpansion.directional F k y := by
    rw [Finset.mul_sum]
    unfold CubicTaylorExpansion.directional gradient dotProduct
    apply Finset.sum_congr rfl
    intro i hi
    rw [← mul_assoc, Int.mul_ediv_cancel' (hg i), mul_comm]
  rw [CubicTaylorExpansion.eval_cubic_add_smul F hF]
  simp only [quotientPolynomial, map_add, map_sum, map_mul, eval_C, eval_X,
    eval_quadraticPolynomial]
  linear_combination -hc - p*hl

/-- The exact rescaling identity in any target commutative ring, including
every prime-power residue ring. Integer divisibility is checked before mapping. -/
theorem eval₂_translate_eq_sq_mul_quotient {n : ℕ} {S : Type*} [CommRing S]
    (F : MvPolynomial (Fin n) ℤ) (hF : F.IsHomogeneous 3)
    (k : Fin n → ℤ) (p : ℤ)
    (h0 : p^2 ∣ eval k F) (hg : ∀ i, p ∣ eval k (pderiv i F))
    (f : ℤ →+* S) (y : Fin n → S) :
    eval₂ f ((f ∘ k) + f p • y) F =
      (f p)^2 * eval₂ f y (quotientPolynomial F k p) := by
  have hc : (f p)^2 * f (eval k F / p^2) = f (eval k F) := by
    rw [← map_pow, ← map_mul, Int.mul_ediv_cancel' h0]
  have hl : f p * (∑ i, f (eval k (pderiv i F) / p) * y i) =
      ∑ i, y i * f (eval k (pderiv i F)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [← mul_assoc, ← map_mul, Int.mul_ediv_cancel' (hg i), mul_comm]
  rw [CubicTaylorExpansion.eval₂_cubic_add_smul F hF]
  simp only [← eval₂_comp, quotientPolynomial, eval₂_add, eval₂_sum,
    eval₂_mul, eval₂_C, eval₂_X, quadraticPolynomial, dotProduct, Function.comp_apply]
  linear_combination -hc - f p*hl

theorem totalDegree_quotient_le_three {n : ℕ}
    (F : MvPolynomial (Fin n) ℤ) (hF : F.IsHomogeneous 3)
    (k : Fin n → ℤ) (p : ℤ) : (quotientPolynomial F k p).totalDegree ≤ 3 := by
  have hlin : (∑ i : Fin n, C (eval k (pderiv i F) / p) * X i).IsHomogeneous 1 := by
    apply IsHomogeneous.sum
    intro i hi
    exact isHomogeneous_C_mul_X _ _
  unfold quotientPolynomial
  apply (totalDegree_add _ _).trans
  apply max_le
  · apply (totalDegree_add _ _).trans
    apply max_le
    · apply (totalDegree_add _ _).trans
      exact max_le (by simp only [totalDegree_C]; omega)
        (hlin.totalDegree_le.trans (by omega))
    · exact (homogeneous_quadraticPolynomial F hF k).totalDegree_le.trans (by omega)
  · exact (hF.C_mul p).totalDegree_le

/-- Modulo the chosen modulus the cubic term vanishes. This statement is
valid for every natural modulus, including zero, without primality. -/
theorem totalDegree_reduction_quotient_le_two {n : ℕ}
    (F : MvPolynomial (Fin n) ℤ) (hF : F.IsHomogeneous 3)
    (k : Fin n → ℤ) (p : ℕ) :
    (map (Int.castRingHom (ZMod p)) (quotientPolynomial F k (p : ℤ))).totalDegree ≤ 2 := by
  let φ := Int.castRingHom (ZMod p)
  have hlin : (∑ i : Fin n, C (eval k (pderiv i F) / (p : ℤ)) * X i).IsHomogeneous 1 := by
    apply IsHomogeneous.sum
    intro i hi
    exact isHomogeneous_C_mul_X _ _
  have hq := (homogeneous_quadraticPolynomial F hF k).map φ
  have hl := hlin.map φ
  change (map φ (quotientPolynomial F k (p : ℤ))).totalDegree ≤ 2
  simp only [quotientPolynomial, map_add, map_mul, map_C,
    show φ (p : ℤ) = 0 by simp [φ], C_0, zero_mul, add_zero]
  apply (totalDegree_add _ _).trans
  apply max_le
  · apply (totalDegree_add _ _).trans
    exact max_le (by simp only [totalDegree_C]; omega)
      (hl.totalDegree_le.trans (by omega))
  · exact hq.totalDegree_le

/-- The quadratic Taylor polynomial has precisely the original cubic
Hessian at its center, over arbitrary commutative rings. -/
theorem hessian_quadraticPolynomial {R : Type*} [CommRing R] {n : ℕ}
    (F : MvPolynomial (Fin n) R) (hF : F.IsHomogeneous 3)
    (k y : Fin n → R) :
    hessian (quadraticPolynomial F k) y = hessian F k := by
  ext i j
  change eval y (pderiv j (pderiv i (quadraticPolynomial F k))) = hessian F k i j
  simp only [quadraticPolynomial, map_sum, pderiv_C_mul, map_mul, eval_C]
  rw [hessian_entry_expansion hF]
  apply Finset.sum_congr rfl
  intro l hl
  congr 1
  rw [partials_commute F i l, partials_commute (pderiv i F) j l]
  have hh : (pderiv l (pderiv j (pderiv i F))).IsHomogeneous 0 := hF.pderiv.pderiv.pderiv
  rw [homogeneous_zero_eq_constant hh, eval_C, coeff_zero_C]

/-- Constant and linear quotient coefficients make no contribution to the
Hessian; the cubic term vanishes at the origin. No divisibility is needed. -/
theorem hessian_quotient_origin {n : ℕ}
    (F : MvPolynomial (Fin n) ℤ) (hF : F.IsHomogeneous 3)
    (k : Fin n → ℤ) (p : ℤ) :
    hessian (quotientPolynomial F k p) (0 : Fin n → ℤ) = hessian F k := by
  have hlin (i j : Fin n) :
      pderiv j (pderiv i (∑ l : Fin n, C (eval k (pderiv l F) / p) * X l)) = 0 := by
    simp [Pi.single_apply, apply_ite]
  have hz (i j : Fin n) : eval (0 : Fin n → ℤ) (pderiv j (pderiv i F)) = 0 :=
    congrArg (fun M : Matrix (Fin n) (Fin n) ℤ => M i j) (hessian_zero hF)
  ext i j
  change eval (0 : Fin n → ℤ) (pderiv j (pderiv i (quotientPolynomial F k p))) = _
  simp only [quotientPolynomial, map_add, pderiv_C, zero_add,
    hlin, pderiv_C_mul, eval_mul, eval_C, hz, mul_zero, add_zero]
  exact congrArg (fun M : Matrix (Fin n) (Fin n) ℤ => M i j)
    (hessian_quadraticPolynomial F hF k 0)

/-- After reduction, the quotient's actual Hessian at zero is exactly the
original cubic's actual Hessian at the reduced center. Valid for every p. -/
theorem hessian_reduction_quotient_origin {n : ℕ}
    (F : MvPolynomial (Fin n) ℤ) (hF : F.IsHomogeneous 3)
    (k : Fin n → ℤ) (p : ℕ) :
    hessian (map (Int.castRingHom (ZMod p)) (quotientPolynomial F k (p : ℤ)))
      (0 : Fin n → ZMod p) =
    hessian (map (Int.castRingHom (ZMod p)) F) (fun i => (k i : ZMod p)) := by
  rw [QuadraticHessianConstant.hessian_map_origin, hessian_quotient_origin F hF]
  ext i j
  simp only [hessian, hessianPolynomial, Matrix.map_apply, pderiv_map]
  exact map_eval (Int.castRingHom (ZMod p)) k (pderiv j (pderiv i F))

end CubicTenVariables.CubicSingularQuotient
