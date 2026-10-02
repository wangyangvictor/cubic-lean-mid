import HessianTheorem11.HessianLinearity

/-! The polynomial identity behind incidence concentration (source 5.5).
This is the actual incidence equation, not an assumed dimension formula. -/

noncomputable section
namespace HessianTheorem11
open MvPolynomial

variable {K : Type*} [Field K] [CharZero K] {n : ℕ}

theorem gradient_difference {F : MvPolynomial (Fin n) K}
    (hF : F.IsHomogeneous 3) (x y : Fin n → K) :
    gradient F (x + y) - gradient F (x - y) = 2 • (hessian F x).mulVec y := by
  ext i
  have hp := congrFun (hessian_mulVec_self hF (x + y)) i
  have hm := congrFun (hessian_mulVec_self hF (x - y)) i
  have hs := congrFun (hessian_polarization hF x y) i
  simp only [hessian_add hF, hessian_sub hF, Matrix.add_mulVec, Matrix.sub_mulVec,
    Matrix.mulVec_add, Matrix.mulVec_sub, Pi.add_apply, Pi.sub_apply, Pi.smul_apply,
    nsmul_eq_mul] at hp hm hs ⊢
  linear_combination (-1 / 2 : K) * hp + (1 / 2 : K) * hm - hs

theorem incidence_iff_equal_gradients {F : MvPolynomial (Fin n) K}
    (hF : F.IsHomogeneous 3) (x y : Fin n → K) :
    (hessian F x).mulVec y = 0 ↔ gradient F (x + y) = gradient F (x - y) := by
  conv_rhs => rw [← sub_eq_zero, gradient_difference hF]
  constructor
  · intro h; rw [h, smul_zero]
  · intro h
    ext i
    have hi := congrFun h i
    simp only [Pi.smul_apply, Pi.zero_apply, nsmul_eq_mul] at hi
    exact (mul_eq_zero.mp hi).resolve_left (by norm_num)

/-- The linear change from the two incidence variables to two points with
equal gradients is invertible in characteristic zero. -/
def incidenceCoordinateChange : ((Fin n → K) × (Fin n → K)) ≃ₗ[K]
    ((Fin n → K) × (Fin n → K)) where
  toFun p := (p.1 + p.2, p.1 - p.2)
  invFun p := ((2 : K)⁻¹ • (p.1 + p.2), (2 : K)⁻¹ • (p.1 - p.2))
  left_inv p := by
    ext i <;> simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] <;> field_simp <;> ring
  right_inv p := by
    ext i <;> simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] <;> field_simp <;> ring
  map_add' p q := by ext i <;> simp <;> ring
  map_smul' a p := by ext i <;> simp [mul_sub]

end HessianTheorem11
