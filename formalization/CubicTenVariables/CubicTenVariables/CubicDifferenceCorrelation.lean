import CubicTenVariables.CubicTaylorExpansion
import CubicTenVariables.QuadraticGaussBound

/-! The actual finite difference of a homogeneous cubic is a quadratic phase.
Its constant phase has norm one, and its polar matrix is the Hessian at the
shift. No division by two or three occurs, so the correlation estimate holds
over every nonzero modulus, including 1, 2 and 3. -/

set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.CubicDifferenceCorrelation
open MvPolynomial HessianTheorem11 CubicTaylorExpansion
open scoped BigOperators

/-- The exact polynomial difference, with its constant and linear terms. -/
theorem difference_phase {R : Type*} [CommRing R] {n : ℕ}
    (F : MvPolynomial (Fin n) R) (hF : F.IsHomogeneous 3)
    (a : R) (h x : Fin n → R) :
    a * (eval (x + h) F - eval x F) =
      a * eval h F + (a * quadraticAt F h x + dotProduct (a • gradient F h) x) := by
  have he := eval_cubic_add_smul F hF h x (1 : R)
  simp only [one_smul, one_pow, one_mul] at he
  rw [add_comm x h, he, smul_dotProduct]
  rw [dotProduct_comm (gradient F h) x]
  simp only [smul_eq_mul, directional]
  ring

/-- Factoring out the constant unit-modulus phase gives the literal mixed
quadratic Gauss sum, with no normalization or change of summation variables. -/
theorem sum_eq_phase_mul_mixed_sum {q n : ℕ} [NeZero q]
    (F : MvPolynomial (Fin n) (ZMod q)) (hF : F.IsHomogeneous 3)
    (a : ZMod q) (h : Fin n → ZMod q) :
    (∑ x : Fin n → ZMod q,
      ZMod.stdAddChar (a * (eval (x + h) F - eval x F))) =
      ZMod.stdAddChar (a * eval h F) *
        ∑ x : Fin n → ZMod q,
          ZMod.stdAddChar (a * quadraticAt F h x + dotProduct (a • gradient F h) x) := by
  simp_rw [difference_phase F hF, AddChar.map_add_eq_mul]
  rw [Finset.mul_sum]

/-- The squared norm of the actual cubic correlation is bounded by the
ambient cardinality times the literal kernel cardinality of the Hessian. -/
theorem norm_sum_sq_le {q n : ℕ} [NeZero q]
    (F : MvPolynomial (Fin n) (ZMod q)) (hF : F.IsHomogeneous 3)
    (a : (ZMod q)ˣ) (h : Fin n → ZMod q) :
    ‖∑ x : Fin n → ZMod q,
      ZMod.stdAddChar ((a : ZMod q) * (eval (x + h) F - eval x F))‖ ^ 2 ≤
      (q : ℝ) ^ n * Nat.card {z : Fin n → ZMod q // (hessian F h).mulVec z = 0} := by
  rw [sum_eq_phase_mul_mixed_sum F hF, norm_mul,
    QuadraticGaussBound.norm_stdAddChar, one_mul]
  exact QuadraticGaussBound.norm_mixed_sum_sq_le q n (quadraticAt F h) (hessian F h)
    (quadraticAt_add F hF h) a ((a : ZMod q) • gradient F h)

end CubicTenVariables.CubicDifferenceCorrelation
