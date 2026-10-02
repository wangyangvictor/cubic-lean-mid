import CubicTenVariables.CubicTaylorExpansion
import CubicTenVariables.QuadraticGaussBound

/-!
# The actual cubic Hessian controls the quadratic Gauss sum

For a homogeneous cubic over ZMod d, the integral quadratic term at y is
Q_y(z)=Σ_i y_i (∂_i F)(z). The proved division-free polarization identity
identifies its polar matrix with the actual Hessian H_F(y). Applying finite
orthogonality therefore bounds the squared norm by d^n times the literal
Hessian-kernel cardinality. A unit multiplier and arbitrary linear phase
are allowed. These statements include even moduli and require no Smith
normal form, smoothness, or analytic estimate as input.
-/

noncomputable section
namespace CubicTenVariables.CubicQuadraticGauss

open MvPolynomial HessianTheorem11 CubicTaylorExpansion QuadraticGaussBound
open scoped BigOperators

variable (d n : ℕ) [NeZero d]

/-- The quadratic term of the actual cubic has the Hessian-kernel bound. -/
theorem norm_quadraticAt_sum_sq_le (F : MvPolynomial (Fin n) (ZMod d))
    (hF : F.IsHomogeneous 3) (y : Fin n → ZMod d) :
    ‖∑ z : Fin n → ZMod d, ZMod.stdAddChar (quadraticAt F y z)‖ ^ 2 ≤
      (d : ℝ) ^ n * Nat.card {h : Fin n → ZMod d // (hessian F y).mulVec h = 0} :=
  norm_sum_sq_le_card_kernel d n (quadraticAt F y) (hessian F y)
    (quadraticAt_add F hF y)

/-- The form directly used after cubic Taylor expansion: a unit times
Q_y plus an arbitrary linear phase, with the unchanged Hessian kernel. -/
theorem norm_mixed_quadraticAt_sum_sq_le (F : MvPolynomial (Fin n) (ZMod d))
    (hF : F.IsHomogeneous 3) (y : Fin n → ZMod d)
    (u : (ZMod d)ˣ) (v : Fin n → ZMod d) :
    ‖∑ z : Fin n → ZMod d,
      ZMod.stdAddChar ((u : ZMod d) * quadraticAt F y z + dotProduct v z)‖ ^ 2 ≤
      (d : ℝ) ^ n * Nat.card {h : Fin n → ZMod d // (hessian F y).mulVec h = 0} :=
  norm_mixed_sum_sq_le d n (quadraticAt F y) (hessian F y)
    (quadraticAt_add F hF y) u v

/-- The same bound displaying the actual formal partial derivatives in
the quadratic phase instead of an auxiliary phase name. -/
theorem norm_mixed_partial_sum_sq_le (F : MvPolynomial (Fin n) (ZMod d))
    (hF : F.IsHomogeneous 3) (y : Fin n → ZMod d)
    (u : (ZMod d)ˣ) (v : Fin n → ZMod d) :
    ‖∑ z : Fin n → ZMod d,
      ZMod.stdAddChar ((u : ZMod d) * (∑ i, y i * eval z (pderiv i F)) +
        ∑ i, v i * z i)‖ ^ 2 ≤
      (d : ℝ) ^ n * Nat.card {h : Fin n → ZMod d // (hessian F y).mulVec h = 0} :=
  norm_mixed_quadraticAt_sum_sq_le d n F hF y u v

end CubicTenVariables.CubicQuadraticGauss
