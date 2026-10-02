import HessianTheorem11.PolynomialRestriction
import Mathlib.Algebra.MvPolynomial.Funext

/-! Elementary binary coefficient comparison and cancellation over an
infinite characteristic-zero field. -/
noncomputable section
namespace HessianTheorem11.BinaryPolynomialCancellation
open MvPolynomial
variable {K : Type*} [Field K] [CharZero K]

theorem cubic_zero_coefficients (a b c d e f : K)
    (h : ∀ x y : K, a*x^3 + (2*b+d)*x^2*y + (c+2*e)*x*y^2 + f*y^3 = 0) :
    a = 0 ∧ f = 0 ∧ d = -2*b ∧ c = -2*e := by
  have ha := h 1 0
  have hf := h 0 1
  have hp := h 1 1
  have hm := h 1 (-1)
  refine ⟨by simpa using ha, by simpa using hf, ?_, ?_⟩
  · linear_combination (hp-hm)/2 - hf
  · linear_combination (hp+hm)/2 - ha

theorem quadratic_zero_coefficients (a b c : K)
    (h : ∀ x y : K, a*x^2 + b*x*y + c*y^2 = 0) : a=0 ∧ b=0 ∧ c=0 := by
  have ha := h 1 0
  have hc := h 0 1
  have hb := h 1 1
  exact ⟨by simpa using ha, by linear_combination hb-ha-hc, by simpa using hc⟩

def binaryLinear (a b : K) : MvPolynomial (Fin 2) K := C a * X 0 + C b * X 1

theorem binaryLinear_eval (a b : K) (u : Fin 2 → K) :
    eval u (binaryLinear a b) = a*u 0+b*u 1 := by simp [binaryLinear]

theorem binaryLinear_ne_zero (a b : K) (h : a ≠ 0 ∨ b ≠ 0) : binaryLinear a b ≠ 0 := by
  intro hz
  rcases h with ha | hb
  · have he := congrArg (eval ![1,0]) hz
    simp [binaryLinear] at he
    exact ha he
  · have he := congrArg (eval ![0,1]) hz
    simp [binaryLinear] at he
    exact hb he

theorem cancel_binary_linear (a b : K) (h : a≠0 ∨ b≠0)
    (P : MvPolynomial (Fin 2) K) (k : ℕ)
    (hz : ∀ u : Fin 2 → K, (a*u 0+b*u 1)^k * eval u P = 0) : P=0 := by
  have hh : (binaryLinear a b)^k * P = 0 := by
    apply MvPolynomial.funext
    intro u
    simpa [binaryLinear_eval] using hz u
  exact (mul_eq_zero.mp hh).resolve_left (pow_ne_zero k (binaryLinear_ne_zero a b h))

theorem cancel_linear_quadratic (a b c d e : K) (h : a≠0 ∨ b≠0) (k : ℕ)
    (hz : ∀ x y : K, (a*x+b*y)^k * (c*x^2+d*x*y+e*y^2) = 0) :
    c=0 ∧ d=0 ∧ e=0 := by
  let P : MvPolynomial (Fin 2) K := C c*X 0^2+C d*X 0*X 1+C e*X 1^2
  have hp : P=0 := cancel_binary_linear a b h P k (by intro u; simpa [P] using hz (u 0) (u 1))
  apply quadratic_zero_coefficients
  intro x y
  have he := congrArg (eval ![x,y]) hp
  simpa [P] using he

end HessianTheorem11.BinaryPolynomialCancellation
