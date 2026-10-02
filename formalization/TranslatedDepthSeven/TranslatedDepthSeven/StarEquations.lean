import TranslatedDepthSeven.TangentTaylor

/-!
# Explicit equations for a star of lines

For an integral polynomial `f` and a fixed integral vector `h`, this file
constructs a polynomial in the line parameter whose coefficients are literal
integral multivariable polynomials in a second vector `z`.  Their simultaneous
vanishing is proved equivalent to the identity
`f(h + t z) = 0` for every integral `t`.

This is the algebraic part of the manuscript's sentence that the equations of
`Star_Z(h)` are obtained by equating coefficients after restriction to the
line through `h` and `z`.  No geometric assertion or height estimate is
assumed here.
-/

namespace TranslatedDepthSeven

noncomputable section

open MvPolynomial Polynomial

variable {σ : Type*}

/-- Restrict `f` to `h + T z`, retaining the coordinates of `z` as
indeterminates in the coefficient ring. -/
def symbolicLinePolynomial (f : MvPolynomial σ ℤ) (h : σ → ℤ) :
    Polynomial (MvPolynomial σ ℤ) :=
  MvPolynomial.eval₂Hom
    (Polynomial.C.comp MvPolynomial.C)
    (fun i ↦ Polynomial.C (MvPolynomial.C (h i)) +
      Polynomial.X * Polynomial.C (MvPolynomial.X i)) f

@[simp]
theorem symbolicLinePolynomial_C (a : ℤ) (h : σ → ℤ) :
    symbolicLinePolynomial (MvPolynomial.C a) h =
      Polynomial.C (MvPolynomial.C a) := by
  simp [symbolicLinePolynomial]

@[simp]
theorem symbolicLinePolynomial_X (i : σ) (h : σ → ℤ) :
    symbolicLinePolynomial (MvPolynomial.X i) h =
      Polynomial.C (MvPolynomial.C (h i)) +
        Polynomial.X * Polynomial.C (MvPolynomial.X i) := by
  simp [symbolicLinePolynomial]

@[simp]
theorem symbolicLinePolynomial_add
    (f g : MvPolynomial σ ℤ) (h : σ → ℤ) :
    symbolicLinePolynomial (f + g) h =
      symbolicLinePolynomial f h + symbolicLinePolynomial g h := by
  simp [symbolicLinePolynomial]

@[simp]
theorem symbolicLinePolynomial_mul
    (f g : MvPolynomial σ ℤ) (h : σ → ℤ) :
    symbolicLinePolynomial (f * g) h =
      symbolicLinePolynomial f h * symbolicLinePolynomial g h := by
  simp [symbolicLinePolynomial]

/-- The explicit coefficient equation of order `k` obtained from the line
restriction. -/
def starCoefficient (f : MvPolynomial σ ℤ) (h : σ → ℤ) (k : ℕ) :
    MvPolynomial σ ℤ :=
  (symbolicLinePolynomial f h).coeff k

/-- Substituting an integral vector `z` into the symbolic coefficients gives
the ordinary line-restriction polynomial from `TangentTaylor`. -/
theorem symbolicLinePolynomial_map_eval
    (f : MvPolynomial σ ℤ) (h z : σ → ℤ) :
    (symbolicLinePolynomial f h).map (MvPolynomial.eval z) =
      linePolynomial f h z := by
  induction f using MvPolynomial.induction_on with
  | C a => simp [symbolicLinePolynomial, linePolynomial]
  | add f g hf hg =>
      rw [symbolicLinePolynomial_add, Polynomial.map_add,
        linePolynomial_add, hf, hg]
  | mul_X f i hf =>
      rw [symbolicLinePolynomial_mul, Polynomial.map_mul,
        linePolynomial_mul]
      have hx :
          (symbolicLinePolynomial (MvPolynomial.X i) h).map
              (MvPolynomial.eval z) =
            linePolynomial (MvPolynomial.X i) h z := by
        rw [symbolicLinePolynomial_X, linePolynomial_X]
        rw [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C,
          Polynomial.map_X, Polynomial.map_C, MvPolynomial.eval_C,
          MvPolynomial.eval_X]
      exact congrArg₂ (· * ·) hf hx

/-- Evaluation of each displayed star equation is exactly the corresponding
coefficient of the ordinary line restriction. -/
theorem eval_starCoefficient
    (f : MvPolynomial σ ℤ) (h z : σ → ℤ) (k : ℕ) :
    MvPolynomial.eval z (starCoefficient f h k) =
      (linePolynomial f h z).coeff k := by
  have hmap := congrArg (fun g : Polynomial ℤ ↦ g.coeff k)
    (symbolicLinePolynomial_map_eval f h z)
  simpa [starCoefficient] using hmap

/-- It suffices to impose the finitely many coefficient equations indexed by
the support of the symbolic restriction. -/
theorem linePolynomial_eq_zero_iff_starCoefficients
    (f : MvPolynomial σ ℤ) (h z : σ → ℤ) :
    linePolynomial f h z = 0 ↔
      ∀ k ∈ (symbolicLinePolynomial f h).support,
        MvPolynomial.eval z (starCoefficient f h k) = 0 := by
  constructor
  · intro hzero k _hk
    rw [eval_starCoefficient, hzero]
    simp
  · intro hcoeff
    apply Polynomial.ext
    intro k
    rw [← eval_starCoefficient]
    by_cases hk : k ∈ (symbolicLinePolynomial f h).support
    · simpa using hcoeff k hk
    · have hsymbolic : (symbolicLinePolynomial f h).coeff k = 0 := by
        simpa [Polynomial.mem_support_iff] using hk
      simp [starCoefficient, hsymbolic]

/-- Vanishing of the finitely many explicit coefficient equations is
equivalent to vanishing of `f` at every integral point on the affine line
`h + ℤ z`. -/
theorem starCoefficients_iff_eval_line_zero
    (f : MvPolynomial σ ℤ) (h z : σ → ℤ) :
    (∀ k ∈ (symbolicLinePolynomial f h).support,
        MvPolynomial.eval z (starCoefficient f h k) = 0) ↔
      ∀ t : ℤ, MvPolynomial.eval (fun i ↦ h i + t * z i) f = 0 := by
  rw [← linePolynomial_eq_zero_iff_starCoefficients]
  constructor
  · intro hzero t
    rw [← linePolynomial_eval, hzero]
    simp
  · intro heval
    exact Polynomial.zero_of_eval_zero _ fun t ↦ by
      rw [linePolynomial_eval]
      exact heval t

end

end TranslatedDepthSeven
