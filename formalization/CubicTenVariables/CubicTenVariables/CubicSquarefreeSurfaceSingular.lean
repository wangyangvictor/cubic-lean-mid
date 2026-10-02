import CubicTenVariables.CubicTaylorExpansion

/-! Actual singular equations of the four-variable squarefree cubic.
With all four coefficients nonzero, singular zeros are exactly coordinate
axes in every characteristic. Excluding characteristic three is necessary
only when the cubic equation is omitted and recovered from the partials. -/
set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.CubicSquarefreeSurfaceSingular
open MvPolynomial HessianTheorem11

variable {R : Type*} [CommRing R]

def polynomial (c : Fin 4 → R) : MvPolynomial (Fin 4) R :=
  C (c 0) * X 1 * X 2 * X 3 + C (c 1) * X 0 * X 2 * X 3 +
    C (c 2) * X 0 * X 1 * X 3 + C (c 3) * X 0 * X 1 * X 2

@[simp] theorem eval_polynomial (c x : Fin 4 → R) :
    eval x (polynomial c) = c 0 * x 1 * x 2 * x 3 + c 1 * x 0 * x 2 * x 3 +
      c 2 * x 0 * x 1 * x 3 + c 3 * x 0 * x 1 * x 2 := by
  simp [polynomial]

theorem polynomial_isHomogeneous (c : Fin 4 → R) : (polynomial c).IsHomogeneous 3 := by
  have ht (a : R) (i j k : Fin 4) : (C a * X i * X j * X k).IsHomogeneous 3 :=
    ((isHomogeneous_C_mul_X a i).mul (isHomogeneous_X R j)).mul (isHomogeneous_X R k)
  exact ((ht _ _ _ _).add (ht _ _ _ _)).add (ht _ _ _ _) |>.add (ht _ _ _ _)

/-- These are the actual formal partial derivatives, evaluated at x. -/
theorem gradient_polynomial (c x : Fin 4 → R) :
    gradient (polynomial c) x =
      ![c 1 * x 2 * x 3 + c 2 * x 1 * x 3 + c 3 * x 1 * x 2,
        c 0 * x 2 * x 3 + c 2 * x 0 * x 3 + c 3 * x 0 * x 2,
        c 0 * x 1 * x 3 + c 1 * x 0 * x 3 + c 3 * x 0 * x 1,
        c 0 * x 1 * x 2 + c 1 * x 0 * x 2 + c 2 * x 0 * x 1] := by
  ext i
  fin_cases i <;> simp [gradient, polynomial, Derivation.leibniz] <;> ring

/-- Every coordinate axis consists of actual singular zeros. -/
theorem coordinate_axis_singular (c : Fin 4 → R) (i : Fin 4) (t : R) :
    eval (Pi.single i t) (polynomial c) = 0 ∧
      gradient (polynomial c) (Pi.single i t) = 0 := by
  rw [gradient_polynomial]
  fin_cases i <;> simp

variable {K : Type*} [Field K]

/-- No classification is used: the equation and its four partials force
at most one coordinate to be nonzero. -/
theorem exists_coordinate_axis_of_singular
    (c : Fin 4 → K) (hc : ∀ i, c i ≠ 0) (x : Fin 4 → K)
    (hf : eval x (polynomial c) = 0) (hg : gradient (polynomial c) x = 0) :
    ∃ i : Fin 4, x = Pi.single i (x i) := by
  rw [eval_polynomial] at hf
  rw [gradient_polynomial] at hg
  have hg0 := congrFun hg 0
  have hg1 := congrFun hg 1
  have hg2 := congrFun hg 2
  have hg3 := congrFun hg 3
  simp at hg0 hg1 hg2 hg3
  have ht : c 0 * x 1 * x 2 * x 3 = 0 := by
    linear_combination hf - x 0 * hg0
  have hc0 := hc 0
  have hc1 := hc 1
  have hc2 := hc 2
  have hc3 := hc 3
  by_cases h0 : x 0 = 0 <;> by_cases h1 : x 1 = 0 <;>
    by_cases h2 : x 2 = 0 <;> by_cases h3 : x 3 = 0 <;>
    simp_all [mul_eq_zero]
  all_goals first
    | (refine ⟨0, ?_⟩; ext i; fin_cases i <;> simp_all; done)
    | (refine ⟨1, ?_⟩; ext i; fin_cases i <;> simp_all; done)
    | (refine ⟨2, ?_⟩; ext i; fin_cases i <;> simp_all; done)
    | (refine ⟨3, ?_⟩; ext i; fin_cases i <;> simp_all)

theorem singular_iff_coordinate_axis
    (c : Fin 4 → K) (hc : ∀ i, c i ≠ 0) (x : Fin 4 → K) :
    (eval x (polynomial c) = 0 ∧ gradient (polynomial c) x = 0) ↔
      ∃ i : Fin 4, ∃ t : K, x = Pi.single i t := by
  constructor
  · rintro ⟨hf,hg⟩
    obtain ⟨i,hi⟩ := exists_coordinate_axis_of_singular c hc x hf hg
    exact ⟨i,x i,hi⟩
  · rintro ⟨i,t,rfl⟩
    exact coordinate_axis_singular c i t

/-- The nonzero geometric singular points are exactly the four coordinate
points; no restriction on the characteristic is needed when F(x)=0 is given. -/
theorem exists_axis_of_nonzero_singular
    (c : Fin 4 → K) (hc : ∀ i, c i ≠ 0) (x : Fin 4 → K) (hx : x ≠ 0)
    (hf : eval x (polynomial c) = 0) (hg : gradient (polynomial c) x = 0) :
    ∃ i : Fin 4, ∃ t : K, t ≠ 0 ∧ x = Pi.single i t := by
  obtain ⟨i,hi⟩ := exists_coordinate_axis_of_singular c hc x hf hg
  refine ⟨i,x i,?_,hi⟩
  intro hz
  apply hx
  exact hi.trans (by rw [hz]; simp)

/-- Away from characteristic three, the four partial equations alone
imply the cubic equation, by the literal Euler identity. -/
theorem eval_eq_zero_of_gradient_eq_zero
    (h3 : (3 : K) ≠ 0) (c x : Fin 4 → K) (hg : gradient (polynomial c) x = 0) :
    eval x (polynomial c) = 0 := by
  rw [gradient_polynomial] at hg
  have hg0 := congrFun hg 0
  have hg1 := congrFun hg 1
  have hg2 := congrFun hg 2
  have hg3 := congrFun hg 3
  simp at hg0 hg1 hg2 hg3
  have he : 3 * eval x (polynomial c) = 0 := by
    rw [eval_polynomial]
    linear_combination x 0 * hg0 + x 1 * hg1 + x 2 * hg2 + x 3 * hg3
  exact (mul_eq_zero.mp he).resolve_left h3

theorem gradient_eq_zero_iff_coordinate_axis
    (h3 : (3 : K) ≠ 0) (c : Fin 4 → K) (hc : ∀ i, c i ≠ 0) (x : Fin 4 → K) :
    gradient (polynomial c) x = 0 ↔ ∃ i : Fin 4, ∃ t : K, x = Pi.single i t := by
  constructor
  · intro hg
    exact (singular_iff_coordinate_axis c hc x).mp
      ⟨eval_eq_zero_of_gradient_eq_zero h3 c x hg,hg⟩
  · rintro ⟨i,t,rfl⟩
    exact (coordinate_axis_singular c i t).2

end CubicTenVariables.CubicSquarefreeSurfaceSingular
