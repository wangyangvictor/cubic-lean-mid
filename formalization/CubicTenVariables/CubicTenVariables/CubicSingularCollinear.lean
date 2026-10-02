import CubicTenVariables.PlaneCubicSingularGeometry

/-! Three distinct singular points on a projective line force the whole
line to be singular. All equations are literal vector evaluations and the
proof uses the division-free quadratic expansion of the gradient. -/
set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.CubicSingularCollinear
open MvPolynomial HessianTheorem11

variable {K : Type*} [Field K] {n : ℕ}

private theorem gradient_smul (F : MvPolynomial (Fin n) K) (hF : F.IsHomogeneous 3)
    (p : Fin n → K) (a : K) : gradient F (a • p) = a^2 • gradient F p := by
  ext i
  simpa only [HessianTheorem11.gradient, Pi.smul_apply, smul_eq_mul, eval₂_id] using
    CubicGradientScaling.eval₂_partial_smul F hF (RingHom.id K) i p a

/-- The actual quadratic gradient expansion, with no division by two. -/
theorem gradient_two_vector_expansion
    (F : MvPolynomial (Fin n) K) (hF : F.IsHomogeneous 3)
    (p q : Fin n → K) (a b : K) :
    gradient F (a • p + b • q) =
      a^2 • gradient F p + b^2 • gradient F q +
        (a*b) • (hessian F p).mulVec q := by
  rw [CubicTaylorExpansion.gradient_add F hF, gradient_smul F hF,
    gradient_smul F hF, hessian_smul hF, Matrix.smul_mulVec,
    Matrix.mulVec_smul, smul_smul]

/-- A third vanishing gradient away from the two endpoints kills the
cross term, hence the gradient on every vector of the line. -/
theorem gradient_span_eq_zero_of_third
    (F : MvPolynomial (Fin n) K) (hF : F.IsHomogeneous 3)
    (p q : Fin n → K) (hp : gradient F p = 0) (hq : gradient F q = 0)
    (a b : K) (ha : a ≠ 0) (hb : b ≠ 0)
    (hr : gradient F (a • p + b • q) = 0) (s t : K) :
    gradient F (s • p + t • q) = 0 := by
  rw [gradient_two_vector_expansion F hF, hp, hq, smul_zero,
    smul_zero, zero_add, zero_add] at hr
  have hcross : (hessian F p).mulVec q = 0 :=
    (smul_eq_zero.mp hr).resolve_left (mul_ne_zero ha hb)
  rw [gradient_two_vector_expansion F hF, hp, hq, hcross]
  simp

/-- Literal scalar form of the three-point statement, in every characteristic.
The cubic equation on the span is the already-proved secant theorem. -/
theorem singular_span_of_third
    (F : MvPolynomial (Fin n) K) (hF : F.IsHomogeneous 3)
    (p q : Fin n → K) (hp : eval p F = 0) (hgp : gradient F p = 0)
    (hq : eval q F = 0) (hgq : gradient F q = 0)
    (a b : K) (ha : a ≠ 0) (hb : b ≠ 0)
    (hthird : gradient F (a • p + b • q) = 0) (s t : K) :
    eval (s • p + t • q) F = 0 ∧ gradient F (s • p + t • q) = 0 :=
  ⟨PlaneCubicSingularGeometry.eval_singular_span F hF p q hp hgp hq hgq s t,
    gradient_span_eq_zero_of_third F hF p q hgp hgq a b ha hb hthird s t⟩

/-- Exact geometric adapter: r is in the line spanned by p and q but is
in neither endpoint's one-dimensional span. No projective API is assumed. -/
theorem singular_span_of_nonproportional_third
    (F : MvPolynomial (Fin n) K) (hF : F.IsHomogeneous 3)
    (p q r : Fin n → K) (hp : eval p F = 0) (hgp : gradient F p = 0)
    (hq : eval q F = 0) (hgq : gradient F q = 0) (hgr : gradient F r = 0)
    (hr : r ∈ Submodule.span K ({p,q} : Set (Fin n → K)))
    (hrp : r ∉ Submodule.span K ({p} : Set (Fin n → K)))
    (hrq : r ∉ Submodule.span K ({q} : Set (Fin n → K)))
    (x : Fin n → K) (hx : x ∈ Submodule.span K ({p,q} : Set (Fin n → K))) :
    eval x F = 0 ∧ gradient F x = 0 := by
  obtain ⟨a,b,hrab⟩ := Submodule.mem_span_pair.mp hr
  have ha : a ≠ 0 := by
    intro ha
    apply hrq
    apply Submodule.mem_span_singleton.mpr
    refine ⟨b, ?_⟩
    simpa only [ha, zero_smul, zero_add] using hrab
  have hb : b ≠ 0 := by
    intro hb
    apply hrp
    apply Submodule.mem_span_singleton.mpr
    refine ⟨a, ?_⟩
    simpa only [hb, zero_smul, add_zero] using hrab
  obtain ⟨s,t,rfl⟩ := Submodule.mem_span_pair.mp hx
  apply singular_span_of_third F hF p q hp hgp hq hgq a b ha hb
  simpa only [hrab] using hgr

end CubicTenVariables.CubicSingularCollinear
