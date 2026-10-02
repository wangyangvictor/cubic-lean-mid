import Mathlib

/-! # Literal absolute irreducibility of rational multivariate polynomials -/

namespace TranslatedDepthSeven.Published

noncomputable section

/-- Irreducibility after extending coefficients to an algebraic closure of
`ℚ`. This is the absolute-irreducibility hypothesis in the corrected form
of Salberger 2023, Theorem 0.4. -/
def IsAbsolutelyIrreducible {σ : Type*} (f : MvPolynomial σ ℚ) : Prop :=
  Irreducible (MvPolynomial.map (algebraMap ℚ (AlgebraicClosure ℚ)) f)

theorem IsAbsolutelyIrreducible.ne_zero {σ : Type*}
    {f : MvPolynomial σ ℚ} (hf : IsAbsolutelyIrreducible f) : f ≠ 0 := by
  unfold IsAbsolutelyIrreducible at hf
  intro h
  exact hf.ne_zero (by simp [h])

theorem IsAbsolutelyIrreducible.const_mul {σ : Type*}
    {f : MvPolynomial σ ℚ} (hf : IsAbsolutelyIrreducible f)
    (c : ℚ) (hc : c ≠ 0) :
    IsAbsolutelyIrreducible (MvPolynomial.C c * f) := by
  unfold IsAbsolutelyIrreducible at hf ⊢
  rw [map_mul, MvPolynomial.map_C]
  apply (irreducible_isUnit_mul _).2 hf
  exact (isUnit_iff_ne_zero.mpr ((map_ne_zero (algebraMap ℚ
    (AlgebraicClosure ℚ))).2 hc)).map MvPolynomial.C

end
end TranslatedDepthSeven.Published
