import Mathlib.RingTheory.Smooth.StandardSmooth

/-!
# A localized complete intersection is standard smooth

This file records the component-free algebraic core of the vertical
specialization argument.  Start with a literal quotient of a finite-variable
polynomial ring by finitely many equations, choose distinct variables for the
relations, and let `jacobian` be the resulting selected Jacobian determinant.
After localizing away from any multiple of `jacobian`, the quotient is standard
smooth of the expected relative dimension.

The proof uses the exact naive presentation of the quotient and composes it
with the canonical presentation of a localization.  In particular, it makes
no assertion identifying the displayed equations with the ideal of a separate
component.
-/

noncomputable section

open MvPolynomial

namespace TranslatedDepthSeven

universe u v w z

variable {R : Type u} [CommRing R]
variable {vars : Type v} {rels : Type w} [Finite vars] [Finite rels]

/-- The literal quotient by a finite family of multivariable polynomials. -/
abbrev EquationQuotient (equations : rels → MvPolynomial vars R) :=
  MvPolynomial vars R ⧸ Ideal.span (Set.range equations)

/-- The naive pre-submersive presentation associated to a choice of one
distinct variable for each relation. -/
def equationPreSubmersivePresentation
    (equations : rels → MvPolynomial vars R)
    (selectedVar : rels → vars) (hselected : Function.Injective selectedVar) :
    Algebra.PreSubmersivePresentation R (EquationQuotient equations) vars rels :=
  Algebra.PreSubmersivePresentation.naive (v := equations) selectedVar hselected

/-- Localizing a quotient by `rels` equations in `vars` variables away from a
multiple of the selected Jacobian determinant gives a standard-smooth algebra
of relative dimension `Nat.card vars - Nat.card rels`.

The target `T` may be any chosen realization of the indicated localization.
-/
theorem equationQuotient_localizedAt_mul_jacobian_isStandardSmoothOfRelativeDimension
    (equations : rels → MvPolynomial vars R)
    (selectedVar : rels → vars) (hselected : Function.Injective selectedVar)
    (h : EquationQuotient equations)
    (T : Type z) [CommRing T] [Algebra (EquationQuotient equations) T]
    [Algebra R T] [IsScalarTower R (EquationQuotient equations) T]
    [IsLocalization.Away
      (h * (equationPreSubmersivePresentation equations selectedVar hselected).jacobian) T] :
    Algebra.IsStandardSmoothOfRelativeDimension
      (Nat.card vars - Nat.card rels) R T := by
  let P := equationPreSubmersivePresentation equations selectedVar hselected
  let localizationElement : EquationQuotient equations := h * P.jacobian
  let Q : Algebra.SubmersivePresentation
      (EquationQuotient equations) T Unit Unit :=
    Algebra.SubmersivePresentation.localizationAway T localizationElement
  let PQpre : Algebra.PreSubmersivePresentation R T (Unit ⊕ vars) (Unit ⊕ rels) :=
    Q.toPreSubmersivePresentation.comp P
  have hjacobian : IsUnit (algebraMap (EquationQuotient equations) T P.jacobian) := by
    have hproduct : IsUnit
        (algebraMap (EquationQuotient equations) T (h * P.jacobian)) := by
      exact IsLocalization.map_units T
        ⟨h * P.jacobian, Submonoid.mem_powers (h * P.jacobian)⟩
    rw [map_mul, IsUnit.mul_iff] at hproduct
    exact hproduct.2
  let PQ : Algebra.SubmersivePresentation R T (Unit ⊕ vars) (Unit ⊕ rels) :=
    { toPreSubmersivePresentation := PQpre
      jacobian_isUnit := by
        rw [show PQpre = Q.toPreSubmersivePresentation.comp P from rfl]
        rw [Algebra.PreSubmersivePresentation.comp_jacobian_eq_jacobian_smul_jacobian,
          Algebra.smul_def, IsUnit.mul_iff]
        exact ⟨hjacobian, Q.jacobian_isUnit⟩ }
  apply PQ.isStandardSmoothOfRelativeDimension
  change (Q.toPreSubmersivePresentation.comp P).dimension =
    Nat.card vars - Nat.card rels
  rw [Algebra.PreSubmersivePresentation.dimension_comp_eq_dimension_add_dimension]
  simp [Algebra.Presentation.dimension]

/-- The finite-index specialization of
`equationQuotient_localizedAt_mul_jacobian_isStandardSmoothOfRelativeDimension`.
-/
theorem finEquationQuotient_localizedAt_mul_jacobian_isStandardSmoothOfRelativeDimension
    {N r : ℕ} (equations : Fin r → MvPolynomial (Fin N) R)
    (selectedVar : Fin r → Fin N) (hselected : Function.Injective selectedVar)
    (h : EquationQuotient equations)
    (T : Type z) [CommRing T] [Algebra (EquationQuotient equations) T]
    [Algebra R T] [IsScalarTower R (EquationQuotient equations) T]
    [IsLocalization.Away
      (h * (equationPreSubmersivePresentation equations selectedVar hselected).jacobian) T] :
    Algebra.IsStandardSmoothOfRelativeDimension (N - r) R T := by
  simpa using
    equationQuotient_localizedAt_mul_jacobian_isStandardSmoothOfRelativeDimension
      equations selectedVar hselected h T

end TranslatedDepthSeven
