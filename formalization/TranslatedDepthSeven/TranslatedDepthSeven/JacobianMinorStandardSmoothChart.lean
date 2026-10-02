import TranslatedDepthSeven.LocalizedCompleteIntersectionStandardSmooth
import TranslatedDepthSeven.RationalPointResidueField

/-!
# A literal Jacobian-minor chart at a rational point

For a finite family of affine equations, this file writes down the selected
Jacobian determinant in the polynomial ring.  If those equations generate
the displayed component ideal and the determinant is nonzero at a marked
rational point, evaluation extends to the corresponding principal open and
that principal open is standard smooth of the expected relative dimension.

The hypotheses are equations, an equality of ideals, a pointwise vanishing
condition, and one explicit determinant inequality.  No smoothness or
component-presentation predicate is assumed.
-/

namespace TranslatedDepthSeven

noncomputable section

open MvPolynomial

universe u

section CommRing

variable {k : Type u} [CommRing k]

/-- The determinant of the derivatives of the displayed equations in the
displayed distinct variables. -/
noncomputable def selectedJacobianDeterminant {N c : ℕ}
    (equations : Fin c → MvPolynomial (Fin N) k)
    (selectedVar : Fin c → Fin N) : MvPolynomial (Fin N) k :=
  Matrix.det (Matrix.of fun i j ↦
    MvPolynomial.pderiv (selectedVar i) (equations j))

/-- The literal selected Jacobian determinant commutes with extension of
coefficients.  This is the coefficient-specialization identity needed when
one fixed characteristic-zero chart is reduced modulo all primes outside a
single denominator. -/
theorem map_selectedJacobianDeterminant
    {K L : Type*} [CommRing K] [CommRing L] (φ : K →+* L)
    {N c : ℕ} (equations : Fin c → MvPolynomial (Fin N) K)
    (selectedVar : Fin c → Fin N) :
    MvPolynomial.map φ
        (selectedJacobianDeterminant equations selectedVar) =
      selectedJacobianDeterminant
        (fun i ↦ MvPolynomial.map φ (equations i)) selectedVar := by
  rw [selectedJacobianDeterminant, selectedJacobianDeterminant,
    (MvPolynomial.map φ).map_det]
  apply congrArg Matrix.det
  apply Matrix.ext
  intro i j
  change MvPolynomial.map φ
      (MvPolynomial.pderiv (selectedVar i) (equations j)) =
    MvPolynomial.pderiv (selectedVar i)
      (MvPolynomial.map φ (equations j))
  rw [MvPolynomial.pderiv_map]

end CommRing

variable {k : Type u} [Field k]

/-- The abstract Jacobian of the naive pre-submersive presentation is the
quotient class of the literal selected determinant. -/
theorem equationPreSubmersivePresentation_jacobian_eq_mk_selectedJacobian
    {N c : ℕ} (equations : Fin c → MvPolynomial (Fin N) k)
    (selectedVar : Fin c → Fin N)
    (hselected : Function.Injective selectedVar) :
    (equationPreSubmersivePresentation
      equations selectedVar hselected).jacobian =
      Ideal.Quotient.mk (Ideal.span (Set.range equations))
        (selectedJacobianDeterminant equations selectedVar) := by
  classical
  let P := equationPreSubmersivePresentation
    equations selectedVar hselected
  rw [P.jacobian_eq_jacobiMatrix_det]
  change Ideal.Quotient.mk (Ideal.span (Set.range equations))
      P.jacobiMatrix.det =
    Ideal.Quotient.mk (Ideal.span (Set.range equations))
      (selectedJacobianDeterminant equations selectedVar)
  congr 1
  apply congrArg Matrix.det
  apply Matrix.ext
  intro i j
  simp [P, equationPreSubmersivePresentation,
    Algebra.PreSubmersivePresentation.jacobiMatrix_naive]

/-- A nonzero selected Jacobian minor produces a marked standard-smooth
principal open of the literal quotient by the displayed ideal.

The ideal equality is deliberately an equality of the concrete ideals in
the polynomial ring.  Thus the statement can be applied after any earlier
localization or affine change of coordinates simply by instantiating `k`,
the equations, and `J` with those literal objects. -/
theorem selectedJacobian_principalOpen_standardSmooth_and_point
    {N c : ℕ} (equations : Fin c → MvPolynomial (Fin N) k)
    (selectedVar : Fin c → Fin N)
    (hselected : Function.Injective selectedVar)
    (J : Ideal (MvPolynomial (Fin N) k))
    (hJ : Ideal.span (Set.range equations) = J)
    (z : Fin N → k)
    (hz : J ≤ RingHom.ker (MvPolynomial.aeval z).toRingHom)
    (hminor : MvPolynomial.aeval z
      (selectedJacobianDeterminant equations selectedVar) ≠ 0) :
    let Q := MvPolynomial (Fin N) k ⧸ J
    let chart : Q := Ideal.Quotient.mk J
      (selectedJacobianDeterminant equations selectedVar)
    let T := Localization.Away chart
    ∃ point : T →ₐ[k] k,
      point.comp (IsScalarTower.toAlgHom k Q T) =
          affineQuotientRationalPoint J z hz ∧
        Algebra.IsStandardSmoothOfRelativeDimension (N - c) k T := by
  classical
  subst J
  let Q := EquationQuotient equations
  let P := equationPreSubmersivePresentation
    equations selectedVar hselected
  let chart : Q := Ideal.Quotient.mk (Ideal.span (Set.range equations))
    (selectedJacobianDeterminant equations selectedVar)
  let T := Localization.Away chart
  let pointQ : Q →ₐ[k] k := affineQuotientRationalPoint
    (Ideal.span (Set.range equations)) z hz
  have hchartValue : pointQ chart =
      MvPolynomial.aeval z
        (selectedJacobianDeterminant equations selectedVar) := by
    rfl
  have hchartUnit : IsUnit (pointQ chart) := by
    rw [hchartValue]
    exact (isUnit_iff_ne_zero.mpr hminor)
  have hmapUnits : ∀ s : Submonoid.powers chart, IsUnit (pointQ s) := by
    rintro ⟨s, n, rfl⟩
    simpa only [map_pow] using hchartUnit.pow n
  let point : T →ₐ[k] k := IsLocalization.liftAlgHom hmapUnits
  have hpoint : point.comp (IsScalarTower.toAlgHom k Q T) = pointQ := by
    apply AlgHom.ext
    intro x
    change point (algebraMap Q T x) = pointQ x
    change (IsLocalization.liftAlgHom hmapUnits)
      (algebraMap Q T x) = pointQ x
    rw [IsLocalization.liftAlgHom_apply, IsLocalization.lift_eq]
    rfl
  have hchartEq : chart = P.jacobian := by
    exact (equationPreSubmersivePresentation_jacobian_eq_mk_selectedJacobian
      equations selectedVar hselected).symm
  letI : IsLocalization.Away (1 * P.jacobian) T := by
    simp only [one_mul]
    rw [← hchartEq]
    infer_instance
  have hstandard :
      Algebra.IsStandardSmoothOfRelativeDimension (N - c) k T :=
    finEquationQuotient_localizedAt_mul_jacobian_isStandardSmoothOfRelativeDimension
      equations selectedVar hselected 1 T
  exact ⟨point, hpoint, hstandard⟩

end

end TranslatedDepthSeven
