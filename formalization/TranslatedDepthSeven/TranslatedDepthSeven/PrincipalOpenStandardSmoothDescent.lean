import TranslatedDepthSeven.FiniteZeroRelationDescent
import TranslatedDepthSeven.LocalizedCompleteIntersectionStandardSmooth
import TranslatedDepthSeven.ScalarExtensionStability

/-!
# A marked standard-smooth chart on one parameter principal open

Let `R₀ → R` be a parameter algebra and let a finite family of equations
over `R` be equipped with a marked `R`-valued tuple.  Assume that the
equations vanish at that tuple after the elements of a submonoid `M ⊆ R₀`
are inverted.  Fix a selected-Jacobian chart in the literal equation
quotient, together with a polynomial representative of its localization
element.  If the value of that representative is a unit on the generic
localization, then finitely many zero relations and the localization unit
criterion give one product `δ ∈ M` on which:

* the marked tuple defines a point of the equation quotient;
* the chart element is a unit at that point;
* the point lifts to the selected-Jacobian localization; and
* after scalar extension from `R` to `R[1/δ]`, this chart is standard
  smooth of the expected relative dimension.

Everything is expressed using the displayed equations, marked coordinates,
and one displayed representative of the chart element.  There is no
component space, Hilbert scheme, Chow variety, or assertion that the
displayed quotient is a separate selected component.
-/

namespace TranslatedDepthSeven

noncomputable section

open MvPolynomial
open scoped TensorProduct

universe u v w

/-- A point of an `R`-algebra extends canonically to a point of its scalar
base change.  This version only requires commutative rings. -/
def baseChangePointAlgHom
    (R : Type u) (S : Type v) (A : Type w)
    [CommRing R] [CommRing S] [CommRing A]
    [Algebra R S] [Algebra R A]
    (g : A →ₐ[R] S) : (S ⊗[R] A) →ₐ[S] S :=
  Algebra.TensorProduct.lift (AlgHom.id S S) g
    (fun _ _ ↦ mul_comm _ _)

@[simp]
theorem baseChangePointAlgHom_includeRight
    (R : Type u) (S : Type v) (A : Type w)
    [CommRing R] [CommRing S] [CommRing A]
    [Algebra R S] [Algebra R A]
    (g : A →ₐ[R] S) (x : A) :
    baseChangePointAlgHom R S A g
        (Algebra.TensorProduct.includeRight x) = g x := by
  simp [baseChangePointAlgHom]

/-- Vertical descent of a marked selected-Jacobian chart.

`chartLift` is a literal polynomial representative of the quotient element
`h * jacobian`.  The generic-unit hypothesis `hchartGeneric` says that its
value at the marked tuple is invertible after all elements of `M` have been
inverted.  The returned denominator is the product of a denominator clearing
the equation values and an element of `M` divisible by the chart value.

The conclusion supplies an actual point of the scalar-extended chart and
records its values on all affine coordinates. -/
theorem exists_principalOpen_marked_standardSmooth_chart
    {R₀ : Type u} {R : Type v} [CommRing R₀] [CommRing R] [Algebra R₀ R]
    (M : Submonoid R₀) {N r : ℕ}
    (equations : Fin r → MvPolynomial (Fin N) R)
    (selectedVar : Fin r → Fin N)
    (hselected : Function.Injective selectedVar)
    (y : Fin N → R)
    (h : EquationQuotient equations)
    (chartLift : MvPolynomial (Fin N) R)
    (hchartLift :
      Ideal.Quotient.mk (Ideal.span (Set.range equations)) chartLift =
        h *
          (equationPreSubmersivePresentation
            equations selectedVar hselected).jacobian)
    (hequationsGeneric : ∀ i,
      algebraMap R
          (Localization (M.map (algebraMap R₀ R)))
          (MvPolynomial.eval y (equations i)) = 0)
    (hchartGeneric :
      IsUnit (algebraMap R
          (Localization (M.map (algebraMap R₀ R)))
          (MvPolynomial.eval y chartLift))) :
    ∃ δ : R₀, δ ∈ M ∧
      let Rδ := Localization.Away (algebraMap R₀ R δ)
      let Q := EquationQuotient equations
      let chart : Q :=
        h *
          (equationPreSubmersivePresentation
            equations selectedVar hselected).jacobian
      let T := Localization.Away chart
      ∃ point : (Rδ ⊗[R] T) →ₐ[Rδ] Rδ,
        (∀ i,
          point
              (Algebra.TensorProduct.includeRight
                (algebraMap Q T
                  (Ideal.Quotient.mk
                    (Ideal.span (Set.range equations))
                    (MvPolynomial.X i)))) =
            algebraMap R Rδ (y i)) ∧
        Algebra.IsStandardSmoothOfRelativeDimension
          (N - r) Rδ (Rδ ⊗[R] T) := by
  classical
  obtain ⟨mEq, hmEqClear, _hmEqAway⟩ :=
    exists_submonoid_element_killing_finite_family_of_localization_eq_zero
      M (fun i ↦ MvPolynomial.eval y (equations i)) hequationsGeneric
  obtain ⟨chartDenom, hchartDenomM, hchartDiv⟩ :=
    (IsLocalization.algebraMap_isUnit_iff
      (M.map (algebraMap R₀ R))).mp hchartGeneric
  obtain ⟨mChartValue, hmChartM, hmChartEq⟩ :=
    Submonoid.mem_map.mp hchartDenomM
  let mChart : M := ⟨mChartValue, hmChartM⟩
  have hchartDivBase :
      MvPolynomial.eval y chartLift ∣ algebraMap R₀ R (mChart : R₀) := by
    rw [hmChartEq]
    exact hchartDiv
  let δ : R₀ := (mEq : R₀) * (mChart : R₀)
  have hδM : δ ∈ M := by
    exact M.mul_mem mEq.property mChart.property
  let Rδ := Localization.Away (algebraMap R₀ R δ)
  let Q := EquationQuotient equations
  let P := equationPreSubmersivePresentation
    equations selectedVar hselected
  let chart : Q := h * P.jacobian
  let T := Localization.Away chart
  let yδ : Fin N → Rδ := fun i ↦ algebraMap R Rδ (y i)
  have hEqRδ : ∀ i,
      algebraMap R Rδ (MvPolynomial.eval y (equations i)) = 0 := by
    intro i
    apply (IsUnit.mul_right_eq_zero
      (IsLocalization.Away.algebraMap_isUnit (algebraMap R₀ R δ))).mp
    rw [← map_mul]
    have hkill :
        algebraMap R₀ R δ * MvPolynomial.eval y (equations i) = 0 := by
      change algebraMap R₀ R
          ((mEq : R₀) * (mChart : R₀)) *
            MvPolynomial.eval y (equations i) = 0
      rw [map_mul]
      calc
        (algebraMap R₀ R (mEq : R₀) *
              algebraMap R₀ R (mChart : R₀)) *
            MvPolynomial.eval y (equations i) =
            algebraMap R₀ R (mChart : R₀) *
              (algebraMap R₀ R (mEq : R₀) *
                MvPolynomial.eval y (equations i)) := by ring
        _ = 0 := by rw [hmEqClear i, mul_zero]
    rw [hkill, map_zero]
  have hIdeal :
      Ideal.span (Set.range equations) ≤
        RingHom.ker (MvPolynomial.aeval yδ).toRingHom := by
    rw [Ideal.span_le]
    rintro f ⟨i, rfl⟩
    change MvPolynomial.aeval yδ (equations i) = 0
    rw [MvPolynomial.aeval_def]
    change MvPolynomial.eval₂ (algebraMap R Rδ)
      ((algebraMap R Rδ) ∘ y) (equations i) = 0
    rw [← MvPolynomial.eval₂_comp]
    exact hEqRδ i
  let qpoint : Q →ₐ[R] Rδ :=
    Ideal.Quotient.liftₐ
      (Ideal.span (Set.range equations))
      (MvPolynomial.aeval yδ) hIdeal
  have hChartValue :
      qpoint chart =
        algebraMap R Rδ (MvPolynomial.eval y chartLift) := by
    calc
      qpoint chart = qpoint
          (Ideal.Quotient.mk
            (Ideal.span (Set.range equations)) chartLift) := by
          rw [hchartLift]
      _ = MvPolynomial.aeval yδ chartLift := rfl
      _ = algebraMap R Rδ (MvPolynomial.eval y chartLift) := by
          rw [MvPolynomial.aeval_def]
          change MvPolynomial.eval₂ (algebraMap R Rδ)
            ((algebraMap R Rδ) ∘ y) chartLift = _
          rw [← MvPolynomial.eval₂_comp]
  have hJunit :
      IsUnit (algebraMap R Rδ (MvPolynomial.eval y chartLift)) := by
    have hmChartDvd :
        algebraMap R₀ R (mChart : R₀) ∣ algebraMap R₀ R δ := by
      refine ⟨algebraMap R₀ R (mEq : R₀), ?_⟩
      change algebraMap R₀ R ((mEq : R₀) * (mChart : R₀)) = _
      rw [map_mul]
      ring
    have hdvd :
        MvPolynomial.eval y chartLift ∣ algebraMap R₀ R δ :=
      dvd_trans hchartDivBase hmChartDvd
    exact IsLocalization.Away.isUnit_of_dvd
      (algebraMap R₀ R δ) (S := Rδ) hdvd
  have hChartUnit : IsUnit (qpoint chart) := by
    rw [hChartValue]
    exact hJunit
  have hmapUnits : ∀ z : Submonoid.powers chart, IsUnit (qpoint z) := by
    rintro ⟨z, n, rfl⟩
    simpa only [map_pow] using hChartUnit.pow n
  let chartPoint : T →ₐ[R] Rδ :=
    IsLocalization.liftAlgHom hmapUnits
  let point : (Rδ ⊗[R] T) →ₐ[Rδ] Rδ :=
    baseChangePointAlgHom R Rδ T chartPoint
  have hcoordinates : ∀ i,
      point
          (Algebra.TensorProduct.includeRight
            (algebraMap Q T
              (Ideal.Quotient.mk
                (Ideal.span (Set.range equations))
                (MvPolynomial.X i)))) =
        algebraMap R Rδ (y i) := by
    intro i
    change baseChangePointAlgHom R Rδ T chartPoint
        (Algebra.TensorProduct.includeRight
          (algebraMap Q T
            (Ideal.Quotient.mk
              (Ideal.span (Set.range equations))
              (MvPolynomial.X i)))) = _
    rw [baseChangePointAlgHom_includeRight]
    change chartPoint
        (algebraMap Q T
          (Ideal.Quotient.mk
            (Ideal.span (Set.range equations))
            (MvPolynomial.X i))) = _
    change (IsLocalization.liftAlgHom hmapUnits)
        (algebraMap Q T
          (Ideal.Quotient.mk
            (Ideal.span (Set.range equations))
            (MvPolynomial.X i))) = _
    rw [IsLocalization.liftAlgHom_apply, IsLocalization.lift_eq]
    change MvPolynomial.aeval
        (fun k ↦ algebraMap R Rδ (y k)) (MvPolynomial.X i) = _
    simp
  have hstandardR :
      Algebra.IsStandardSmoothOfRelativeDimension (N - r) R T := by
    exact
      finEquationQuotient_localizedAt_mul_jacobian_isStandardSmoothOfRelativeDimension
        equations selectedVar hselected h T
  letI : Algebra.IsStandardSmoothOfRelativeDimension (N - r) R T :=
    hstandardR
  have hstandardRδ :
      Algebra.IsStandardSmoothOfRelativeDimension
        (N - r) Rδ (Rδ ⊗[R] T) :=
    standardSmooth_relativeDimension_stable_under_baseChange
  exact ⟨δ, hδM, point, hcoordinates, hstandardRδ⟩

end

end TranslatedDepthSeven
