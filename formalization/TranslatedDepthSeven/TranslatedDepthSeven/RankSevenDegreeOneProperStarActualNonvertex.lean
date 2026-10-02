import TranslatedDepthSeven.RankSevenDegreeOneProperStarActualFibre

/-!
# Uniform nonvertex bound for the actual selected record fibre

The four-alternative projective-star estimate is applied here to the exact
finite image constructed from the literal node, edge, and persistent record
cells.  Constants are selected before the cutoff, translated box, records,
component occurrence, and low direction.

The theorem covers both Jacobian-regular and Jacobian-singular centres.  Its
only excluded centres are genuine projective-vertex directions.
-/

namespace TranslatedDepthSeven

noncomputable section

open MvPolynomial Published

attribute [local instance] MvPolynomial.gradedAlgebra

set_option maxHeartbeats 20000000

/-- The selected underlying points of every actual low nonvertex direction
obey the coefficient-uniform `4 + epsilon` star bound.  No grouped-fibre
bound occurs among the hypotheses. -/
theorem exists_uniform_rankSevenDegreeOne_actual_selected_nonvertex_bound
    (hline : StandardAG.DegreeOneAffinePrimeCurveIsIntegralLine)
    (hPila : Pila1995TheoremA)
    (hSalberger : Salberger2023Theorem04)
    (hProjection : StandardAG.BoundedDegreeHomogeneousProjectionMenu)
    (hHilbert : StandardAG.ProjectiveHilbertDegreeCertification ℚ)
    (hBezout : StandardAG.FiniteEquationProjectiveComponentBezoutBounds)
    (hstarVertex : StandardAG.ProjectiveStarEqualityForcesVertex)
    (hHyperplane : StandardAG.GeometricallyIntegralProjectiveFourfoldHyperplaneRealDegreeMass)
    (hDegreeSpan : StandardAG.ProjectiveDegreeSpanInequality ℚ)
    (hRationalSmooth : StandardAG.RationalProjectiveSmoothPointGeometricIntegrality)
    (hQbarDetectsGeometricPrimeness :
      ∀ (N : ℕ) (I : Ideal (MvPolynomial (Fin N) ℚ)),
        (qbarCoefficientExtensionIdeal I).IsPrime →
          GeometricallyPrimeMvPolynomialIdeal I)
    (equations : Finset (MvPolynomial (Fin 13) ℤ))
    (degree : MvPolynomial (Fin 13) ℤ → ℕ)
    (hdegree : ∀ f ∈ equations, f.IsHomogeneous (degree f))
    {originalDegree : ℕ}
    (hOriginal : HasProjectiveDimensionDegree
      (rationalDepthSevenEquationIdeal equations) 5 originalDegree)
    (hOriginalPrime :
      (rationalDepthSevenEquationIdeal equations).IsPrime)
    (hOriginalGeometricallyPrime : GeometricallyPrimeMvPolynomialIdeal
      (rationalDepthSevenEquationIdeal equations)) :
    ∃ CF0 : ℕ, ∀ (epsilon : ℝ), 0 < epsilon →
    ∃ K : ℕ, ∃ C : ℝ, 0 < C ∧
      ∀ (CF : ℕ), CF0 ≤ CF →
      ∀ (p : Parameters) (x₀ : IntVector 13)
        (Cchart : IntegralDepthSevenJacobianChartIndex equations)
        (model : FixedFivefoldResidueModel
          (indexedFinsetFamily (rationalizedEquationFinset equations)))
        (P : Finset ℕ) (k markCount : ℕ)
        (hPrime : ∀ s ∈ P, s.Prime)
        (hlower : ∀ q : ReservoirModulus P k,
          manuscriptReservoirTarget normalizedSurfaceReservoirConstant
            p.T (5 / 7) ≤ q.1)
        (I : Ideal (MvPolynomial (Fin 14) ℚ))
        (X : Finset (IntVector 13))
        (hX : X ⊆ rankSevenPersistentSurfaceCell
          p x₀ equations CF Cchart model.denominator P k hPrime hlower I)
        (localEquations : Fin 11 → MvPolynomial (Fin 13) ℤ)
        (selectedVar : Fin 11 → Fin 13)
        (menu : Fin markCount → MvPolynomial (Fin 13) ℤ)
        (markOf : IntVector 13 → Fin markCount)
        (auxiliaryForm : RankSevenPersistentRecord P k markCount →
          MvPolynomial (Fin 14) ℚ),
      let J := rankSevenDegreeOneIdeal p x₀ equations CF Cchart model P k
        markCount hPrime hlower I X localEquations selectedVar menu markOf
          auxiliaryForm
      let Y := rankSevenDegreeOnePointSet p x₀ equations CF Cchart model P k
        markCount hPrime hlower I X localEquations selectedVar menu markOf
      ∃ (base direction : TaggedLinearComponent J → IntVector 13)
        (parameter : TaggedLinearComponent J → IntVector 13 → ℤ),
        (∀ o ∈ activeTaggedLinearComponents J Y,
          PrimitiveDirection (direction o) ∧
          Set.InjOn (parameter o)
            (↑((assignedLinearComponentFibre J Y o).image
              (fun x ↦ x.2.1)) : Set (IntVector 13)) ∧
          (∀ z ∈ (assignedLinearComponentFibre J Y o).image
              (fun x ↦ x.2.1),
            z = fun i ↦ base o i + parameter o z * direction o i) ∧
          affineIdealZeroLocus o.2.1 =
            Set.range (fun t : ℝ ↦
              fun i ↦ (base o i : ℝ) + t * (direction o i : ℝ)) ∧
          (∀ t : ℤ, IntegralCommonZero equations
            (integralAffineMap x₀
              (fun i ↦ base o i + t * direction o i) p.m)) ∧
          IntegralCommonZero equations (direction o)) ∧
        ∀ o ∈ activeTaggedLinearComponents J Y,
          directionHeight (direction o) ≤
              lowDirectionNaturalRadius (surfaceTangentRealSide p) →
          ¬ LiesInGeometricProjectiveVertex (direction o)
              (rationalDepthSevenEquationIdeal equations) →
          let h := integralProjectiveClassOrFirstRankSeven (direction o)
          let Z := activeSelectedUnderlyingDirectionImage J Y direction h
          (Z.card : ℝ) ≤ C *
            (((max 1 K *
              max 1 (2 * surfaceTangentNaturalSide p) + 1 : ℕ) : ℝ) ^
                ((4 : ℝ) + epsilon)) := by
  classical
  obtain ⟨CF0, hstarUniform⟩ :=
    exists_uniform_low_nonvertex_projectiveStar_bound
      hPila hSalberger hProjection hHilbert hBezout hstarVertex hHyperplane
        hDegreeSpan hRationalSmooth hQbarDetectsGeometricPrimeness equations degree
          hdegree hOriginal hOriginalPrime hOriginalGeometricallyPrime
  refine ⟨CF0, ?_⟩
  intro epsilon hepsilon
  obtain ⟨K, C, hC, hstarBound⟩ := hstarUniform epsilon hepsilon
  refine ⟨K, C, hC, ?_⟩
  intro CF hCF p x₀ Cchart model P k markCount hPrime hlower I X hX
    localEquations selectedVar menu markOf auxiliaryForm
  dsimp only
  let J := rankSevenDegreeOneIdeal p x₀ equations CF Cchart model P k
    markCount hPrime hlower I X localEquations selectedVar menu markOf
      auxiliaryForm
  let Y := rankSevenDegreeOnePointSet p x₀ equations CF Cchart model P k
    markCount hPrime hlower I X localEquations selectedVar menu markOf
  obtain ⟨base, direction, parameter, hfull, hfibres⟩ :=
    exists_rankSevenDegreeOne_actual_selected_fibres_in_one_star
      hline p x₀ equations CF degree hdegree Cchart model P k markCount
        hPrime hlower I X hX localEquations selectedVar menu markOf
          auxiliaryForm
  refine ⟨base, direction, parameter, hfull, ?_⟩
  intro o ho hlow hnotVertex
  let h := integralProjectiveClassOrFirstRankSeven (direction o)
  let Z := activeSelectedUnderlyingDirectionImage J Y direction h
  have hproperties := hfibres o ho
  have hprimitive : PrimitiveDirection (direction o) := (hfull o ho).1
  have hne : direction o ≠ 0 := by
    intro hz
    obtain ⟨i, hi⟩ := hprimitive.exists_ne_zero
    exact hi (congrFun hz i)
  have hzero : IntegralCommonZero equations (direction o) :=
    (hfull o ho).2.2.2.2.2
  have hM : 1 ≤ 2 * surfaceTangentNaturalSide p := by
    have hs := one_le_surfaceTangentNaturalSide p
    omega
  exact hstarBound CF hCF p x₀ (direction o) hlow hne hzero hnotVertex
    (2 * surfaceTangentNaturalSide p) hM Z hproperties.2.1
      hproperties.2.2.1 hproperties.2.2.2

end

end TranslatedDepthSeven
