import CubicTenVariables.GoodSurfaceFibreSimultaneousBoundaryProjection

/-!
# Finitely many leading forms for one fixed saturated boundary

The good translated fibres all use the same saturated central boundary.
The integral projection matrix is chosen from one finite menu.  Choosing a
boundary image equation once for each usable matrix therefore leaves only
finitely many leading forms, up to nonzero rational scalar multiplication.

The conclusion concerns the actual cleared affine source image equations,
and their actual translated and dilated equations.  It is uniform in the
affine source, fibre target, base point, and positive progression modulus.
It introduces no counting, Bertini, or geometric literature input.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 600000
noncomputable section

namespace CubicTenVariables.GoodSurfaceFibreFiniteLeadingForms

open MvPolynomial TranslatedDepthSeven Published
open GoodSurfaceFibreSimultaneousBoundaryProjection
open GoodSurfaceFibreAffineFourStaticProjection
attribute [local instance] MvPolynomial.gradedAlgebra

/-- Any boundary equation for the same fixed boundary and the same matrix
controls the cleared affine source leading form up to a nonzero scalar.
In particular the boundary equation need not be the one stored in the
source witness. -/
theorem source_topPart_eq_const_mul_of_same_boundary_matrix
    {degree : ℕ}
    {J B : Ideal (MvPolynomial (Fin 10) ℚ)}
    (hIB : projectiveBoundaryIdeal (affineIdealProjectiveClosure J) ≤ B)
    (w : SimultaneousSourceSaturatedBoundaryMenuProjection J B degree)
    (H : MvPolynomial (Fin 4) ℚ)
    (hH : StandardAG.IsHomogeneousFiniteBirationalLinearProjection
      (degree := degree) B w.boundary_prime
      (affineChartProjectionBoundaryMatrix
        (w.matrix.map (Int.castRingHom ℚ))) H) :
    ∃ c : ℚ, c ≠ 0 ∧
      affineChartProjectionTopPart w.sourceEquation degree = C c * H := by
  obtain ⟨c, hc, heq⟩ :=
    boundary_specialization_eq_const_mul_of_saturatedProjection
      (affineIdealProjectiveClosure J) B hIB
      (affineIdealProjectiveClosure_isPrime J w.source_prime)
      (affineIdealProjectiveClosure_X_zero_not_mem J w.source_prime)
      w.matrix w.sourceEquation w.source_projection w.boundary_prime H hH
  let D : ℕ := mvPolynomialRationalCommonDenominator
    (rationalAffineProjectionEquation
      (w.matrix.map (Int.castRingHom ℚ)) w.sourceEquation)
  have hD : (D : ℚ) ≠ 0 := by
    exact_mod_cast (mvPolynomialRationalCommonDenominator_pos _).ne'
  refine ⟨(D : ℚ) * c, mul_ne_zero hD hc, ?_⟩
  change map (Int.castRingHom ℚ)
    (homogeneousComponent degree
      (clearRationalMvPolynomial
        (rationalSpecializeFirstCoordinate 1 w.sourceEquation))) = _
  rw [← integralAffineProjectionTopPart_map_intCast w.matrix w.sourceEquation,
    integralAffineProjectionTopPart_eq_const_mul_boundary _
      w.source_projection.2.2.2.2.1, heq]
  simp only [D, map_mul, mul_assoc]

/-- Select one boundary equation per usable matrix. The finite set is
chosen before every affine source and every source projection witness.
The degree and absolute irreducibility of each chosen equation are literal
properties of that polynomial. -/
theorem exists_finite_saturatedBoundary_leadingForm_menu
    (degree : ℕ) (B : Ideal (MvPolynomial (Fin 10) ℚ))
    (hBprime : B.IsPrime)
    (hBgeom : GeometricallyPrimeMvPolynomialIdeal B) :
    ∃ menu : Finset (MvPolynomial (Fin 4) ℚ),
      menu.card ≤ (affineFourSimultaneousProjectionMenu degree).card ∧
      (∀ H ∈ menu, H.IsHomogeneous degree ∧ IsAbsolutelyIrreducible H) ∧
      (∀ (J : Ideal (MvPolynomial (Fin 10) ℚ))
          (_hIB : projectiveBoundaryIdeal (affineIdealProjectiveClosure J) ≤ B)
          (w : SimultaneousSourceSaturatedBoundaryMenuProjection J B degree),
        ∃ H ∈ menu, ∃ c : ℚ, c ≠ 0 ∧
          affineChartProjectionTopPart w.sourceEquation degree = C c * H) := by
  classical
  let GoodMatrix (A : Matrix (Fin 5) (Fin 11) ℤ) : Prop :=
    ∃ H : MvPolynomial (Fin 4) ℚ,
      StandardAG.IsHomogeneousFiniteBirationalLinearProjection
        (degree := degree) B hBprime
        (affineChartProjectionBoundaryMatrix (A.map (Int.castRingHom ℚ))) H
  let matrices := (affineFourSimultaneousProjectionMenu degree).filter GoodMatrix
  let equation (A : Matrix (Fin 5) (Fin 11) ℤ) : MvPolynomial (Fin 4) ℚ :=
    if hA : GoodMatrix A then Classical.choose hA else 0
  have hprojection (A : Matrix (Fin 5) (Fin 11) ℤ) (hA : A ∈ matrices) :
      StandardAG.IsHomogeneousFiniteBirationalLinearProjection
        (degree := degree) B hBprime
        (affineChartProjectionBoundaryMatrix
          (A.map (Int.castRingHom ℚ))) (equation A) := by
    have hg : GoodMatrix A := (Finset.mem_filter.mp hA).2
    dsimp only [equation]
    rw [dif_pos hg]
    exact Classical.choose_spec hg
  let menu := matrices.image equation
  refine ⟨menu, ?_, ?_, ?_⟩
  · exact (Finset.card_image_le).trans
      (Finset.card_le_card (Finset.filter_subset _ _))
  · intro H hH
    obtain ⟨A, hA, rfl⟩ := Finset.mem_image.mp hH
    have hp := hprojection A hA
    refine ⟨hp.2.2.2.1, ?_⟩
    exact absolutelyIrreducible_of_ker_eq_span_of_geometricallyPrime
      B hBgeom
      (StandardAG.projectiveMatrixCoordinateMap B
        (affineChartProjectionBoundaryMatrix
          (A.map (Int.castRingHom ℚ))))
      (equation A) hp.2.2.2.2.1.ne_zero hp.2.2.1
  · intro J hIB w
    have hw : w.matrix ∈ matrices :=
      Finset.mem_filter.mpr ⟨w.matrix_mem, w.boundaryEquation, w.boundary_projection⟩
    refine ⟨equation w.matrix, ?_, ?_⟩
    · exact Finset.mem_image.mpr ⟨w.matrix, hw, rfl⟩
    · exact source_topPart_eq_const_mul_of_same_boundary_matrix hIB w
        (equation w.matrix) (hprojection w.matrix hw)

/-- The same finite leading-form set controls every actual equation after
translation by an arbitrary integral base and dilation by an arbitrary
positive modulus. All dependence on those parameters is confined to a
nonzero scalar. -/
theorem exists_finite_saturatedBoundary_dynamic_topPart_menu
    (degree : ℕ) (B : Ideal (MvPolynomial (Fin 10) ℚ))
    (hBprime : B.IsPrime)
    (hBgeom : GeometricallyPrimeMvPolynomialIdeal B) :
    ∃ menu : Finset (MvPolynomial (Fin 4) ℚ),
      menu.card ≤ (affineFourSimultaneousProjectionMenu degree).card ∧
      (∀ H ∈ menu, H.IsHomogeneous degree ∧ IsAbsolutelyIrreducible H) ∧
      (∀ (J : Ideal (MvPolynomial (Fin 10) ℚ))
          (_hIB : projectiveBoundaryIdeal (affineIdealProjectiveClosure J) ≤ B)
          (w : SimultaneousSourceSaturatedBoundaryMenuProjection J B degree)
          (base : IntVector 4) (m : ℕ), 0 < m →
        ∃ H ∈ menu, ∃ c : ℚ, c ≠ 0 ∧
          IsTopHomogeneousPart
            (integralAffineTransform base m
              (affineChartProjectionEquation w.sourceEquation))
            (C c * H) degree) := by
  obtain ⟨menu, hcard, hforms, hsource⟩ :=
    exists_finite_saturatedBoundary_leadingForm_menu degree B hBprime hBgeom
  refine ⟨menu, hcard, hforms, ?_⟩
  intro J hIB w base m hm
  obtain ⟨H, hH, c, hc, heq⟩ := hsource J hIB w
  have habsolute : IsAbsolutelyIrreducible
      (affineChartProjectionTopPart w.sourceEquation degree) := by
    rw [heq]
    exact (hforms H hH).2.const_mul c hc
  have htop := affineChartProjectionEquation_isTopHomogeneousPart
    w.source_projection.2.2.2.2.1 habsolute
  have hdynamic := isTopHomogeneousPart_integralAffineTransform base hm htop
  have hmQ : (m : ℚ) ≠ 0 := by exact_mod_cast hm.ne'
  refine ⟨H, hH, (m : ℚ) ^ degree * c,
    mul_ne_zero (pow_ne_zero degree hmQ) hc, ?_⟩
  simpa only [heq, map_mul, mul_assoc] using hdynamic

end CubicTenVariables.GoodSurfaceFibreFiniteLeadingForms
