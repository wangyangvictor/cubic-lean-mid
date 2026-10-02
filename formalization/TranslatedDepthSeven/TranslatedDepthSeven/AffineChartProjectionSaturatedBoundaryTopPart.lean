import TranslatedDepthSeven.AffineChartProjectionBoundaryTopPart

/-!
# Leading forms from a saturated boundary projection

The image equation at infinity already lies in the projection kernel of
the literal boundary.  Hence it lies in the kernel for every larger
saturated boundary ideal.  This is the only change needed to identify the
leading form with the equation of a birational projection of that
saturated boundary.
-/

namespace TranslatedDepthSeven

noncomputable section

open MvPolynomial Published StandardAG

attribute [local instance] MvPolynomial.gradedAlgebra

set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 500000

/-- Kernel membership at infinity persists after enlarging the literal
boundary ideal to a saturated boundary. -/
theorem boundary_specialization_mem_saturatedProjection_kernel
    {N r : ℕ}
    (I : Ideal (MvPolynomial (Fin (N + 1)) ℚ))
    (B : Ideal (MvPolynomial (Fin N) ℚ))
    (hIB : projectiveBoundaryIdeal I ≤ B)
    (A : Matrix (Fin (r + 2)) (Fin (N + 1)) ℚ)
    (hfirst : FirstFinProjectionRowIsHomogenizingCoordinate A)
    (G : MvPolynomial (Fin (r + 2)) ℚ)
    (hG : G ∈ RingHom.ker
      (projectiveMatrixCoordinateMap I A).toRingHom) :
    rationalSpecializeFirstCoordinate 0 G ∈ RingHom.ker
      (projectiveMatrixCoordinateMap B
        (affineChartProjectionBoundaryMatrix A)).toRingHom := by
  have hliteral := boundary_specialization_mem_projection_kernel
    I A hfirst G hG
  rw [RingHom.mem_ker]
  change Ideal.Quotient.mk B
    (aeval (projectiveMatrixLinearForm
      (affineChartProjectionBoundaryMatrix A))
      (rationalSpecializeFirstCoordinate 0 G)) = 0
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  have hliteral' :
      aeval (projectiveMatrixLinearForm
        (affineChartProjectionBoundaryMatrix A))
        (rationalSpecializeFirstCoordinate 0 G) ∈ projectiveBoundaryIdeal I := by
    rw [RingHom.mem_ker] at hliteral
    exact Ideal.Quotient.eq_zero_iff_mem.mp hliteral
  exact hIB hliteral'

/-- The source equation specializes to a nonzero scalar multiple of the
equation of a same-degree birational projection of a saturated boundary. -/
theorem boundary_specialization_eq_const_mul_of_saturatedProjection
    {N r degree : ℕ}
    (I : Ideal (MvPolynomial (Fin (N + 2)) ℚ))
    (B : Ideal (MvPolynomial (Fin (N + 1)) ℚ))
    (hIB : projectiveBoundaryIdeal I ≤ B)
    (hI : I.IsPrime)
    (hX : X (0 : Fin (N + 2)) ∉ I)
    (A : Matrix (Fin (r + 3)) (Fin (N + 2)) ℤ)
    (G : MvPolynomial (Fin (r + 3)) ℚ)
    (hsource : IsAffineChartFiniteBirationalLinearProjection
      (degree := degree) I hI A G)
    (hBprime : B.IsPrime)
    (H : MvPolynomial (Fin (r + 2)) ℚ)
    (hboundary : IsHomogeneousFiniteBirationalLinearProjection
      (degree := degree) B hBprime
      (affineChartProjectionBoundaryMatrix
        (A.map (Int.castRingHom ℚ))) H) :
    ∃ c : ℚ, c ≠ 0 ∧
      rationalSpecializeFirstCoordinate 0 G = C c * H := by
  have hGmem : G ∈ RingHom.ker
      (projectiveMatrixCoordinateMap I
        (A.map (Int.castRingHom ℚ))).toRingHom := by
    rw [hsource.2.2.2.1]
    exact Ideal.mem_span_singleton_self G
  have hGboundaryMem :=
    boundary_specialization_mem_saturatedProjection_kernel
      I B hIB (A.map (Int.castRingHom ℚ)) hsource.1 G hGmem
  have hdiv : H ∣ rationalSpecializeFirstCoordinate 0 G := by
    rw [hboundary.2.2.1] at hGboundaryMem
    exact Ideal.mem_span_singleton.mp hGboundaryMem
  have hGboundary : rationalSpecializeFirstCoordinate 0 G ≠ 0 :=
    rationalSpecializeFirstCoordinate_zero_ne_of_affineChartProjection
      I hI hX A G hsource
  have hGboundaryHom :
      (rationalSpecializeFirstCoordinate 0 G).IsHomogeneous degree := by
    simpa [rationalSpecializeFirstCoordinate, restrictFirstPolynomialToZero]
      using restrictFirstPolynomialToZero_isHomogeneous hsource.2.2.2.2.1
  exact eq_scalar_mul_of_homogeneous_dvd_same_degree
    hGboundary hboundary.2.2.2.2.1.ne_zero hGboundaryHom
      hboundary.2.2.2.1 hdiv

/-- A geometrically prime saturated boundary makes the leading form of the
cleared affine image equation absolutely irreducible. -/
theorem integralAffineProjectionTopPart_absolutelyIrreducible_of_saturatedBoundaryProjection
    {N r degree : ℕ}
    (I : Ideal (MvPolynomial (Fin (N + 2)) ℚ))
    (B : Ideal (MvPolynomial (Fin (N + 1)) ℚ))
    (hIB : projectiveBoundaryIdeal I ≤ B)
    (hI : I.IsPrime)
    (hX : X (0 : Fin (N + 2)) ∉ I)
    (A : Matrix (Fin (r + 3)) (Fin (N + 2)) ℤ)
    (G : MvPolynomial (Fin (r + 3)) ℚ)
    (hsource : IsAffineChartFiniteBirationalLinearProjection
      (degree := degree) I hI A G)
    (hBprime : B.IsPrime)
    (hBgeometric : GeometricallyPrimeMvPolynomialIdeal B)
    (H : MvPolynomial (Fin (r + 2)) ℚ)
    (hboundary : IsHomogeneousFiniteBirationalLinearProjection
      (degree := degree) B hBprime
      (affineChartProjectionBoundaryMatrix
        (A.map (Int.castRingHom ℚ))) H) :
    IsAbsolutelyIrreducible
      (integralAffineProjectionTopPart
        (A.map (Int.castRingHom ℚ)) G degree) := by
  obtain ⟨c, hc, hspecialize⟩ :=
    boundary_specialization_eq_const_mul_of_saturatedProjection
      I B hIB hI hX A G hsource hBprime H hboundary
  have hHabsolute : IsAbsolutelyIrreducible H := by
    apply absolutelyIrreducible_of_ker_eq_span_of_geometricallyPrime
      B hBgeometric
      (projectiveMatrixCoordinateMap B
        (affineChartProjectionBoundaryMatrix
          (A.map (Int.castRingHom ℚ))))
      H hboundary.2.2.2.2.1.ne_zero
    exact hboundary.2.2.1
  apply integralAffineProjectionTopPart_absolutelyIrreducible_of_boundary
    (A.map (Int.castRingHom ℚ)) hsource.2.2.2.2.1
  rw [hspecialize]
  exact hHabsolute.const_mul c hc

end

end TranslatedDepthSeven
