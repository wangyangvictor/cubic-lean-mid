import TranslatedDepthSeven.IsolatedVertexQuotientLiteralExceptionalLift

/-!
# Literal quotient points and their node components

This file proves that an actual integral quotient packet point lies on an
actual minimal-prime component of the displayed quotient node.  All
coordinate and ideal identities are proved directly; no component geometry
or point-count estimate is assumed.
-/

namespace TranslatedDepthSeven

noncomputable section

open Matrix MvPolynomial

set_option maxHeartbeats 3000000

/-- An integral common zero of the lower equation family lies on its
literal geometric ideal after coefficient extension. -/
theorem integralCommonZero_mem_geometricIsolatedVertexLowerIdeal
    (lowerEquations : Finset (MvPolynomial (Fin 12) ℤ))
    (y : IntVector 12) (hy : IntegralCommonZero lowerEquations y) :
    qbarIntVector y ∈
      affineIdealZeroLocus
        (geometricIsolatedVertexLowerIdeal lowerEquations) := by
  change geometricIsolatedVertexLowerIdeal lowerEquations ≤
    RingHom.ker (eval (qbarIntVector y))
  rw [geometricIsolatedVertexLowerIdeal]
  rw [Ideal.map_le_iff_le_comap]
  intro f hf
  apply RingHom.mem_ker.mpr
  have hfzero : MvPolynomial.eval (fun j ↦ (y j : ℚ)) f = 0 :=
    integralPointVanishesOn_rationalizedEquationIdeal_of_commonZero
      lowerEquations y hy f hf
  calc
    MvPolynomial.eval (qbarIntVector y)
        (MvPolynomial.map (algebraMap ℚ Qbar) f) =
      algebraMap ℚ Qbar
        (MvPolynomial.eval (fun j ↦ (y j : ℚ)) f) := by
          simpa [qbarIntVector] using
            (MvPolynomial.map_eval (algebraMap ℚ Qbar)
              (fun j ↦ (y j : ℚ)) f).symm
    _ = 0 := by rw [hfzero, map_zero]

/-- A point of the affine cone base gives the standard affine-chart point
of the projective cone. -/
theorem projectiveConeIdealExtension_le_affineChart_eval
    {K : Type*} [Field K] {n : ℕ}
    (J : Ideal (MvPolynomial (Fin n) K)) (y : Fin n → K)
    (hy : y ∈ affineIdealZeroLocus J) :
    projectiveConeIdealExtension J ≤
      RingHom.ker (eval (affineChartVector y)) := by
  rw [projectiveConeIdealExtension, Ideal.map_le_iff_le_comap]
  intro f hf
  apply RingHom.mem_ker.mpr
  rw [MvPolynomial.eval_rename]
  have hcomp : affineChartVector y ∘ some = y := by
    funext i
    rfl
  rw [hcomp]
  exact RingHom.mem_ker.mp (hy f hf)

/-- The affine representative `(1,w)` lies on the translated cone whenever
`b+m*w` lies on the base. -/
theorem translatedProjectiveConeIdeal_le_affineQuotientPoint_eval
    {K : Type*} [Field K] {n : ℕ}
    (J : Ideal (MvPolynomial (Fin n) K))
    (b w : Fin n → K) (m : K) (hm : m ≠ 0)
    (hy : (fun j ↦ b j + m * w j) ∈ affineIdealZeroLocus J) :
    translatedProjectiveConeIdeal b m hm J ≤
      RingHom.ker (eval (affineChartVector w)) := by
  unfold translatedProjectiveConeIdeal
  rw [Ideal.map_le_iff_le_comap]
  intro f hf
  apply RingHom.mem_ker.mpr
  change aeval (affineChartVector w)
      (homogeneousAffinePolynomialChangeAlgEquiv b m hm f) = 0
  rw [aeval_homogeneousAffinePolynomialChange]
  have hpoint :
      homogeneousAffineLinearEquiv b m hm (affineChartVector w) =
        affineChartVector (fun j ↦ b j + m * w j) := by
    exact homogeneousAffineLinearEquiv_affineChart b m hm w
  rw [hpoint]
  exact RingHom.mem_ker.mp
    (projectiveConeIdealExtension_le_affineChart_eval J _ hy hf)

/-- The coefficient-extended standard quotient point is the reindexing of
the affine-chart representative in option coordinates. -/
theorem geometricQuotientPoint_comp_finSuccEquiv_symm
    (w : IntVector 12) :
    geometricQuotientRationalHomogeneousAffinePoint w ∘
        (_root_.finSuccEquiv 12).symm =
      affineChartVector (qbarIntVector w) := by
  funext j
  cases j <;> simp [geometricQuotientRationalHomogeneousAffinePoint,
    quotientRationalHomogeneousAffinePoint, qbarIntVector,
    affineChartVector]

/-- An integral common zero of the translated lower family gives literal
membership of `(1,w)` in the reindexed geometric translated-cone ideal. -/
theorem geometricQuotientPoint_mem_isolatedVertexTranslatedConeFinIdeal
    (lowerEquations : Finset (MvPolynomial (Fin 12) ℤ))
    (b w : IntVector 12) (m : ℤ) (hm : m ≠ 0)
    (hy : IntegralCommonZero lowerEquations
      (integralQuotientAffinePoint b w m)) :
    geometricQuotientRationalHomogeneousAffinePoint w ∈
      affineIdealZeroLocus
        (isolatedVertexTranslatedConeFinIdeal
          (qbarIntVector b) (algebraMap ℚ Qbar (m : ℚ))
          (qbarIntCast_ne_zero hm)
          (geometricIsolatedVertexLowerIdeal lowerEquations)) := by
  let y := integralQuotientAffinePoint b w m
  have hybar : qbarIntVector y ∈ affineIdealZeroLocus
      (geometricIsolatedVertexLowerIdeal lowerEquations) :=
    integralCommonZero_mem_geometricIsolatedVertexLowerIdeal
      lowerEquations y hy
  have hpoint : qbarIntVector y =
      fun j ↦ qbarIntVector b j +
        algebraMap ℚ Qbar (m : ℚ) * qbarIntVector w j := by
    funext j
    simp [y, integralQuotientAffinePoint, qbarIntVector, map_add, map_mul]
  rw [hpoint] at hybar
  unfold isolatedVertexTranslatedConeFinIdeal
  change (translatedProjectiveConeIdeal
      (qbarIntVector b) (algebraMap ℚ Qbar (m : ℚ))
      (qbarIntCast_ne_zero hm)
      (geometricIsolatedVertexLowerIdeal lowerEquations)).map
        (MvPolynomial.renameEquiv Qbar
          (_root_.finSuccEquiv 12).symm) ≤
    RingHom.ker
      (eval (geometricQuotientRationalHomogeneousAffinePoint w))
  rw [Ideal.map_le_iff_le_comap]
  intro f hf
  apply RingHom.mem_ker.mpr
  rw [MvPolynomial.renameEquiv_apply, MvPolynomial.eval_rename,
    geometricQuotientPoint_comp_finSuccEquiv_symm]
  exact RingHom.mem_ker.mp
    (translatedProjectiveConeIdeal_le_affineQuotientPoint_eval
      (geometricIsolatedVertexLowerIdeal lowerEquations)
      (qbarIntVector b) (qbarIntVector w)
      (algebraMap ℚ Qbar (m : ℚ)) (qbarIntCast_ne_zero hm)
      hybar hf)

/-- A packet point satisfies the coefficient-extended row equations of its
literal integral packet plane. -/
theorem integralPacketPlane_geometricMatrix_mulVec_eq_zero
    {Z : Finset (IntVector 12)} {q R : ℕ}
    {rho : Fin 12 → ZMod q}
    (plane : IntegralIsolatedVertexQuotientPacketPlane Z q R rho)
    (w : IntVector 12) (hw : w ∈ integralResiduePacket Z rho) :
    Matrix.mulVec (qbarIntMatrix plane.matrix)
      (geometricQuotientRationalHomogeneousAffinePoint w) = 0 := by
  have hwQ := plane.packet_mem w hw
  funext i
  have hi := congrFun hwQ i
  simpa [qbarIntMatrix, geometricQuotientRationalHomogeneousAffinePoint,
    Matrix.mulVec, dotProduct] using
      congrArg (algebraMap ℚ Qbar) hi

/-- Every literal packet point which satisfies the translated lower
equations lies on an actual minimal-prime component of the displayed node,
and the chosen component retains that point. -/
theorem exists_integralQuotientNodeComponent_through_packetPoint
    (lowerEquations : Finset (MvPolynomial (Fin 12) ℤ))
    (b : IntVector 12) (m : ℤ) (hm : m ≠ 0)
    {Z : Finset (IntVector 12)} {q R : ℕ}
    {rho : Fin 12 → ZMod q}
    (plane : IntegralIsolatedVertexQuotientPacketPlane Z q R rho)
    (w : IntVector 12) (hw : w ∈ integralResiduePacket Z rho)
    (hy : IntegralCommonZero lowerEquations
      (integralQuotientAffinePoint b w m)) :
    ∃ P : Ideal (MvPolynomial (Fin 13) Qbar),
      P ∈ integralIsolatedVertexQuotientNodeComponents
        lowerEquations b m hm plane.matrix ∧
      geometricQuotientRationalHomogeneousAffinePoint w ∈
        affineIdealZeroLocus P := by
  let point := geometricQuotientRationalHomogeneousAffinePoint w
  let node := isolatedVertexQuotientNodeIdeal
    (geometricIsolatedVertexLowerIdeal lowerEquations)
    (qbarIntVector b) (algebraMap ℚ Qbar (m : ℚ))
    (qbarIntCast_ne_zero hm) (qbarIntMatrix plane.matrix)
  have hcone : isolatedVertexTranslatedConeFinIdeal
      (qbarIntVector b) (algebraMap ℚ Qbar (m : ℚ))
      (qbarIntCast_ne_zero hm)
      (geometricIsolatedVertexLowerIdeal lowerEquations) ≤
        RingHom.ker (eval point) :=
    geometricQuotientPoint_mem_isolatedVertexTranslatedConeFinIdeal
      lowerEquations b w m hm hy
  have hrows : matrixRowLinearIdeal (qbarIntMatrix plane.matrix) ≤
      RingHom.ker (eval point) :=
    (matrixRowLinearIdeal_le_evaluationKernel_iff
      (qbarIntMatrix plane.matrix) point).mpr
        (integralPacketPlane_geometricMatrix_mulVec_eq_zero plane w hw)
  have hnode : node ≤ RingHom.ker (eval point) := by
    exact sup_le hcone hrows
  letI : (RingHom.ker (eval point)).IsPrime := RingHom.ker_isPrime _
  obtain ⟨P, hP, hPle⟩ := exists_finiteMinimalPrime_le hnode
  refine ⟨P, ?_, ?_⟩
  · exact (mem_finiteMinimalPrimes_iff node P).mpr
      ((mem_finiteMinimalPrimes_iff node P).mp hP)
  · exact fun f hf ↦ RingHom.mem_ker.mp (hPle hf)

end

end TranslatedDepthSeven
