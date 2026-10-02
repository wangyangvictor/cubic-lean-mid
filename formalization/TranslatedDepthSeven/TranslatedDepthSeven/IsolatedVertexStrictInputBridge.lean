import TranslatedDepthSeven.IsolatedVertexTransformedBox
import TranslatedDepthSeven.StrictProjectiveInputBridge

/-!
# The strict fivefold input in the isolated-vertex quotient

This file connects the literal equation ideal from the strict root statement
to the affine quotient reduction.  Its main elementary point is that an
integral common zero of the displayed generators vanishes on their entire
rational ideal, not merely on the generators.
-/

namespace TranslatedDepthSeven

noncomputable section

open MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra

/-- Vanishing of the displayed integral generators implies vanishing on the
whole rational ideal which they generate. -/
theorem integralPointVanishesOn_rationalizedEquationIdeal_of_commonZero
    {n : ℕ} (equations : Finset (MvPolynomial (Fin n) ℤ))
    (x : IntVector n) (hx : IntegralCommonZero equations x) :
    IntegralPointVanishesOnRationalIdeal
      (finiteEquationIdeal (rationalizedEquationFinset equations)) x := by
  let φ : MvPolynomial (Fin n) ℤ →+* MvPolynomial (Fin n) ℚ :=
    MvPolynomial.map (Int.castRingHom ℚ)
  let ev : MvPolynomial (Fin n) ℚ →+* ℚ :=
    MvPolynomial.eval (fun i ↦ (x i : ℚ))
  have hgenerators : Ideal.map φ
      (Ideal.span (equations : Set (MvPolynomial (Fin n) ℤ))) ≤
        RingHom.ker ev := by
    rw [Ideal.map_le_iff_le_comap]
    apply Ideal.span_le.2
    intro f hf
    change ev (φ f) = 0
    change MvPolynomial.eval (fun i ↦ (x i : ℚ))
      (MvPolynomial.map (Int.castRingHom ℚ) f) = 0
    rw [eval_map_intCast, hx f hf, Int.cast_zero]
  have hideal : Ideal.map φ
      (Ideal.span (equations : Set (MvPolynomial (Fin n) ℤ))) =
        finiteEquationIdeal (rationalizedEquationFinset equations) := by
    rw [finiteEquationIdeal, rationalizedEquationFinset, Ideal.map_span]
    apply congrArg Ideal.span
    ext f
    simp [φ]
  intro f hf
  have hfker : f ∈ RingHom.ker ev := by
    apply hgenerators
    rw [hideal]
    exact hf
  exact hfker

/-- Every point of the literal normalized target vanishes on the strict
rational fivefold ideal at its affine image `x₀+mz`. -/
theorem normalizedDisplacement_affineImage_vanishesOn_strictIdeal
    (p : Parameters) (x₀ : IntVector 13)
    (equations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    {z : IntVector 13}
    (hz : z ∈ depthSevenNormalizedDisplacementFinset p x₀ equations CF) :
    IntegralPointVanishesOnRationalIdeal
      (rationalDepthSevenEquationIdeal equations)
      (integralAffineMap x₀ z p.m) := by
  classical
  apply integralPointVanishesOn_rationalizedEquationIdeal_of_commonZero
  exact (Finset.mem_filter.mp hz).2.2.1

/-- The strict equation ideal may therefore be substituted directly into
the exact affine quotient reduction.  No separate point-membership
assumption remains in the conclusion. -/
theorem exists_strictIsolatedVertex_affineQuotientReduction
    (hvertexTheorem : StandardAG.ProjectiveVertexIdealTranslationStability)
    (hcylinder : StandardAG.TranslationStableHomogeneousIdealCylinderGenerators)
    (hcompletion : StandardLattice.PrimitiveDirectionUnimodularCompletion)
    (equations : Finset (MvPolynomial (Fin 13) ℤ))
    (degree : ℕ)
    (hprojective : Published.IsIntegralProjectiveVariety
      (N := 12) (rationalDepthSevenEquationIdeal equations) 5 degree)
    (h : IntVector 13) (hprimitive : PrimitiveDirection h)
    (hvertex : LiesInGeometricProjectiveVertex h
      (rationalDepthSevenEquationIdeal equations)) :
    ∃ (equationsI : Finset (MvPolynomial (Fin 13) ℤ))
        (U : IntegralUnimodularChange 13)
        (lowerHomogeneousEquations : Finset (MvPolynomial (Fin 12) ℤ)),
      Ideal.map (MvPolynomial.map (Int.castRingHom ℚ))
          (Ideal.span (equationsI : Set (MvPolynomial (Fin 13) ℤ))) =
            rationalDepthSevenEquationIdeal equations ∧
      Matrix.mulVec U.forward h = firstCoordinateIntDirection ∧
      U.transformEquationFinset equationsI =
          liftEquationFinsetAfterFirst lowerHomogeneousEquations ∧
      (∀ g ∈ lowerHomogeneousEquations, ∃ d : ℕ, g.IsHomogeneous d) ∧
      ∀ (p : Parameters) (x₀ : IntVector 13) (CF : ℕ),
        (isolatedVertexQuotientPointFinset U p x₀ equations CF ⊆
          integralCommonZeroInBox
            (M := isolatedVertexTransformedNaturalSide U p)
            (integralAffineTransformEquationFinset
              (dropFirstIntVector (U.pointEquiv x₀)) p.m
              lowerHomogeneousEquations)) ∧
        (depthSevenNormalizedDisplacementFinset p x₀ equations CF).card ≤
          (isolatedVertexQuotientPointFinset U p x₀ equations CF).card *
            (2 * isolatedVertexTransformedNaturalSide U p + 1) := by
  have hdata := strictProjectiveInput_consequences
    equations degree hprojective
  obtain ⟨equationsI, U, lowerEquations, hideal, hforward, hfamily,
      hhomLower, hreduction⟩ :=
    exists_isolatedVertex_affineQuotientReduction
      hvertexTheorem hcylinder hcompletion
      (rationalDepthSevenEquationIdeal equations) hdata.2.2.1.isRadical
      hdata.1 h hprimitive hvertex
  refine ⟨equationsI, U, lowerEquations, hideal, hforward, hfamily,
    hhomLower, ?_⟩
  intro p x₀ CF
  apply hreduction p x₀ equations CF
  intro z hz
  exact normalizedDisplacement_affineImage_vanishesOn_strictIdeal
    p x₀ equations CF hz

end

end TranslatedDepthSeven
