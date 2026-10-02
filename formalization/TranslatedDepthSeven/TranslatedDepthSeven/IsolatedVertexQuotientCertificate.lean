import TranslatedDepthSeven.IsolatedVertexQuotientTangentPacket
import TranslatedDepthSeven.AffineTransformBounds
import TranslatedDepthSeven.DepthSevenRankSevenPacketAssembly

/-!
# Integral certificates for the isolated-vertex quotient

The lower homogeneous equation family is fixed after the vertex coordinate
is removed.  For a translated normalized problem its literal equations are
obtained by the scalar affine substitution `x = b + m z`.  This file bounds
the support, degree, coefficients, and one nonzero `7 × 7` Jacobian minor of
that displayed family.  Every bound is an explicit polynomial expression;
no effective-height or component theorem is used.
-/

namespace TranslatedDepthSeven

noncomputable section

set_option maxHeartbeats 1000000

/-- The lower coordinates of the transformed base point have the expected
fixed-matrix height bound. -/
theorem dropFirst_pointEquiv_coordinate_natAbs_le
    (U : IntegralUnimodularChange 13) (x₀ : IntVector 13) (i : Fin 12) :
    (dropFirstIntVector (U.pointEquiv x₀) i).natAbs ≤
      integralMatrixL1Norm U.forward * depthSevenProjectionBaseHeight x₀ := by
  apply matrix_mulVec_natAbs_le_integralMatrixL1Norm_mul
  intro j
  exact coordinate_le_depthSevenProjectionBaseHeight x₀ j

/-- Literal translated quotient equation family. -/
def isolatedVertexQuotientAffineEquationFinset
    (U : IntegralUnimodularChange 13) (p : Parameters)
    (x₀ : IntVector 13)
    (lowerEquations : Finset (MvPolynomial (Fin 12) ℤ)) :
    Finset (MvPolynomial (Fin 12) ℤ) :=
  integralAffineTransformEquationFinset
    (dropFirstIntVector (U.pointEquiv x₀)) p.m lowerEquations

/-- Uniform support bound after the literal quotient substitution. -/
theorem quotientAffineEquation_support_card_le
    (U : IntegralUnimodularChange 13) (p : Parameters)
    (x₀ : IntVector 13)
    (lowerEquations : Finset (MvPolynomial (Fin 12) ℤ))
    {g : MvPolynomial (Fin 12) ℤ}
    (hg : g ∈ isolatedVertexQuotientAffineEquationFinset
      U p x₀ lowerEquations) :
    g.support.card ≤
      (equationFamilyDegreeBound lowerEquations + 1) *
        (equationFamilySupportBound lowerEquations *
          2 ^ equationFamilyDegreeBound lowerEquations) := by
  obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp hg
  have hraw := integralAffineTransform_support_card_le
    (dropFirstIntVector (U.pointEquiv x₀)) p.m f
    (totalDegree_le_equationFamilyDegreeBound hf)
  exact hraw.trans (by
    gcongr
    exact support_card_le_equationFamilySupportBound hf)

/-- Uniform degree bound after the literal quotient substitution. -/
theorem quotientAffineEquation_totalDegree_le
    (U : IntegralUnimodularChange 13) (p : Parameters)
    (x₀ : IntVector 13)
    (lowerEquations : Finset (MvPolynomial (Fin 12) ℤ))
    {g : MvPolynomial (Fin 12) ℤ}
    (hg : g ∈ isolatedVertexQuotientAffineEquationFinset
      U p x₀ lowerEquations) :
    g.totalDegree ≤ equationFamilyDegreeBound lowerEquations := by
  obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp hg
  rw [totalDegree_integralAffineTransform p.hm]
  exact totalDegree_le_equationFamilyDegreeBound hf

/-- Uniform coefficient bound after the literal quotient substitution. -/
theorem quotientAffineEquation_coeff_natAbs_le
    (U : IntegralUnimodularChange 13) (p : Parameters)
    (x₀ : IntVector 13)
    (lowerEquations : Finset (MvPolynomial (Fin 12) ℤ))
    {g : MvPolynomial (Fin 12) ℤ}
    (hg : g ∈ isolatedVertexQuotientAffineEquationFinset
      U p x₀ lowerEquations) (mu : Fin 12 →₀ ℕ) :
    (g.coeff mu).natAbs ≤
      (equationFamilyDegreeBound lowerEquations + 1) *
        (equationFamilySupportBound lowerEquations *
          equationFamilyCoefficientBound lowerEquations *
          (2 * max 1
            (integralMatrixL1Norm U.forward *
              depthSevenProjectionBaseHeight x₀)) ^
                equationFamilyDegreeBound lowerEquations) *
        max 1 p.m ^ equationFamilyDegreeBound lowerEquations := by
  obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp hg
  have hraw := integralAffineTransform_coeff_natAbs_le
    (d := equationFamilyDegreeBound lowerEquations)
    (C := equationFamilyCoefficientBound lowerEquations)
    (H := integralMatrixL1Norm U.forward *
      depthSevenProjectionBaseHeight x₀)
    (dropFirstIntVector (U.pointEquiv x₀)) p.m f
    (fun mu hmu ↦ coeff_natAbs_le_equationFamilyCoefficientBound hf hmu)
    (totalDegree_le_equationFamilyDegreeBound hf)
    (dropFirst_pointEquiv_coordinate_natAbs_le U x₀) mu
  exact hraw.trans (by
    gcongr
    exact support_card_le_equationFamilySupportBound hf)

/-- The smooth quotient point supplies one nonzero minor whose height is
bounded directly by the fixed lower family and the displayed translated
parameters. -/
theorem exists_quotientAffineEquation_bounded_nonzero_jacobianMinor
    (U : IntegralUnimodularChange 13) (p : Parameters)
    (x₀ : IntVector 13)
    (lowerEquations : Finset (MvPolynomial (Fin 12) ℤ))
    (w : IntVector 12)
    (hregular : IsQuotientJacobianRegularAt
      (isolatedVertexQuotientAffineEquationFinset U p x₀ lowerEquations) w)
    (hw : ∀ i, (w i).natAbs ≤ isolatedVertexTransformedNaturalSide U p) :
    ∃ rows : Fin 7 → Fin
        (isolatedVertexQuotientAffineEquationFinset U p x₀ lowerEquations).card,
      ∃ cols : Fin 7 → Fin 12,
        Function.Injective rows ∧ Function.Injective cols ∧
        integralJacobianMinor
          (indexedFinsetFamily
            (isolatedVertexQuotientAffineEquationFinset
              U p x₀ lowerEquations)) w rows cols ≠ 0 ∧
        (integralJacobianMinor
          (indexedFinsetFamily
            (isolatedVertexQuotientAffineEquationFinset
              U p x₀ lowerEquations)) w rows cols).natAbs ≤
          Nat.factorial 7 *
            (((equationFamilyDegreeBound lowerEquations + 1) *
                (equationFamilySupportBound lowerEquations *
                  2 ^ equationFamilyDegreeBound lowerEquations)) *
              equationFamilyDegreeBound lowerEquations *
              ((equationFamilyDegreeBound lowerEquations + 1) *
                (equationFamilySupportBound lowerEquations *
                  equationFamilyCoefficientBound lowerEquations *
                  (2 * max 1
                    (integralMatrixL1Norm U.forward *
                      depthSevenProjectionBaseHeight x₀)) ^
                        equationFamilyDegreeBound lowerEquations) *
                max 1 p.m ^ equationFamilyDegreeBound lowerEquations) *
              max 1 (isolatedVertexTransformedNaturalSide U p) ^
                equationFamilyDegreeBound lowerEquations) ^ 7 := by
  classical
  let equationsT :=
    isolatedVertexQuotientAffineEquationFinset U p x₀ lowerEquations
  let S := (equationFamilyDegreeBound lowerEquations + 1) *
    (equationFamilySupportBound lowerEquations *
      2 ^ equationFamilyDegreeBound lowerEquations)
  let d := equationFamilyDegreeBound lowerEquations
  let C := (equationFamilyDegreeBound lowerEquations + 1) *
    (equationFamilySupportBound lowerEquations *
      equationFamilyCoefficientBound lowerEquations *
      (2 * max 1 (integralMatrixL1Norm U.forward *
        depthSevenProjectionBaseHeight x₀)) ^
          equationFamilyDegreeBound lowerEquations) *
    max 1 p.m ^ equationFamilyDegreeBound lowerEquations
  apply exists_bounded_nonzero_integralJacobianMinor_of_polynomial_bounds
    (indexedFinsetFamily equationsT) w hregular
  · intro i
    exact quotientAffineEquation_support_card_le U p x₀ lowerEquations
      (equationsT.equivFin.symm i).2
  · intro i mu _hmu
    exact quotientAffineEquation_coeff_natAbs_le U p x₀ lowerEquations
      (equationsT.equivFin.symm i).2 mu
  · intro i
    exact quotientAffineEquation_totalDegree_le U p x₀ lowerEquations
      (equationsT.equivFin.symm i).2
  · exact hw

end

end TranslatedDepthSeven
