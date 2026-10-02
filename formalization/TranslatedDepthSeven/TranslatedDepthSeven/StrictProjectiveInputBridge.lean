import TranslatedDepthSeven.StrictRootTheorem
import TranslatedDepthSeven.GenericJacobianMinor
import TranslatedDepthSeven.FixedConeResidueCount

/-!
# Literal consequences of the strict projective input

The strict root hypothesis already contains homogeneity, saturation,
primality, affine-cone dimension six, and positive degree.  This file merely
projects those conjuncts and combines the dimension statement with the
generic conormal calculation to select an actual Jacobian chart.
-/

namespace TranslatedDepthSeven

noncomputable section

open Published

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The strict projective fivefold hypothesis gives a homogeneous prime
affine cone of Krull dimension six and positive degree. -/
theorem strictProjectiveInput_consequences
    (equations : Finset (MvPolynomial (Fin 13) ℤ)) (degree : ℕ)
    (h : IsIntegralProjectiveVariety
      (N := 12) (rationalDepthSevenEquationIdeal equations) 5 degree) :
    (rationalDepthSevenEquationIdeal equations).IsHomogeneous
        (MvPolynomial.homogeneousSubmodule (Fin 13) ℚ) ∧
      IsSaturatedByProjectiveIrrelevantIdeal
        (rationalDepthSevenEquationIdeal equations) ∧
      (rationalDepthSevenEquationIdeal equations).IsPrime ∧
      ringKrullDim
          (MvPolynomial (Fin 13) ℚ ⧸
            rationalDepthSevenEquationIdeal equations) = 6 ∧
      0 < degree := by
  exact ⟨h.1, h.2.1, h.2.2.1, by simpa using h.2.2.2.1,
    h.2.2.2.2.1⟩

/-- A projective fivefold presented by the displayed rationalized equation
family has a literal `7 × 7` Jacobian minor which is nonzero at its generic
point. -/
theorem exists_rationalizedDepthSevenJacobianChart_of_strictProjectiveInput
    (equations : Finset (MvPolynomial (Fin 13) ℤ)) (degree : ℕ)
    (h : IsIntegralProjectiveVariety
      (N := 12) (rationalDepthSevenEquationIdeal equations) 5 degree) :
    ∃ C : DepthSevenJacobianChartIndex
        (rationalizedEquationFinset equations),
      C.determinant ∉ rationalDepthSevenEquationIdeal equations := by
  have hdata := strictProjectiveInput_consequences equations degree h
  apply
    exists_depthSevenJacobianChart_determinant_notMem_of_prime_dimension_six
      (rationalizedEquationFinset equations)
      (rationalDepthSevenEquationIdeal equations)
      hdata.2.2.1
  · rfl
  · exact hdata.2.2.2.1

/-- The strict projective hypothesis supplies the literal vertical finite
normalization model used for every square-free residue count.  This is only
an instantiation of the internally proved normalization theorem: the model,
its denominator, and its local constant are chosen from the fixed displayed
equations before any translated box or modulus is introduced. -/
theorem nonempty_fixedFivefoldResidueModel_of_strictProjectiveInput
    (equations : Finset (MvPolynomial (Fin 13) ℤ)) (degree : ℕ)
    (h : IsIntegralProjectiveVariety
      (N := 12) (rationalDepthSevenEquationIdeal equations) 5 degree) :
    Nonempty (FixedFivefoldResidueModel
      (indexedFinsetFamily (rationalizedEquationFinset equations))) := by
  apply nonempty_fixedFivefoldResidueModel_finiteEquationIdeal
    (rationalizedEquationFinset equations) degree
  simpa [rationalDepthSevenEquationIdeal] using h

end

end TranslatedDepthSeven
