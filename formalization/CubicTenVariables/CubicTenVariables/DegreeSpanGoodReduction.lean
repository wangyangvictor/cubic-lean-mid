import CubicTenVariables.DegreeSpanEightPlane
import CubicTenVariables.DegreeSpanReduction
import CubicTenVariables.IntegralModelDimension

/-! The degree--span plane contains the actual reductions of a fixed
integral equation model outside one fixed finite set of characteristics.
The only unproved geometric input is the explicit Harris degree--span
inequality; clearing all equation-membership denominators is proved. -/

set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.DegreeSpanGoodReduction

open MvPolynomial Matrix Module TranslatedDepthSeven
open IntegralModelDimension DegreeSpanEightPlane
attribute [local instance] MvPolynomial.gradedAlgebra

/-- A geometrically integral homogeneous ten-variable integral model
with projective dimension plus degree at most eight lies in one fixed
rational eight-plane. Its actual reductions satisfy that plane's integral
equations over every field of every characteristic outside a fixed integer.
The integer and the plane are chosen before the field or the point. -/
theorem exists_plane {t : ℕ}
    (degreeSpan : StandardAG.ProjectiveDegreeSpanInequality ℚ)
    (G : Fin t → MvPolynomial (Fin 10) ℤ) (r d : ℕ)
    (hprime : (rationalIdeal G).IsPrime)
    (hgeometric : ((rationalIdeal G).map
      (map (algebraMap ℚ (AlgebraicClosure ℚ)))).IsPrime)
    (hhom : (rationalIdeal G).IsHomogeneous (homogeneousSubmodule (Fin 10) ℚ))
    (hdegree : Published.HasProjectiveDimensionDegree (rationalIdeal G) r d)
    (hsmall : r + d ≤ 8) :
    ∃ (A : Matrix (Fin 2) (Fin 10) ℤ) (D : ℕ),
      1 ≤ D ∧ (A.map (Int.castRingHom ℚ)).rank = 2 ∧
      finrank ℚ (LinearMap.ker (A.map (Int.castRingHom ℚ)).mulVecLin) = 8 ∧
      ∀ p : ℕ, ¬ p ∣ D → ∀ (K : Type*) [Field K] [CharP K p]
        (x : Fin 10 → K),
        (∀ i, eval x (map (Int.castRingHom K) (G i)) = 0) →
        (A.map (Int.castRingHom K)).mulVec x = 0 := by
  obtain ⟨A, hArank, hAdim, hrows⟩ := exists_integral_rows degreeSpan
    (rationalIdeal G) r d hprime hgeometric hhom hdegree hsmall
  obtain ⟨D, hD, hreduce⟩ := DegreeSpanReduction.exists_uniform_family_reduction
    G (rowPolynomial A) hrows
  refine ⟨A, D, hD, hArank, hAdim, ?_⟩
  intro p hp K _ _ x hx
  ext j
  simpa only [map_rowPolynomial, eval_rowPolynomial, Pi.zero_apply] using
    hreduce p hp K x hx j

end CubicTenVariables.DegreeSpanGoodReduction
