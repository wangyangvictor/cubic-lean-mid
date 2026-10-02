import CubicTenVariables.DegreeSpanGoodReduction
import TranslatedDepthSeven.ProjectiveBertiniGenericSectionConstruction

/-!
The two degree--span applications needed in ten variables, with the
degree--span premise supplied by the internally constructed generic
integral sections. The dimensions, degrees, and geometric primality in
these statements refer to the actual homogeneous polynomial ideals.
-/

set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.DegreeSpanEightPlaneProved

open MvPolynomial Matrix Module TranslatedDepthSeven
open DegreeSpanEightPlane IntegralModelDimension
attribute [local instance] MvPolynomial.gradedAlgebra

/-- A geometrically integral affine cone of dimension six and degree at
most three is contained in an eight-dimensional rational linear space. -/
theorem exists_integral_rows_dim_six
    (I : Ideal (MvPolynomial (Fin 10) ℚ)) (d : ℕ)
    (hprime : I.IsPrime)
    (hgeometric : (I.map (map (algebraMap ℚ (AlgebraicClosure ℚ)))).IsPrime)
    (hhom : I.IsHomogeneous (homogeneousSubmodule (Fin 10) ℚ))
    (hdegree : Published.HasProjectiveDimensionDegree I 5 d) (hd : d ≤ 3) :
    ∃ A : Matrix (Fin 2) (Fin 10) ℤ,
      (A.map (Int.castRingHom ℚ)).rank = 2 ∧
      finrank ℚ (LinearMap.ker (A.map (Int.castRingHom ℚ)).mulVecLin) = 8 ∧
      ∀ j, map (Int.castRingHom ℚ) (rowPolynomial A j) ∈ I :=
  DegreeSpanEightPlane.exists_integral_rows_dim_six
    rationalProjectiveDegreeSpan_internal I d hprime hgeometric hhom hdegree hd

/-- A geometrically integral affine cone of dimension five and degree at
most four is contained in an eight-dimensional rational linear space. -/
theorem exists_integral_rows_dim_five
    (I : Ideal (MvPolynomial (Fin 10) ℚ)) (d : ℕ)
    (hprime : I.IsPrime)
    (hgeometric : (I.map (map (algebraMap ℚ (AlgebraicClosure ℚ)))).IsPrime)
    (hhom : I.IsHomogeneous (homogeneousSubmodule (Fin 10) ℚ))
    (hdegree : Published.HasProjectiveDimensionDegree I 4 d) (hd : d ≤ 4) :
    ∃ A : Matrix (Fin 2) (Fin 10) ℤ,
      (A.map (Int.castRingHom ℚ)).rank = 2 ∧
      finrank ℚ (LinearMap.ker (A.map (Int.castRingHom ℚ)).mulVecLin) = 8 ∧
      ∀ j, map (Int.castRingHom ℚ) (rowPolynomial A j) ∈ I :=
  DegreeSpanEightPlane.exists_integral_rows_dim_five
    rationalProjectiveDegreeSpan_internal I d hprime hgeometric hhom hdegree hd

/-- The same fixed integral plane contains the reductions of a given
equation model over every field outside one fixed finite set of primes. -/
theorem exists_plane {t : ℕ}
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
        (A.map (Int.castRingHom K)).mulVec x = 0 :=
  DegreeSpanGoodReduction.exists_plane rationalProjectiveDegreeSpan_internal
    G r d hprime hgeometric hhom hdegree hsmall

end CubicTenVariables.DegreeSpanEightPlaneProved
