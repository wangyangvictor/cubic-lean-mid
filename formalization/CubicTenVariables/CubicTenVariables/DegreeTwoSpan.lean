import CubicTenVariables.DegreeTwoNormalization
import TranslatedDepthSeven.ProjectiveDegreeSpanScalarExtensionInternal

/-! The projective degree-span inequality in degree at most two, in every
rational ambient dimension. This supplies the first two ten-variable
terminal-stratum promotion cases without the general degree-span input.
Degrees three and four remain open here. -/

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 300000
set_option maxHeartbeats 4000000
noncomputable section
namespace CubicTenVariables.DegreeTwoSpan
open MvPolynomial TranslatedDepthSeven TranslatedDepthSeven.Published
attribute [local instance] MvPolynomial.gradedAlgebra

theorem degree_two {N r : ℕ}
    (I : Ideal (MvPolynomial (Fin (N+1)) ℚ))
    (hprime : I.IsPrime)
    (hgeometric : (I.map
      (MvPolynomial.map (algebraMap ℚ (AlgebraicClosure ℚ)))).IsPrime)
    (hhomogeneous : I.IsHomogeneous
      (MvPolynomial.homogeneousSubmodule (Fin (N+1)) ℚ))
    (hprojective : HasProjectiveDimensionDegree I r 2) :
    N+1 ≤ Module.finrank ℚ (StandardAG.degreeOnePartInIdeal I)+r+2 := by
  let Ibar : Ideal (MvPolynomial (Fin (N+1)) Qbar) :=
    I.map (MvPolynomial.map (algebraMap ℚ Qbar))
  have hbarPrime : Ibar.IsPrime := hgeometric
  have hbarHomogeneous : Ibar.IsHomogeneous
      (MvPolynomial.homogeneousSubmodule (Fin (N+1)) Qbar) :=
    isHomogeneous_map_mvPolynomialMap (algebraMap ℚ Qbar) I hhomogeneous
  have hbarDegree : HasProjectiveDimensionDegree Ibar r 2 :=
    qbarHasProjectiveDimensionDegree_of_rational I hprojective hbarPrime
  obtain ⟨D⟩ := exists_homogeneousLinearNormalizationData
    (N+1) Ibar hbarPrime hbarHomogeneous
  obtain ⟨hcount,hrank⟩ :=
    homogeneousLinearNormalization_genericRank_le_projectiveDegree
      Ibar hbarPrime D hbarDegree
  have hpiece := DegreeTwoNormalization.finrank_quotientHomogeneousComponent_one_le_succ_parameterCount_of_rank_le_two
      Qbar Ibar hbarPrime hbarHomogeneous D hrank
  have htransport := projectiveHilbertPiece_finrank_map_eq
    (K := ℚ) (L := Qbar) N 1 I
  change Module.finrank Qbar
      (quotientHomogeneousComponent Qbar (Fin (N+1)) Ibar 1) =
    Module.finrank ℚ (quotientHomogeneousComponent ℚ (Fin (N+1)) I 1) at htransport
  rw [htransport,hcount] at hpiece
  have hsum := finrank_degreeOnePart_add_quotientHomogeneousComponent_eq I
  omega

theorem degree_le_two {N r d : ℕ}
    (I : Ideal (MvPolynomial (Fin (N+1)) ℚ))
    (hprime : I.IsPrime)
    (hgeometric : (I.map
      (MvPolynomial.map (algebraMap ℚ (AlgebraicClosure ℚ)))).IsPrime)
    (hhomogeneous : I.IsHomogeneous
      (MvPolynomial.homogeneousSubmodule (Fin (N+1)) ℚ))
    (hprojective : HasProjectiveDimensionDegree I r d) (hd : d ≤ 2) :
    N+1 ≤ Module.finrank ℚ (StandardAG.degreeOnePartInIdeal I)+r+d := by
  have hpos : 0 < d := hprojective.2.1
  have hcases : d=1 ∨ d=2 := by omega
  rcases hcases with rfl | rfl
  · exact projectiveDegreeSpan_degree_one_internal I hprime hhomogeneous hprojective
  · exact degree_two I hprime hgeometric hhomogeneous hprojective

/-- The exact linear-equation count for (dimension, degree cap)=(7,1),(6,2). -/
theorem ten_variable_two_linear_equations {r d : ℕ}
    (I : Ideal (MvPolynomial (Fin 10) ℚ))
    (hprime : I.IsPrime)
    (hgeometric : (I.map
      (MvPolynomial.map (algebraMap ℚ (AlgebraicClosure ℚ)))).IsPrime)
    (hhomogeneous : I.IsHomogeneous
      (MvPolynomial.homogeneousSubmodule (Fin 10) ℚ))
    (hprojective : HasProjectiveDimensionDegree I r d)
    (hd : d ≤ 2) (hrd : r+d ≤ 8) :
    2 ≤ Module.finrank ℚ (StandardAG.degreeOnePartInIdeal I) := by
  have h : 10 ≤ Module.finrank ℚ (StandardAG.degreeOnePartInIdeal I)+r+d :=
    degree_le_two (N := 9) I hprime hgeometric hhomogeneous hprojective hd
  omega

end CubicTenVariables.DegreeTwoSpan
