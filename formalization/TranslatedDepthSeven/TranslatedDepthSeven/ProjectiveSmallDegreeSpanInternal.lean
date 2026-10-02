import TranslatedDepthSeven.HomogeneousNormalizationDegreeBoundInternal
import TranslatedDepthSeven.ProjectiveDegreeTwoSpanInternal
import TranslatedDepthSeven.StrictRankAtMostSixStandardAG

/-!
# Internally proved small-degree cases of the degree--span inequality

Degree one works in every ambient dimension, without geometric integrality.
The quadratic calculation already proved in thirteen coordinates works in
every projective dimension, not only the fourfold case in its old wrapper.
These are exact cases of the standard degree--span statement; the general
inequality for degree at least three is not assumed or proved here.
-/

namespace TranslatedDepthSeven

noncomputable section

open MvPolynomial Published

attribute [local instance] MvPolynomial.gradedAlgebra

set_option synthInstance.maxHeartbeats 300000
set_option maxHeartbeats 4000000

/-- The literal degree--span inequality for rational degree-one varieties.
Geometric primality is not needed in this case. -/
theorem projectiveDegreeSpan_degree_one_internal
    {N r : ℕ} (I : Ideal (MvPolynomial (Fin (N + 1)) ℚ))
    (hprime : I.IsPrime)
    (hhomogeneous : I.IsHomogeneous
      (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) ℚ))
    (hprojective : HasProjectiveDimensionDegree I r 1) :
    N + 1 ≤ Module.finrank ℚ (StandardAG.degreeOnePartInIdeal I) + r + 1 := by
  obtain ⟨D⟩ := exists_homogeneousLinearNormalizationData
    (N + 1) I hprime hhomogeneous
  obtain ⟨hcount, hsurjective⟩ :=
    homogeneousLinearNormalization_surjective_of_projective_degree_one
      I hprime D hprojective
  have hlinear := finrank_rationalLinearFormsInIdeal_ge_of_normalization_surjective
    I hhomogeneous D hsurjective
  rw [hcount, finrank_rationalLinearFormsInIdeal_eq_degreeOnePart I] at hlinear
  omega

/-- The quadratic degree--span inequality in the literal thirteen-coordinate
ambient space, for any projective dimension.  The algebraic-closure prime
hypothesis is retained and is essential. -/
theorem projectiveDegreeSpan_degree_two_thirteen_internal
    {r : ℕ} (I : Ideal (MvPolynomial (Fin 13) ℚ))
    (hprime : I.IsPrime)
    (hgeometric : (I.map
      (MvPolynomial.map (algebraMap ℚ (AlgebraicClosure ℚ)))).IsPrime)
    (hhomogeneous : I.IsHomogeneous
      (MvPolynomial.homogeneousSubmodule (Fin 13) ℚ))
    (hprojective : HasProjectiveDimensionDegree I r 2) :
    13 ≤ Module.finrank ℚ (StandardAG.degreeOnePartInIdeal I) + r + 2 := by
  let Ibar : Ideal (MvPolynomial (Fin 13) Qbar) :=
    I.map (MvPolynomial.map (algebraMap ℚ Qbar))
  have hbarPrime : Ibar.IsPrime := hgeometric
  have hbarHomogeneous : Ibar.IsHomogeneous
      (MvPolynomial.homogeneousSubmodule (Fin 13) Qbar) :=
    isHomogeneous_map_mvPolynomialMap (algebraMap ℚ Qbar) I hhomogeneous
  have hbarDegree : HasProjectiveDimensionDegree Ibar r 2 :=
    qbarHasProjectiveDimensionDegree_of_rational I hprojective hbarPrime
  obtain ⟨D⟩ := exists_homogeneousLinearNormalizationData
    13 Ibar hbarPrime hbarHomogeneous
  obtain ⟨hcount, hrank⟩ :=
    homogeneousLinearNormalization_genericRank_le_projectiveDegree
      Ibar hbarPrime D hbarDegree
  have hpiece :=
    finrank_quotientHomogeneousComponent_one_le_succ_parameterCount_of_rank_le_two
      Qbar Ibar hbarPrime hbarHomogeneous D hrank
  have htransport := projectiveHilbertPiece_finrank_map_eq
    (K := ℚ) (L := Qbar) 12 1 I
  change Module.finrank Qbar
      (quotientHomogeneousComponent Qbar (Fin 13) Ibar 1) =
    Module.finrank ℚ (quotientHomogeneousComponent ℚ (Fin 13) I 1) at htransport
  rw [htransport, hcount] at hpiece
  have hsum := finrank_rationalLinearFormsInIdeal_add_quotientDegreeOne_eq I
  rw [finrank_rationalLinearFormsInIdeal_eq_degreeOnePart I] at hsum
  omega

/-- Both small-degree cases combined, including exclusion of degree zero by
the actual Hilbert-degree certificate. -/
theorem projectiveDegreeSpan_degree_le_two_thirteen_internal
    {r d : ℕ} (I : Ideal (MvPolynomial (Fin 13) ℚ))
    (hprime : I.IsPrime)
    (hgeometric : (I.map
      (MvPolynomial.map (algebraMap ℚ (AlgebraicClosure ℚ)))).IsPrime)
    (hhomogeneous : I.IsHomogeneous
      (MvPolynomial.homogeneousSubmodule (Fin 13) ℚ))
    (hprojective : HasProjectiveDimensionDegree I r d)
    (hsmall : d ≤ 2) :
    13 ≤ Module.finrank ℚ (StandardAG.degreeOnePartInIdeal I) + r + d := by
  have hdpos : 0 < d := hprojective.2.1
  have hd : d = 1 ∨ d = 2 := by omega
  rcases hd with rfl | rfl
  · exact projectiveDegreeSpan_degree_one_internal I hprime hhomogeneous hprojective
  · exact projectiveDegreeSpan_degree_two_thirteen_internal
      I hprime hgeometric hhomogeneous hprojective

end

end TranslatedDepthSeven
