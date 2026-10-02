import TranslatedDepthSeven.PowerSeriesFilteredGrowthInternal
import TranslatedDepthSeven.SmoothCurvePowerSeriesEmbeddingInternal
import TranslatedDepthSeven.IntegralCurveStandardSmoothChartInternal
import TranslatedDepthSeven.ProjectiveChosenNonemptyChartInternal
import TranslatedDepthSeven.ProjectiveDegreeSpanScalarExtensionInternal

/-!
# The degree--span inequality for geometrically integral curves

On a nonempty affine chart, a smooth principal localization embeds in
one-variable formal power series. The product-space inequality forces the
degree filtration to grow with slope at least `dim F₁ - 1`. Its actual
Hilbert polynomial has slope equal to the curve degree. A coordinate
permutation treats an arbitrary nonempty projective curve, and coefficient
extension descends the conclusion to geometrically integral rational curves.

This is the curve case only. No generic hyperplane-section theorem is
assumed, and the higher-dimensional degree--span inequality is not asserted.
-/

namespace TranslatedDepthSeven

noncomputable section

open MvPolynomial Published
attribute [local instance] MvPolynomial.gradedAlgebra

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 300000

theorem projectiveCurve_firstChart_hilbertOne_le_degree_add_one
    {K : Type*} [Field K] [CharZero K] [IsAlgClosed K] {N d : ℕ}
    (I : Ideal (MvPolynomial (Fin (N + 1)) K)) (hI : I.IsPrime)
    (hhom : I.IsHomogeneous (homogeneousSubmodule (Fin (N + 1)) K))
    (hX : X (0 : Fin (N + 1)) ∉ I)
    (hdegree : HasProjectiveDimensionDegree I 1 d) :
    Module.finrank K (projectiveHilbertPiece K N I 1) ≤ d + 1 := by
  let J := I.map (standardDehomogenizationHom K N)
  obtain ⟨hJ, _hdim, a, ha, hstandard, ⟨f⟩⟩ :=
    integralProjectiveCurve_firstChart_exists_standardSmooth_augmentation
      I hI hhom hX hdegree
  letI : J.IsPrime := hJ
  let A := MvPolynomial (Fin N) K ⧸ J
  let B := Localization.Away a
  have hM : Submonoid.powers a ≤ nonZeroDivisors A :=
    powers_le_nonZeroDivisors_of_noZeroDivisors ha
  letI : IsDomain B := IsLocalization.isDomain_of_le_nonZeroDivisors B hM
  letI : Algebra.IsStandardSmoothOfRelativeDimension 1 K B := hstandard
  let g : A →ₐ[K] B := IsScalarTower.toAlgHom K A B
  let h : A →ₐ[K] PowerSeries K := (smoothCurveSeriesAlgHom f).comp g
  have hh : Function.Injective h :=
    (smoothCurveSeriesAlgHom_injective f).comp (IsLocalization.injective B hM)
  obtain ⟨P, hdeg, hlc, n₀, hn₀⟩ := hdegree.2.2
  have hpoly : ∃ n₀, ∀ n ≥ n₀,
      (Module.finrank K (affineHilbertFiltration K N J n) : ℚ) = P.eval (n : ℚ) := by
    refine ⟨n₀, fun n hn ↦ ?_⟩
    rw [← finrank_projectiveHilbertPiece_eq_standardAffineChart I hhom hI hX]
    exact hn₀ n hn
  have hbound := linear_hilbert_slope_ge_filtration_first_rank_sub_one
    (fun n ↦ Module.finrank K (affineHilbertFiltration K N J n)) d P hdeg
    (by simpa using hlc) hpoly
    (affineHilbertFiltration_linear_lower_of_powerSeries_embedding J hJ h hh)
  rwa [finrank_projectiveHilbertPiece_eq_standardAffineChart I hhom hI hX]

theorem projectiveCurve_hilbertOne_le_degree_add_one
    {K : Type*} [Field K] [CharZero K] [IsAlgClosed K] {N d : ℕ}
    (I : Ideal (MvPolynomial (Fin (N + 1)) K)) (hI : I.IsPrime)
    (hhom : I.IsHomogeneous (homogeneousSubmodule (Fin (N + 1)) K))
    (hdegree : HasProjectiveDimensionDegree I 1 d) :
    Module.finrank K (projectiveHilbertPiece K N I 1) ≤ d + 1 := by
  obtain ⟨e, hI', hhom', hX', hdegree', hpieces⟩ :=
    exists_coordinatePermutation_nonemptyFirstChart I hI hhom hdegree
  rw [hpieces 1]
  exact projectiveCurve_firstChart_hilbertOne_le_degree_add_one
    _ hI' hhom' hX' hdegree'

theorem projectiveCurveDegreeSpan_of_isAlgClosed_internal
    {K : Type*} [Field K] [CharZero K] [IsAlgClosed K] {N d : ℕ}
    (I : Ideal (MvPolynomial (Fin (N + 1)) K)) (hI : I.IsPrime)
    (hhom : I.IsHomogeneous (homogeneousSubmodule (Fin (N + 1)) K))
    (hdegree : HasProjectiveDimensionDegree I 1 d) :
    N + 1 ≤ Module.finrank K (StandardAG.degreeOnePartInIdeal I) + 1 + d := by
  have hbound := projectiveCurve_hilbertOne_le_degree_add_one I hI hhom hdegree
  have hsum := finrank_degreeOnePart_add_quotientHomogeneousComponent_eq I
  change Module.finrank K (quotientHomogeneousComponent K (Fin (N + 1)) I 1) ≤
    d + 1 at hbound
  omega

theorem rationalProjectiveCurveDegreeSpan_internal
    {N d : ℕ} (I : Ideal (MvPolynomial (Fin (N + 1)) ℚ))
    (hI : I.IsPrime)
    (hgeometric : (I.map
      (MvPolynomial.map (algebraMap ℚ (AlgebraicClosure ℚ)))).IsPrime)
    (hhom : I.IsHomogeneous (homogeneousSubmodule (Fin (N + 1)) ℚ))
    (hdegree : HasProjectiveDimensionDegree I 1 d) :
    N + 1 ≤ Module.finrank ℚ (StandardAG.degreeOnePartInIdeal I) + 1 + d := by
  apply projectiveDegreeSpan_descends_coefficientExtension (L := Qbar)
  exact projectiveCurveDegreeSpan_of_isAlgClosed_internal _ hgeometric
    (isHomogeneous_map_mvPolynomialMap (algebraMap ℚ Qbar) I hhom)
    (qbarHasProjectiveDimensionDegree_of_rational I hdegree hgeometric)

end

end TranslatedDepthSeven
