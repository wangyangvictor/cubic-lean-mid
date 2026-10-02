import TranslatedDepthSeven.RankSevenPersistentSurfaceSmoothDevissage
import TranslatedDepthSeven.GeometricPrimeness

/-!
# Geometric integrality at a smooth rational point

Marmon's Proposition 6.2 and CCDN's Proposition 4.3.1 are statements for
geometrically integral varieties. Rational primality alone is not their
hypothesis. Stacks, Lemma 33.25.10 (tag 0CDW), gives precisely the needed
test: an integral variety with a smooth rational point is geometrically
integral. Thus every rational point of a non-geometrically-integral
component belongs to its ordinary nonsmooth locus.

The textbook theorem is an explicit input below, not a proved declaration
and not an assumption about counts, heights, or component catalogues. The
finite-set consequences are proved using the existing literal singular
component decomposition. No non-geometric component is silently discarded.
-/

namespace TranslatedDepthSeven

noncomputable section

open MvPolynomial Published

attribute [local instance] MvPolynomial.gradedAlgebra

namespace StandardAG

/-- Stacks, Lemma 33.25.10, in projective affine-chart coordinates.

The prime homogeneous ideal defines an integral projective variety; the
chart is nonempty because `X 0` is not in the ideal. Smoothness of the
displayed rational chart point is smoothness on that variety. The lemma
gives geometric integrality; equivalently, its homogeneous prime ideal
remains prime after every coefficient-field extension. These are the
ordinary chart and homogeneous-coordinate translations of the cited fact.

Reference: https://stacks.math.columbia.edu/tag/0CDW . -/
def RationalProjectiveSmoothPointGeometricIntegrality : Prop :=
  ∀ (N : ℕ) (I : Ideal (MvPolynomial (Fin (N + 1)) ℚ)),
    I.IsPrime →
    I.IsHomogeneous
      (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) ℚ) →
    MvPolynomial.X (0 : Fin (N + 1)) ∉ I →
    ∀ z : Fin N → ℚ,
      IsSmoothAffineIdealRationalPoint
        (rationalProjectiveAffineChartIdeal I) z →
      GeometricallyPrimeMvPolynomialIdeal I

end StandardAG

/-- A smooth point cell on a rational integral projective variety can be
nonempty only in the geometrically integral case. -/
theorem geometricallyPrime_of_mem_projectiveSmoothPointCell
    (hTextbook : StandardAG.RationalProjectiveSmoothPointGeometricIntegrality)
    {N : ℕ} (I : Ideal (MvPolynomial (Fin (N + 1)) ℚ))
    (hIprime : I.IsPrime)
    (hIhomogeneous : I.IsHomogeneous
      (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) ℚ))
    (hIchart : MvPolynomial.X (0 : Fin (N + 1)) ∉ I)
    (X : Finset (IntVector N)) {z : IntVector N}
    (hz : z ∈ affineIdealSmoothPointCell
      (rationalProjectiveAffineChartIdeal I)
      rationalIntegralAffineCoordinates X) :
    GeometricallyPrimeMvPolynomialIdeal I := by
  exact hTextbook N I hIprime hIhomogeneous hIchart _
    ((mem_affineIdealSmoothPointCell_iff _ _ X z).mp hz).2

/-- No smooth rational chart point exists on a non-geometrically-integral
rational prime. This does not assert that its smooth locus is empty. -/
theorem not_isSmooth_projectiveChartPoint_of_not_geometricallyPrime
    (hTextbook : StandardAG.RationalProjectiveSmoothPointGeometricIntegrality)
    {N : ℕ} (I : Ideal (MvPolynomial (Fin (N + 1)) ℚ))
    (hIprime : I.IsPrime)
    (hIhomogeneous : I.IsHomogeneous
      (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) ℚ))
    (hIchart : MvPolynomial.X (0 : Fin (N + 1)) ∉ I)
    (hnot : ¬ GeometricallyPrimeMvPolynomialIdeal I)
    (z : Fin N → ℚ) :
    ¬ IsSmoothAffineIdealRationalPoint
      (rationalProjectiveAffineChartIdeal I) z := by
  exact fun hsmooth ↦ hnot
    (hTextbook N I hIprime hIhomogeneous hIchart z hsmooth)

/-- The entire finite rational point set of a non-geometric component is
covered by the existing literal singular-component records. -/
theorem finiteIntegralProjectiveChartPointSet_eq_singularComponents_of_not_geometricallyPrime
    (hTextbook : StandardAG.RationalProjectiveSmoothPointGeometricIntegrality)
    {N : ℕ} (I : Ideal (MvPolynomial (Fin (N + 1)) ℚ))
    (hIprime : I.IsPrime)
    (hIhomogeneous : I.IsHomogeneous
      (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) ℚ))
    (hIchart : MvPolynomial.X (0 : Fin (N + 1)) ∉ I)
    (hnot : ¬ GeometricallyPrimeMvPolynomialIdeal I)
    (X : Finset (IntVector N))
    (hX : ∀ z ∈ X,
      (fun i ↦ (integralAffineChartVector z i : ℚ)) ∈
        affineIdealZeroLocus I) :
    X = (affineIdealSingularComponentRecords
      (rationalProjectiveAffineChartIdeal I)).biUnion fun record ↦
        affineIdealSingularComponentPointCell
          (rationalProjectiveAffineChartIdeal I)
          rationalIntegralAffineCoordinates X record := by
  classical
  have hempty : affineIdealSmoothPointCell
      (rationalProjectiveAffineChartIdeal I)
      rationalIntegralAffineCoordinates X = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro z hz
    exact hnot (geometricallyPrime_of_mem_projectiveSmoothPointCell
      hTextbook I hIprime hIhomogeneous hIchart X hz)
  have hsplit :=
    finiteIntegralProjectiveChartPointSet_eq_smooth_union_singularComponents
      I X hX
  simpa only [hempty, Finset.empty_union] using hsplit

end

end TranslatedDepthSeven
