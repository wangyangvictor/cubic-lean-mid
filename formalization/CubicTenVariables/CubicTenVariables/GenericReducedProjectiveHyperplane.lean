import CubicTenVariables.GenericReducedAffineHyperplane
import CubicTenVariables.HomogeneousRadicalChart
import CubicTenVariables.FiniteReducedGeometric
import CubicTenVariables.ProjectiveCurveSectionChartFinite
import TranslatedDepthSeven.DehomogenizationBaseChange
import TranslatedDepthSeven.ProjectiveBertiniGenericNoncontainment
import TranslatedDepthSeven.ProjectiveDegreeSpanGenericExtension
import TranslatedDepthSeven.ProjectiveChosenNonemptyChartInternal

/-! Actual coordinate charts of a full parameter-generic projective hyperplane.
Reducedness over the parameter fraction field is characteristic-free. For a
prime curve in characteristic zero, finite chart algebras are geometrically
reduced. The homogeneous section ideal is not asserted radical at the origin. -/
set_option autoImplicit false
set_option maxHeartbeats 2500000
set_option synthInstance.maxHeartbeats 400000
noncomputable section
namespace CubicTenVariables.GenericReducedProjectiveHyperplane
open MvPolynomial TranslatedDepthSeven Published
attribute [local instance] MvPolynomial.gradedAlgebra

variable {k : Type*} [Field k] {n : ℕ}
abbrev ParameterRing (k : Type*) [Field k] (n : ℕ) := MvPolynomial (Fin (n+1)) k
abbrev ParameterField (k : Type*) [Field k] (n : ℕ) := FractionRing (ParameterRing k n)

def equation (L : Type*) [CommRing L] [Algebra (ParameterRing k n) L] :
    MvPolynomial (Fin (n+1)) L :=
  ∑ i, C (algebraMap (ParameterRing k n) L (X i)) * X i

def sectionIdeal (L : Type*) [CommRing L] [Algebra k L]
    [Algebra (ParameterRing k n) L] (I : Ideal (MvPolynomial (Fin (n+1)) k)) :=
  I.map (MvPolynomial.map (algebraMap k L)) ⊔ Ideal.span {equation (k := k) (n := n) L}

def chartIdeal (L : Type*) [CommRing L] [Algebra k L]
    [Algebra (ParameterRing k n) L] (I : Ideal (MvPolynomial (Fin (n+1)) k))
    (e : Fin (n+1) ≃ Option (Fin n)) : Ideal (MvPolynomial (Fin n) L) :=
  ((sectionIdeal L I).map (renameEquiv L e)).map multivariateDehomogenization.toRingHom

theorem equation_eq (L : Type*) [CommRing L] [Algebra (ParameterRing k n) L] :
    equation (k := k) (n := n) L =
      MvPolynomial.map (algebraMap (ParameterRing k n) L)
        (bertiniCoefficientHyperplane (fun i : Fin (n+1) => (X i : MvPolynomial (Fin (n+1)) k))) := by
  simp [equation, bertiniCoefficientHyperplane]

theorem equation_isHomogeneous (L : Type*) [CommRing L]
    [Algebra (ParameterRing k n) L] :
    (equation (k := k) (n := n) L).IsHomogeneous 1 := by
  classical
  apply IsHomogeneous.sum
  intro i hi
  exact (isHomogeneous_C _ _).mul (isHomogeneous_X L i)

/-- A literal identity of ideals, retaining the original independent
coefficient variables even when the projective coordinates are renamed. -/
theorem chartIdeal_eq (L : Type*) [Field L] [Algebra k L]
    [Algebra (ParameterRing k n) L] [IsScalarTower k (ParameterRing k n) L]
    (I : Ideal (MvPolynomial (Fin (n+1)) k)) (e : Fin (n+1) ≃ Option (Fin n)) :
    chartIdeal L I e =
      (((I.map (renameEquiv k e)).map multivariateDehomogenization.toRingHom).map
        (MvPolynomial.map ((algebraMap (ParameterRing k n) L).comp C)) ⊔
      Ideal.span {MvPolynomial.map (algebraMap (ParameterRing k n) L)
        (bertiniCoefficientHyperplane
          (fun i => GenericReducedAffineHyperplane.coordinateFamily (k := k) (e i)))}) := by
  have hcoef : (algebraMap (ParameterRing k n) L).comp C = algebraMap k L :=
    (IsScalarTower.algebraMap_eq k (ParameterRing k n) L).symm
  have hrename : (I.map (MvPolynomial.map (algebraMap k L))).map (renameEquiv L e) =
      (I.map (renameEquiv k e)).map (MvPolynomial.map (algebraMap k L)) := by
    change (I.map (MvPolynomial.map (algebraMap k L))).map (renameEquiv L e).toRingHom =
      (I.map (renameEquiv k e).toRingHom).map (MvPolynomial.map (algebraMap k L))
    rw [Ideal.map_map, Ideal.map_map]
    congr 1
    ext a i <;> simp [renameEquiv_apply]
  rw [chartIdeal, sectionIdeal, Ideal.map_sup, Ideal.map_sup,
    hrename, map_dehomogenization_map_eq_map_map_dehomogenization,
    Ideal.map_span, Set.image_singleton, Ideal.map_span, Set.image_singleton, hcoef]
  congr 1
  apply congrArg (fun p => Ideal.span {p})
  change multivariateDehomogenization (rename e (equation (k := k) (n := n) L)) = _
  simp only [equation, bertiniCoefficientHyperplane, map_sum, map_mul,
    rename_C, rename_X, map_C]
  apply Finset.sum_congr rfl
  intro i hi
  cases he : e i <;> simp [he, GenericReducedAffineHyperplane.coordinateFamily,
    multivariateDehomogenization_X_none, multivariateDehomogenization]

/-- Every actual affine chart of the generic section of a reduced
homogeneous source is reduced over the parameter fraction field. -/
theorem chart_isReduced (L : Type*) [Field L] [Algebra k L]
    [Algebra (ParameterRing k n) L] [IsScalarTower k (ParameterRing k n) L]
    [IsFractionRing (ParameterRing k n) L]
    (I : Ideal (MvPolynomial (Fin (n+1)) k))
    (hhom : I.IsHomogeneous (homogeneousSubmodule (Fin (n+1)) k))
    (hrad : I.IsRadical) (e : Fin (n+1) ≃ Option (Fin n)) :
    IsReduced (MvPolynomial (Fin n) L ⧸ chartIdeal L I e) := by
  rw [chartIdeal_eq]
  have hr : (I.map (renameEquiv k e)).IsRadical := by
    have heq := Ideal.map_comap_of_equiv (I := I) (renameEquiv k e).toRingEquiv
    exact heq.symm ▸ hrad.comap (renameEquiv k e).toRingEquiv.symm
  exact GenericReducedAffineHyperplane.generic_family_quotient_isReduced L _
    (HomogeneousRadicalChart.isRadical _ (map_renameEquiv_isHomogeneous e I hhom) hr)
    e _ (by simp [GenericReducedAffineHyperplane.coordinateFamily])

/-- The full generic equation is proper on a prime projective curve. -/
theorem equation_not_mem (L : Type*) [Field L] [Algebra k L]
    [Algebra (ParameterRing k n) L] [IsScalarTower k (ParameterRing k n) L]
    [IsFractionRing (ParameterRing k n) L]
    {d : ℕ} (I : Ideal (MvPolynomial (Fin (n+1)) k)) (hI : I.IsPrime)
    (hdegree : HasProjectiveDimensionDegree I 1 d) :
    equation (k := k) (n := n) L ∉ I.map (MvPolynomial.map (algebraMap k L)) := by
  letI : I.IsPrime := hI
  obtain ⟨i, hi⟩ := exists_coordinate_not_mem_of_projectiveHilbertDimensionDegree I hdegree.2
  rw [equation_eq]
  have h := bertiniGenericCoefficientHyperplane_not_mem L I
    (fun i : Fin (n+1) => (X i : MvPolynomial (Fin (n+1)) k)) i hi
  have hcoef : (algebraMap (ParameterRing k n) L).comp C = algebraMap k L :=
    (IsScalarTower.algebraMap_eq k (ParameterRing k n) L).symm
  rw [hcoef] at h
  exact h

/-- For a prime projective curve, the literal generic section chart remains
reduced after any further field extension. No reduced-section witness is
assumed, and every projective coordinate chart is covered by `e`. -/
theorem curve_chart_geometricallyReduced
    [IsAlgClosed k] [CharZero k]
    (L : Type*) [Field L] [Algebra k L]
    [Algebra (ParameterRing k n) L] [IsScalarTower k (ParameterRing k n) L]
    [IsFractionRing (ParameterRing k n) L]
    (E : Type*) [Field E] [Algebra L E]
    {d : ℕ} (I : Ideal (MvPolynomial (Fin (n+1)) k)) (hI : I.IsPrime)
    (hhom : I.IsHomogeneous (homogeneousSubmodule (Fin (n+1)) k))
    (hdegree : HasProjectiveDimensionDegree I 1 d)
    (e : Fin (n+1) ≃ Option (Fin n)) :
    IsReduced (MvPolynomial (Fin n) E ⧸
      (chartIdeal L I e).map (MvPolynomial.map (algebraMap L E))) := by
  letI : CharZero L := charZero_of_injective_algebraMap (algebraMap k L).injective
  have hp := coefficientExtension_isPrime_of_isAlgClosed (L := L) I hI
  have hd := hasProjectiveDimensionDegree_coefficientExtension I hhom hdegree hp
  letI : Module.Finite L (MvPolynomial (Fin n) L ⧸ chartIdeal L I e) :=
    ProjectiveCurveSectionChartFinite.finite_curve_hyperplane_chart _ hp hd
      (equation L) (equation_isHomogeneous L) (equation_not_mem L I hI hdegree) e
  apply FiniteReducedGeometric.polynomial_quotient_isReduced
  exact (Ideal.isRadical_iff_quotient_reduced _).mpr (chart_isReduced L I hhom hI.isRadical e)

end CubicTenVariables.GenericReducedProjectiveHyperplane
