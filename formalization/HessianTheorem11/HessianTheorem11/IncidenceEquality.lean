import HessianTheorem11.RadialLimitKernel
import HessianTheorem11.AffineHypersurfaceDimension
import HessianTheorem11.IncidenceRadial
import HessianTheorem11.Concentration

/-! Equality in the incidence radial estimate promotes the actual
concentrated base to the entire cubic hypersurface. In twelve variables,
failure of the incidence bound therefore forces actual generic Hessian rank
eight. All rigidity steps are proved from the polynomial and tangent data. -/

noncomputable section
namespace HessianTheorem11
open MvPolynomial Module

/-- The source equality-case promotion, including the exact geometric
kernel dimension, for an actual concentrated incidence component. -/
theorem incidence_equality_concentrated_base
    (GP : GenericConePointSelectionInput) (DT : SymmetricDeterminantalTangentInput)
    (AD : AffineHypersurfaceDimensionInput)
    (boundary : NonzeroLimitTransport.RationalRelativeBoundaryInput)
    (bigCell : NonzeroLimitTransport.TextbookOrbitBigCellInput)
    {n e : ℕ} (F : AnisotropicCubic n) (he : 1 ≤ e) (hn : n = 3 * e + 3)
    (hsemi : WeightSemistable (geometricPolynomial F.polynomial))
    (hirred : Irreducible (geometricPolynomial F.polynomial))
    (C : IncidenceConcentration (geometricPolynomial F.polynomial))
    (hD : C.baseDimension + C.nullity = n + e) :
    C.base = polynomialHypersurface (geometricPolynomial F.polynomial) ∧ C.nullity = e + 1 := by
  have hn0 : 0 < n := by omega
  have hnonorigin : ¬ C.base ⊆ {0} := by
    intro ho
    have hd := affineDimension_mono ho
    rw [C.dimension_base, affineDimension_singleton] at hd
    have ht : C.baseDimension ≤ 0 := by exact_mod_cast hd
    have hr := C.rank_nullity
    omega
  let P := GP.choose C.base C.closed C.irreducible C.cone hnonorigin
    (hessianLinearMap (geometricPolynomial F.polynomial) (geometric_homogeneous F.homogeneous))
    (fun i => pderiv i (geometricPolynomial F.polynomial))
  have hprank : (hessian (geometricPolynomial F.polynomial) P.point).rank = C.rank := by
    apply le_antisymm (C.maximal_rank P.point P.member)
    obtain ⟨y, hy, hyr⟩ := C.rank_attained
    have h := P.rank_maximal y hy
    change (hessian (geometricPolynomial F.polynomial) y).rank ≤ _ at h
    rwa [hyr] at h
  have hpt : finrank GeometricField (affineTangentSpace C.base P.point) = C.baseDimension := by
    have hd := P.dimension
    rw [C.dimension_base] at hd
    exact_mod_cast hd.symm
  have hgenericSing : gradient (geometricPolynomial F.polynomial) P.point = 0 →
      ∀ y ∈ C.base, gradient (geometricPolynomial F.polynomial) y = 0 := by
    intro hx
    have hp : P.point ∈ finiteEquationZeroSet
        (fun i => pderiv i (geometricPolynomial F.polynomial)) := by
      intro i
      exact congrFun hx i
    intro y hy
    ext i
    exact P.detects_equations hp hy i
  have hsmooth : gradient (geometricPolynomial F.polynomial) P.point ≠ 0 := by
    intro hs
    have h := geometric_singular_radial_inequality DT (geometricPolynomial F.polynomial)
      (geometric_homogeneous F.homogeneous) hsemi C.base P.point P.member P.nonzero P.radial
      P.rank_maximal (hgenericSing hs)
    rw [hprank, hpt] at h
    have hr := C.rank_nullity
    omega
  have heq : 3 * ((finrank GeometricField (affineTangentSpace C.base P.point) : ℤ) -
      ((hessian (geometricPolynomial F.polynomial) P.point).rank : ℤ)) + 3 = (n : ℤ) := by
    rw [hprank, hpt]
    have hr := C.rank_nullity
    omega
  obtain ⟨E⟩ := smooth_radial_equality_data (geometricPolynomial F.polynomial)
    (geometric_homogeneous F.homogeneous) hsemi P.point (affineTangentSpace C.base P.point)
    P.radial (self_notMem_hessian_ker_of_gradient_ne_zero
      (geometric_homogeneous F.homogeneous) P.point hsmooth)
    (hessian_tangent_polarization_zero DT (geometricPolynomial F.polynomial)
      (geometric_homogeneous F.homogeneous) C.base P.point P.member P.rank_maximal)
    (fun t ht => polarization_self_self_tangent_zero (geometric_homogeneous F.homogeneous)
      C.base C.contained P.point t ht) heq
  have hc := E.normal_card_le_one boundary bigCell F hn0
  have hct := Finset.card_sdiff_add_card_eq_card
    (Finset.subset_univ E.adapted.tangentIndices)
  rw [Finset.card_univ, Fintype.card_fin, E.adapted.tangent_card, hpt] at hct
  have hdimge : n - 1 ≤ C.baseDimension := by omega
  have hbase := equal_hypersurface_of_dimension_ge AD (geometricPolynomial F.polynomial)
    hirred C.base C.closed C.contained (by rw [C.dimension_base]; exact_mod_cast hdimge)
  refine ⟨hbase, ?_⟩
  have hd := C.dimension_base
  rw [hbase, AD.hypersurface _ hirred] at hd
  have hdim : n - 1 = C.baseDimension := by exact_mod_cast hd
  omega

/-- Failure of the twelve-variable incidence bound forces generic Hessian
rank eight. This conclusion concerns the actual rank supremum on the whole
cubic, because the concentrated base has been proved equal to that locus. -/
theorem incidence_twelve_violation_forces_generic_rank_eight
    (AG : ConcentrationGeometryInput) (GP : GenericConePointSelectionInput)
    (DT : SymmetricDeterminantalTangentInput) (AD : AffineHypersurfaceDimensionInput)
    (boundary : NonzeroLimitTransport.RationalRelativeBoundaryInput)
    (bigCell : NonzeroLimitTransport.TextbookOrbitBigCellInput)
    (F : AnisotropicCubic 12)
    (hsemi : WeightSemistable (geometricPolynomial F.polynomial))
    (hirred : Irreducible (geometricPolynomial F.polynomial))
    (hI : 14 < incidenceDimension F.polynomial) :
    genericHessianRank F.polynomial = 8 := by
  obtain ⟨C⟩ := incidence_concentration AG DT (geometricPolynomial F.polynomial)
    (geometric_homogeneous F.homogeneous)
  obtain ⟨D, hD, hrad⟩ := incidence_radial_of_concentrated_base GP DT F.polynomial
    F.homogeneous hsemi C.base C.closed C.irreducible C.cone C.contained
    C.baseDimension C.rank C.nullity C.dimension_base C.dimension_incidence
    C.rank_nullity C.rank_attained C.maximal_rank
  have hlarge : 14 < D := by rw [hD] at hI; exact_mod_cast hI
  have hD15 : D = 15 := by rcases hrad with h | h <;> omega
  have heq : C.baseDimension + C.nullity = 12 + 3 := by
    have hd : incidenceDimension F.polynomial =
        ((C.baseDimension + C.nullity : ℕ) : Dimension) := C.dimension_incidence
    rw [hD, hD15] at hd
    exact_mod_cast hd.symm
  obtain ⟨hbase, hnull⟩ := incidence_equality_concentrated_base GP DT AD boundary bigCell
    F (by decide : 1 ≤ 3) (by decide : 12 = 3 * 3 + 3) hsemi hirred C heq
  have hrank : C.rank = 8 := by have hr := C.rank_nullity; omega
  apply le_antisymm
  · apply csSup_le'
    rintro r ⟨x, hx, rfl⟩
    have hxC : x ∈ C.base := by rw [hbase]; exact hx
    simpa [hrank] using C.maximal_rank x hxC
  · obtain ⟨x, hx, hr⟩ := C.rank_attained
    have hxF : x ∈ cubicLocus F.polynomial := by rw [hbase] at hx; exact hx
    have hb := rank_le_genericHessianRank F.polynomial hxF
    simpa [hr, hrank] using hb

end HessianTheorem11
