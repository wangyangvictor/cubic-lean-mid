import HessianTheorem11.UnconditionalWeightDescent
import HessianTheorem11.ReducedClosedOrbitZero
import HessianTheorem11.CubicIrreducibility
import HessianTheorem11.IncidenceThirteenGeometry
import HessianTheorem11.SaturatedCodimensionTwo
import HessianTheorem11.KernelQuadraticImage
import HessianTheorem11.Completed

/-! The thirteen-variable incidence entry, assembled from actual maximal
concentration, translated kernel saturation, and the three saturated cases. -/
noncomputable section
namespace HessianTheorem11
open MvPolynomial Module Matrix NonzeroLimitTransport

theorem incidence_thirteen_le_fifteen
    (AG : ConcentrationGeometryInput) (GP : GenericConePointSelectionInput)
    (GI : GenericImageTangentInput) (MR : GenericMatrixRankInput)
    (DT : SymmetricDeterminantalTangentInput) (AD : AffineHypersurfaceDimensionInput)
    (FI : FormalImplicitFunctionInput GeometricField) (SA : FormalSmoothArcInput)
    (boundary : RationalRelativeBoundaryInput) (bigCell : TextbookOrbitBigCellInput)
    (F : AnisotropicCubic 13)
    (hsemi : WeightSemistable (geometricPolynomial F.polynomial))
    (hirred : Irreducible (geometricPolynomial F.polynomial))
    (hdet : hessianDeterminantPolynomial (geometricPolynomial F.polynomial)≠0) :
    incidenceDimension F.polynomial≤15 := by
  by_contra hbad
  let f := geometricPolynomial F.polynomial
  have hf : f.IsHomogeneous 3 := geometric_homogeneous F.homogeneous
  obtain ⟨C,hCmax⟩ := exists_maximal_concentration_base AG DT AD f hf hirred
  obtain ⟨d,hd,hrad⟩ := incidence_radial_of_concentrated_base GP DT F.polynomial F.homogeneous hsemi
    C.base C.closed C.irreducible C.cone C.contained C.baseDimension C.rank C.nullity
    C.dimension_base C.dimension_incidence C.rank_nullity C.rank_attained C.maximal_rank
  have hdlarge : 15<d := by
    have hh := lt_of_not_ge hbad
    rw [hd] at hh
    exact_mod_cast hh
  have hd16 : d=16 := by rcases hrad with h|h <;> omega
  have hsize : C.baseDimension+C.nullity=16 := by
    have hh : incidenceDimension F.polynomial=((C.baseDimension+C.nullity:ℕ):Dimension) :=
      C.dimension_incidence
    rw [hd,hd16] at hh
    exact_mod_cast hh.symm
  obtain ⟨G,hgrad⟩ := exists_thirteen_concentration_smooth_rank_open
    AG.toGenericRankOpenInput GP DT F hsemi C hsize
  have hKT := thirteen_concentration_generic_kernel_le_tangent MR DT FI AD boundary bigCell
    F hsemi hdet C hsize G hgrad
  have hsat := maximal_concentration_kernel_saturation AG DT AD f hf C hCmax G hKT
  obtain ⟨x,hx,himage⟩ := exists_generic_image_tangent_in_rank_open GI C.base C.closed C.irreducible
    (fun i => pderiv i f) (hessianLinearMap f hf) G
  rw [polynomialMap_gradient,polynomialMapDifferential_gradient] at himage
  have hxC := G.subset hx
  have hxT := C.cone.radial_tangent x hxC
  have hxL := self_notMem_hessian_ker_of_gradient_ne_zero hf x (hgrad x hx)
  have ht := C.dimension_at_generic hf G x hx
  have hk := C.nullity_at_generic hf G x hx
  have hr := C.rank_at_generic hf G x hx
  have hmax : ∀y∈C.base,(hessian f y).rank≤(hessian f x).rank := G.maximal_rank x hx
  have hann : affineTangentSpace C.base x ≤
      kernelQuadraticAnnihilator f (LinearMap.ker (hessian f x).mulVecLin) :=
    fun _ ht => hessian_tangent_polarization_zero DT f hf C.base x hxC hmax _ ht
  have hlt : finrank GeometricField (LinearMap.ker (hessian f x).mulVecLin)<
      finrank GeometricField (affineTangentSpace C.base x) := by
    apply Submodule.finrank_lt_finrank_of_lt
    exact lt_of_le_of_ne (hKT x hx) (fun he => hxL (he ▸ hxT))
  have htge : 9≤C.baseDimension := by rw [hk,ht] at hlt; omega
  have htle : C.baseDimension≤12 := by
    have hh := affineDimension_mono (show C.base⊆polynomialHypersurface f from C.contained)
    rw [C.dimension_base,AD.hypersurface f hirred] at hh
    exact_mod_cast hh
  have htne12 : C.baseDimension≠12 := by
    intro he
    have hbase := equal_hypersurface_of_dimension_ge AD f hirred C.base C.closed C.contained
      (by rw [C.dimension_base,he])
    have hgood := geometric_rank_thirteen MR DT FI f hf hirred hdet
    rw [geometricCubicGenericRank_geometricPolynomial MR F.polynomial hirred] at hgood
    have hle : genericHessianRank F.polynomial≤C.rank := by
      apply csSup_le'
      rintro r ⟨y,hy,rfl⟩
      apply C.maximal_rank y
      rw [hbase]
      exact hy
    have hn := C.rank_nullity
    omega
  have htne9 := concentrated_base_dimension_ne_nine_of_kernel_saturation
    AG.toGenericRankOpenInput AD f hf hsemi C hsize G x hx hxT hxL (hKT x hx) hann
    (fun a ha => by simpa using hsat x hx 0 a ha)
  have hcases : C.baseDimension=10 ∨ C.baseDimension=11 := by omega
  rcases hcases with hc|hc
  · apply thirteen_saturated_codimension_three_impossible AG.toGenericRankOpenInput AD f hf hsemi
      C.base C.contained x hxC (hgrad x hx) hxT (hKT x hx) hann (ht.trans hc)
      (by rw [hk]; omega) hmax (hsat x hx) himage
  · apply thirteen_saturated_codimension_two_impossible AG.toGenericRankOpenInput AD SA boundary bigCell
      F hsemi C.base C.closed C.irreducible C.contained x hxC
      (by rw [ht]; exact C.dimension_base) (hgrad x hx) hxT (hKT x hx) hann
      (ht.trans hc) (by rw [hk]; omega) hmax (hsat x hx) himage

namespace Completed
open RationalDescent

/-- Theorem 1.1, thirteen-variable incidence dimension: at most fifteen.
The target concerns the actual affine incidence locus and its Krull dimension. -/
theorem I13
    (AG : ConcentrationGeometryInput) (GP : GenericConePointSelectionInput)
    (GI : GenericImageTangentInput) (MR : GenericMatrixRankInput)
    (DT : SymmetricDeterminantalTangentInput) (AD : AffineHypersurfaceDimensionInput)
    (FI : FormalImplicitFunctionInput GeometricField) (SA : FormalSmoothArcInput)
    (boundary : RationalRelativeBoundaryInput) (bigCell : TextbookOrbitBigCellInput)
    (DTQ : DeterminantalTangentOver ℚ) (CI : CubicGeometricIrreducibility)
    : Targets.I13 := by
  intro F
  exact incidence_thirteen_le_fifteen AG GP GI MR DT AD FI SA boundary bigCell F
    (UnconditionalWeightDescent.anisotropic_geometric_weightSemistable F (by norm_num))
    (CI F (by norm_num))
    (geometric_hessianDeterminantPolynomial_ne_zero DTQ F)

end Completed
end HessianTheorem11
