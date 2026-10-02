import HessianTheorem11.AffineOpenSets
import HessianTheorem11.IncidenceDefectOne
import HessianTheorem11.SingularExceptionalComponent
import HessianTheorem11.SaturatedCodimensionThree
import HessianTheorem11.GenericImageTangent

/-! The final geometric reduction for the thirteen-variable incidence bound.
All opens, kernels, tangent spaces and translated lines refer to the original
cubic and its maximal-dimensional concentration base. -/
noncomputable section
namespace HessianTheorem11
open MvPolynomial Module Matrix NonzeroLimitTransport

namespace IncidenceConcentration
variable {n : ℕ} {F : GeometricPolynomial n} (C : IncidenceConcentration F)
  (hF : F.IsHomogeneous 3)
  (G : GenericRankOpen C.base (fun i => pderiv i F) (hessianLinearMap F hF))

theorem rank_at_generic (x : GeometricPoint n) (hx : x∈G.openSet) :
    (hessian F x).rank=C.rank := by
  apply le_antisymm (C.maximal_rank x (G.subset hx))
  obtain ⟨y,hy,hyr⟩ := C.rank_attained
  have hh := G.maximal_rank x hx y hy
  change (hessian F y).rank≤_ at hh
  rwa [hyr] at hh

theorem dimension_at_generic (x : GeometricPoint n) (hx : x∈G.openSet) :
    finrank GeometricField (affineTangentSpace C.base x)=C.baseDimension := by
  rw [G.smooth x hx]
  exact_mod_cast G.dimension_base.symm.trans C.dimension_base

theorem nullity_at_generic (x : GeometricPoint n) (hx : x∈G.openSet) :
    finrank GeometricField (LinearMap.ker (hessian F x).mulVecLin)=C.nullity := by
  have hh := (hessian F x).mulVecLin.finrank_range_add_finrank_ker
  change (hessian F x).rank+_=finrank GeometricField (GeometricPoint n) at hh
  rw [C.rank_at_generic hF G x hx,show finrank GeometricField (GeometricPoint n)=n by simp] at hh
  have hc := C.rank_nullity
  omega
end IncidenceConcentration

theorem thirteen_concentration_not_singular
    (GP : GenericConePointSelectionInput) (DT : SymmetricDeterminantalTangentInput)
    (F : AnisotropicCubic 13) (hsemi : WeightSemistable (geometricPolynomial F.polynomial))
    (C : IncidenceConcentration (geometricPolynomial F.polynomial))
    (hsize : C.baseDimension+C.nullity=16) :
    ¬ C.base ⊆ singularLocus F.polynomial := by
  intro hsing
  have hnonorigin : ¬ C.base⊆{0} := by
    intro hsub
    have hd := affineDimension_mono hsub
    rw [C.dimension_base,affineDimension_singleton] at hd
    have ht : C.baseDimension≤0 := by exact_mod_cast hd
    have hn := C.rank_nullity
    omega
  let f := geometricPolynomial F.polynomial
  have hf : f.IsHomogeneous 3 := geometric_homogeneous F.homogeneous
  let P := GP.choose C.base C.closed C.irreducible C.cone hnonorigin
    (hessianLinearMap f hf) (fun i => pderiv i f)
  have ht : finrank GeometricField (affineTangentSpace C.base P.point)=C.baseDimension := by
    exact_mod_cast P.dimension.symm.trans C.dimension_base
  have hr : (hessian f P.point).rank=C.rank := by
    apply le_antisymm (C.maximal_rank P.point P.member)
    obtain ⟨y,hy,hyr⟩ := C.rank_attained
    have hh := P.rank_maximal y hy
    change (hessian f y).rank≤_ at hh
    rwa [hyr] at hh
  have hh := geometric_singular_radial_inequality DT f hf hsemi C.base P.point
    P.member P.nonzero P.radial P.rank_maximal (fun y hy => hsing hy)
  rw [ht,hr] at hh
  have hn := C.rank_nullity
  omega

theorem exists_thirteen_concentration_smooth_rank_open
    (GR : GenericRankOpenInput) (GP : GenericConePointSelectionInput)
    (DT : SymmetricDeterminantalTangentInput)
    (F : AnisotropicCubic 13) (hsemi : WeightSemistable (geometricPolynomial F.polynomial))
    (C : IncidenceConcentration (geometricPolynomial F.polynomial))
    (hsize : C.baseDimension+C.nullity=16) :
    ∃ G : GenericRankOpen C.base (fun i => pderiv i (geometricPolynomial F.polynomial))
      (hessianLinearMap (geometricPolynomial F.polynomial) (geometric_homogeneous F.homogeneous)),
      ∀x∈G.openSet,gradient (geometricPolynomial F.polynomial) x≠0 := by
  obtain ⟨G⟩ := GR.choose C.base C.closed C.irreducible
    (fun i => pderiv i (geometricPolynomial F.polynomial))
    (hessianLinearMap (geometricPolynomial F.polynomial) (geometric_homogeneous F.homogeneous))
  let O := G.openSet ∩ (C.base \ singularLocus F.polynomial)
  have hO : RelativelyOpenSet C.base O := G.isOpen.inter
    ⟨singularLocus F.polynomial,singularLocus_closed _,rfl⟩
  have hne : O.Nonempty := dense_open_inter_complement_nonempty G.dense
    (singularLocus_closed _) (thirteen_concentration_not_singular GP DT F hsemi C hsize)
  let H := G.restrictOpen O hO Set.inter_subset_left
    (hO.dense_of_nonempty C.closed C.irreducible hne) hne
  refine ⟨H,?_⟩
  intro x hx
  exact hx.2.2

theorem thirteen_concentration_generic_kernel_le_tangent
    (MR : GenericMatrixRankInput) (DT : SymmetricDeterminantalTangentInput)
    (FI : FormalImplicitFunctionInput GeometricField) (AD : AffineHypersurfaceDimensionInput)
    (boundary : RationalRelativeBoundaryInput) (bigCell : TextbookOrbitBigCellInput)
    (F : AnisotropicCubic 13) (hsemi : WeightSemistable (geometricPolynomial F.polynomial))
    (hdet : hessianDeterminantPolynomial (geometricPolynomial F.polynomial)≠0)
    (C : IncidenceConcentration (geometricPolynomial F.polynomial))
    (hsize : C.baseDimension+C.nullity=16)
    (G : GenericRankOpen C.base (fun i => pderiv i (geometricPolynomial F.polynomial))
      (hessianLinearMap (geometricPolynomial F.polynomial) (geometric_homogeneous F.homogeneous)))
    (hsmooth : ∀x∈G.openSet,gradient (geometricPolynomial F.polynomial) x≠0) :
    ∀x∈G.openSet,LinearMap.ker (hessian (geometricPolynomial F.polynomial) x).mulVecLin ≤
      affineTangentSpace C.base x := by
  let f := geometricPolynomial F.polynomial
  have hf : f.IsHomogeneous 3 := geometric_homogeneous F.homogeneous
  intro x hx
  have hxT := C.cone.radial_tangent x (G.subset hx)
  have hxL := self_notMem_hessian_ker_of_gradient_ne_zero hf x (hsmooth x hx)
  have ht := C.dimension_at_generic hf G x hx
  have hr := C.rank_at_generic hf G x hx
  have hmax : ∀y∈C.base,(hessian f y).rank≤(hessian f x).rank := G.maximal_rank x hx
  obtain ⟨E⟩ := smooth_radial_support_data f hf hsemi x _ hxT hxL
    (hessian_tangent_polarization_zero DT f hf C.base x (G.subset hx) hmax)
    (fun t ht => polarization_self_self_tangent_zero hf C.base C.contained x t ht)
  have he : (finrank GeometricField (affineTangentSpace C.base x):ℤ)-((hessian f x).rank:ℤ)=3 := by
    rw [ht,hr]
    have hn := C.rank_nullity
    omega
  have hle := (E.defect_le_one_of_thirteen he).1
  have hne := incidence_thirteen_radial_defect_ne_one MR DT FI AD boundary bigCell F hdet C hsize
    x (G.subset hx) hr _ ht E
  exact E.kernel_le_tangent_of_defect_zero (by omega)

end HessianTheorem11
