import HessianTheorem11.SubmoduleCoordinates
import HessianTheorem11.KernelSaturation

/-! The actual gradient quadrics on a saturated Hessian kernel. A
two-dimensional gradient image cannot have four-dimensional conormal span. -/
noncomputable section
namespace HessianTheorem11
open Module Matrix MvPolynomial

theorem restriction_rank_add_nullity_of_kernel_le
    {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] [AddCommGroup W] [Module K W]
    (A : V →ₗ[K] W) (T : Submodule K V) (hKT : LinearMap.ker A ≤ T) :
    finrank K (LinearMap.range (A.domRestrict T)) +
      finrank K (LinearMap.ker A) = finrank K T := by
  have he : (LinearMap.ker (A.domRestrict T)).map T.subtype = LinearMap.ker A := by
    ext v
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact hu
    · intro hv
      exact ⟨⟨v, hKT hv⟩, hv, rfl⟩
  have hd := congrArg (fun S : Submodule K V => finrank K S) he
  dsimp only at hd
  rw [Submodule.finrank_map_subtype_eq] at hd
  rw [← hd]
  exact (A.domRestrict T).finrank_range_add_finrank_ker

theorem kernelGradientSpan_finrank_le_three_of_low_image
    (GR : GenericRankOpenInput) (AD : AffineHypersurfaceDimensionInput)
    {n : ℕ} (F : GeometricPolynomial n) (hF : F.IsHomogeneous 3)
    (L : Submodule GeometricField (GeometricPoint n))
    (hdim : affineDimension (geometricClosure (gradient F '' (L : Set (GeometricPoint n)))) ≤ 2) :
    finrank GeometricField (kernelGradientSpan F L) ≤ 3 := by
  exact quadratic_submodule_low_image_span_le_three GR AD (fun i => pderiv i F)
    (fun i => hF.pderiv) L hdim

theorem thirteen_conormal_codimension_le_three_of_low_gradient_image
    (GR : GenericRankOpenInput) (AD : AffineHypersurfaceDimensionInput)
    (F : GeometricPolynomial 13) (hF : F.IsHomogeneous 3)
    (hsemi : WeightSemistable F) (x : GeometricPoint 13) (hx : eval x F = 0)
    (T : Submodule GeometricField (GeometricPoint 13)) (hxT : x ∈ T)
    (hxL : x ∉ LinearMap.ker (hessian F x).mulVecLin)
    (hann : T ≤ kernelQuadraticAnnihilator F (LinearMap.ker (hessian F x).mulVecLin))
    (hdim : finrank GeometricField T +
      finrank GeometricField (LinearMap.ker (hessian F x).mulVecLin) = 16)
    (himage : affineDimension (geometricClosure (gradient F ''
      (LinearMap.ker (hessian F x).mulVecLin : Set (GeometricPoint 13)))) ≤ 2) :
    13 - finrank GeometricField T ≤ 3 := by
  have he := kernelGradientSpan_eq_conormal_of_thirteen F hF hsemi x hx T hxT hxL hann hdim
  have hb := kernelGradientSpan_finrank_le_three_of_low_image GR AD F hF _ himage
  rw [he, LinearMap.BilinForm.finrank_orthogonal coordinatePairing_nondegenerate
    coordinatePairing_reflexive] at hb
  simpa using hb

theorem concentrated_base_dimension_ne_nine_of_kernel_saturation
    (GR : GenericRankOpenInput) (AD : AffineHypersurfaceDimensionInput)
    (F : GeometricPolynomial 13) (hF : F.IsHomogeneous 3) (hsemi : WeightSemistable F)
    (C : IncidenceConcentration F) (hsize : C.baseDimension + C.nullity = 16)
    (G : GenericRankOpen C.base (fun i => pderiv i F) (hessianLinearMap F hF))
    (x : GeometricPoint 13) (hx : x ∈ G.openSet)
    (hxT : x ∈ affineTangentSpace C.base x)
    (hxL : x ∉ LinearMap.ker (hessian F x).mulVecLin)
    (hKT : LinearMap.ker (hessian F x).mulVecLin ≤ affineTangentSpace C.base x)
    (hann : affineTangentSpace C.base x ≤
      kernelQuadraticAnnihilator F (LinearMap.ker (hessian F x).mulVecLin))
    (hsat : (LinearMap.ker (hessian F x).mulVecLin : Set (GeometricPoint 13)) ⊆ C.base) :
    C.baseDimension ≠ 9 := by
  intro hbad
  have ht : G.baseDimension = C.baseDimension := by
    have he := G.dimension_base.symm.trans C.dimension_base
    exact_mod_cast he
  have hr : (hessian F x).rank = C.rank := by
    apply le_antisymm (C.maximal_rank x (G.subset hx))
    obtain ⟨y, hy, hyr⟩ := C.rank_attained
    have hh := G.maximal_rank x hx y hy
    change (hessian F y).rank ≤ _ at hh
    rwa [hyr] at hh
  have hk : finrank GeometricField (LinearMap.ker (hessian F x).mulVecLin) = C.nullity := by
    have hn := (hessian F x).mulVecLin.finrank_range_add_finrank_ker
    change (hessian F x).rank + _ = _ at hn
    rw [hr, show finrank GeometricField (GeometricPoint 13) = 13 by simp] at hn
    have hc := C.rank_nullity
    omega
  have hdT : finrank GeometricField (affineTangentSpace C.base x) = 9 := by
    rw [G.smooth x hx, ht, hbad]
  have hd16 : finrank GeometricField (affineTangentSpace C.base x) +
      finrank GeometricField (LinearMap.ker (hessian F x).mulVecLin) = 16 := by
    rw [G.smooth x hx, ht, hk]
    exact hsize
  have hg := G.differential_rank x hx
  rw [polynomialMapDifferential_gradient] at hg
  have hb := restriction_rank_add_nullity_of_kernel_le (hessian F x).mulVecLin
    (affineTangentSpace C.base x) hKT
  rw [hg, hk, hdT] at hb
  have hgi : G.imageDimension = 2 := by omega
  have himage : affineDimension (geometricClosure (gradient F ''
      (LinearMap.ker (hessian F x).mulVecLin : Set (GeometricPoint 13)))) ≤ 2 := by
    have hm := affineDimension_mono (geometricClosure_mono (Set.image_mono
      (f := gradient F) hsat))
    have hd := G.dimension_image
    change affineDimension (geometricClosure (gradient F '' C.base)) = _ at hd
    rw [hd, hgi] at hm
    exact hm
  have hh := thirteen_conormal_codimension_le_three_of_low_gradient_image GR AD F hF hsemi
    x (C.contained x (G.subset hx)) _ hxT hxL hann hd16 himage
  rw [hdT] at hh
  omega

end HessianTheorem11
