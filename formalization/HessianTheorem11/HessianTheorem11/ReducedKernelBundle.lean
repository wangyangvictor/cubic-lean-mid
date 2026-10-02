import HessianTheorem11.ReducedFiberMapDifferential

/-! The full ordinary constant-rank kernel-bundle input is constructed.
Irreducibility is unconditional. Dimension follows from GR, the proved
product dimension theorem, and the actual projector-map differential kernel.
No new geometric premise is introduced. -/
noncomputable section
set_option maxHeartbeats 2400000
namespace HessianTheorem11.ReducedKernelBundle
open MvPolynomial Module Matrix ReducedKernelTangent ReducedGenericImageTangent
  ReducedAffineProduct ReducedAffineProductDimension ReducedKernelBundleCharts
  ReducedFiberMapDifferential KernelAnnihilatorProjector

/-- Dimension of the actual kernel bundle, using generic rank/smoothness
only; the ordinary bundle theorem is not used in its own construction. -/
theorem kernel_bundle_dimension (GR : GenericRankOpenInput) {n a b : ℕ}
    (M : GeometricPoint n →ₗ[GeometricField] Matrix (Fin a) (Fin b) GeometricField)
    (U O : Set (GeometricPoint n)) (hU : AlgebraicallyClosedSet U)
    (hi : GeometricallyIrreducible U) (hO : RelativelyOpenSet U O)
    (hdense : geometricClosure O = U) (t ell : ℕ)
    (ht : affineDimension U = (t : Dimension))
    (hnull : ∀ x ∈ O, finrank GeometricField (LinearMap.ker (M x).mulVecLin) = ell) :
    affineDimension (kernelBundle M O) = ((t+ell : ℕ) : Dimension) := by
  have hnO : O.Nonempty := by
    by_contra hn
    have he : O = ∅ := Set.not_nonempty_iff_eq_empty.mp hn
    have hu : U = ∅ := by
      rw [he] at hdense
      simpa only [geometricClosure,vanishingIdeal_empty,zeroLocus_top] using hdense.symm
    exact hi.nonempty.ne_empty hu
  obtain ⟨x,hx⟩ := hnO
  obtain ⟨rows,cols,hminor⟩ := MatrixRankMinors.exists_rank_minor (M x)
  have hrank (y) (hy : y ∈ O) : (M y).rank = (M x).rank := by
    have ha := (M y).mulVecLin.finrank_range_add_finrank_ker
    have hb := (M x).mulVecLin.finrank_range_add_finrank_ker
    change (M y).rank + _ = _ at ha
    change (M x).rank + _ = _ at hb
    rw [hnull y hy] at ha
    rw [hnull x hx] at hb
    omega
  let A := projector (ReducedDeterminantal.pencilPolynomial M) rows cols
  let V := minorOpen O (minorPolynomial M rows cols)
  have hv : x ∈ V := ⟨hx,by simpa using hminor⟩
  have hV : RelativelyOpenSet U V := minorOpen_isOpen hO _
  let S := affineCylinder U b
  have hS : AlgebraicallyClosedSet S := by
    have he : polynomialMap (linearCoordinatePolynomials (baseProjection n b)) =
        baseProjection n b := funext (polynomialMap_linearCoordinatePolynomials _)
    simpa only [he] using
      closed_polynomial_preimage (linearCoordinatePolynomials (baseProjection n b)) hU
  have hiS : GeometricallyIrreducible S := affineCylinder_irreducible U hi
  obtain ⟨G⟩ := GR.choose S hS hiS (coordinateFiberMap A)
    (0 : GeometricPoint (n+b) →ₗ[GeometricField] Matrix (Fin 0) (Fin 0) GeometricField)
  let LP := linearCoordinatePolynomials (baseProjection n b)
  have hLP : polynomialMap LP '' S = U := cylinder_image_base U
  have hoV : RelativelyOpenSet S (S ∩ polynomialMap LP ⁻¹' V) :=
    relativelyOpen_polynomial_preimage LP S hV (hLP ▸ Set.Subset.refl U)
  have hnV : (S ∩ polynomialMap LP ⁻¹' V).Nonempty := by
    refine ⟨(splitEquiv n b).symm (x,0),?_,?_⟩
    · change ((splitEquiv n b) ((splitEquiv n b).symm (x,0))).1 ∈ U
      simpa using (open_subset hO) hx
    · change polynomialMap LP ((splitEquiv n b).symm (x,0)) ∈ V
      rw [polynomialMap_linearCoordinatePolynomials]
      change ((splitEquiv n b) ((splitEquiv n b).symm (x,0))).1 ∈ V
      simpa using hv
  obtain ⟨z,hzG,hzS,hzV⟩ := dense_inter_open_nonempty G.dense hoV hnV
  have hzV' : baseProjection n b z ∈ V := by simpa only [Set.mem_preimage,LP,polynomialMap_linearCoordinatePolynomials] using hzV
  have hAz : A.map (eval (baseProjection n b z)) =
      projector (M (baseProjection n b z)) rows cols := by
    simp only [A,projector_map,eval_pencil]
  have hArank : (A.map (eval (baseProjection n b z))).rank = ell := by
    change finrank GeometricField (LinearMap.range (A.map (eval (baseProjection n b z))).mulVecLin) = ell
    rw [hAz,range_projector _ rows cols
      (by simpa using hzV'.2) (hrank _ hzV'.1).le,hnull _ hzV'.1]
  have hdimS : affineDimension S = ((t+b : ℕ) : Dimension) := by
    rw [affineCylinder_dimension GR U hU hi,ht]
    norm_cast
  have hbase : G.baseDimension = t+b := by exact_mod_cast G.dimension_base.symm.trans hdimS
  have hD := ((polynomialMapDifferential (coordinateFiberMap A) z).domRestrict
    (affineTangentSpace S z)).finrank_range_add_finrank_ker
  rw [G.differential_rank z hzG,tangent_kernel_dimension A U z hzS,
    G.smooth z hzG,hbase] at hD
  have hAM := (A.map (eval (baseProjection n b z))).mulVecLin.finrank_range_add_finrank_ker
  change (A.map (eval (baseProjection n b z))).rank + _ = _ at hAM
  rw [hArank] at hAM
  simp only [Module.finrank_pi,Fintype.card_fin] at hAM
  have himg : G.imageDimension = t+ell := by omega
  let E := pairCoordinateEquiv n b
  let PE := PolynomialCoordinateEquiv.ofLinearEquiv E
  have hImage : polynomialMap (coordinateFiberMap A) '' S =
      E '' (polynomialMap (fiberMap A) '' affineProduct U) := by
    rw [show S = affineCylinder U b from rfl,affineCylinder_eq_product_image,Set.image_image,Set.image_image]
    congr 1
    funext p
    exact map_coordinateFiberMap_pair A p
  have hEdim : affineDimension (E '' (polynomialMap (fiberMap A) '' affineProduct U)) =
      affineDimension (polynomialMap (fiberMap A) '' affineProduct U) := by
    simpa only [PE,PolynomialCoordinateEquiv.ofLinearEquiv_forwardMap] using
      PE.affineDimension_image (polynomialMap (fiberMap A) '' affineProduct U)
  have hGdim := G.dimension_image
  rw [affineDimension_closure,hImage,hEdim,himg] at hGdim
  have hK := kernel_closure_eq_chart M U O hU hi hO rows cols hrank ⟨x,hv⟩
  have hKdim := congrArg affineDimension hK
  rw [affineDimension_closure,affineDimension_closure] at hKdim
  exact hKdim.trans hGdim

/-- Both fields of the exact old KernelBundleInput, constructed from GR. -/
def kernelBundleInput (GR : GenericRankOpenInput) : KernelBundleInput where
  closure_irreducible := kernel_bundle_closure_irreducible
  dimension := kernel_bundle_dimension GR

end HessianTheorem11.ReducedKernelBundle
