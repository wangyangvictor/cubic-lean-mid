import HessianTheorem11.KernelGradientRadical
import HessianTheorem11.PolynomialImageCoordinates

/-! Excluding a nondominant three-dimensional normal quadratic map from
the actual restricted gradient tuple of a thirteen-variable cubic. -/
noncomputable section
namespace HessianTheorem11
open MvPolynomial Matrix Module PolynomialRestriction
variable {n m d : ℕ}

theorem PolynomialImageCoordinates.differentialRadical_eq
    {P : Fin m → GeometricPolynomial n} (D : PolynomialImageCoordinates P d) :
    polynomialTupleDifferentialRadical D.tuple = polynomialTupleDifferentialRadical P := by
  let A : Matrix (Fin d) (Fin m) GeometricField :=
    fun i j => D.projection ((Pi.basisFun GeometricField (Fin m)) j) i
  let B : Matrix (Fin m) (Fin d) GeometricField :=
    fun i j => D.embedding ((Pi.basisFun GeometricField (Fin d)) j) i
  exact polynomialTupleDifferentialRadical_eq_of_mutual_combine A B D.tuple P
    D.tuple_eq D.reconstruct

theorem PolynomialImageCoordinates.imageClosure_eq_span_of_dense
    {P : Fin m → GeometricPolynomial n} (D : PolynomialImageCoordinates P d)
    (hdense : geometricClosure (polynomialMap D.tuple '' Set.univ) = Set.univ) :
    geometricClosure (polynomialMap P '' Set.univ) =
      (Submodule.span GeometricField (polynomialMap P '' Set.univ) : Set (GeometricPoint m)) := by
  have hrange : geometricClosure (polynomialMap P '' Set.univ) =
      (LinearMap.range D.embedding : Set (GeometricPoint m)) := by
    rw [D.image_eq, geometricClosure_linearMap_image D.embedding D.embedding_injective,
      hdense, Set.image_univ]
    rfl
  apply Set.Subset.antisymm
  · exact geometricClosure_subset_closed
      (fun y hy => Submodule.subset_span hy) (algebraicallyClosedSet_submodule _)
  · rw [hrange]
    apply Submodule.span_le.mpr
    intro y hy
    have hh := subset_geometricClosure (polynomialMap P '' Set.univ) hy
    rwa [hrange] at hh

theorem affineDimension_univ_from_generic_rank (GR : GenericRankOpenInput) (n : ℕ) :
    affineDimension (Set.univ : Set (GeometricPoint n)) = (n : Dimension) := by
  obtain ⟨G⟩ := GR.choose Set.univ algebraicallyClosedSet_univ geometricallyIrreducible_univ
    (fun _ : Fin 0 => (0 : GeometricPolynomial n))
    (0 : GeometricPoint n →ₗ[GeometricField] Matrix (Fin 0) (Fin 0) GeometricField)
  obtain ⟨x, hx⟩ := G.nonempty
  have hs := G.smooth x hx
  rw [affineTangentSpace_univ_geometric] at hs
  have hn : G.baseDimension = n := by simpa using hs.symm
  rw [G.dimension_base, hn]

theorem three_quadrics_dense_of_not_low_image
    (GR : GenericRankOpenInput) (AD : AffineHypersurfaceDimensionInput)
    (P : Fin 3 → GeometricPolynomial n) (hP : ∀ i, (P i).IsHomogeneous 2)
    (hnot : ¬ affineDimension (geometricClosure (polynomialMap P '' Set.univ)) ≤ 2) :
    geometricClosure (polynomialMap P '' Set.univ) = Set.univ := by
  by_contra hne
  have hlt := AD.proper_closed _ Set.univ (algebraicallyClosedSet_geometricClosure _)
    algebraicallyClosedSet_univ geometricallyIrreducible_univ
    (Set.ssubset_iff_subset_ne.mpr ⟨Set.subset_univ _, hne⟩)
  rw [affineDimension_univ_from_generic_rank GR 3] at hlt
  obtain ⟨G⟩ := GR.choose Set.univ algebraicallyClosedSet_univ geometricallyIrreducible_univ
    P (quadraticJacobianLinearMap P hP)
  rw [G.dimension_image] at hlt
  have hn : G.imageDimension < 3 := by exact_mod_cast hlt
  apply hnot
  rw [G.dimension_image]
  have hb : G.imageDimension ≤ 2 := by omega
  exact_mod_cast hb

theorem thirteen_kernel_gradient_image_not_low_of_nullity_six
    (GR : GenericRankOpenInput) (AD : AffineHypersurfaceDimensionInput)
    (F : GeometricPolynomial 13) (hF : F.IsHomogeneous 3) (hsemi : WeightSemistable F)
    (x : GeometricPoint 13) (hx : eval x F = 0)
    (hxL : x ∉ LinearMap.ker (hessian F x).mulVecLin)
    (hnullity : finrank GeometricField (LinearMap.ker (hessian F x).mulVecLin) = 6)
    (hspan : finrank GeometricField
      (kernelGradientSpan F (LinearMap.ker (hessian F x).mulVecLin)) = 3) :
    ¬ affineDimension (geometricClosure (gradient F ''
      (LinearMap.ker (hessian F x).mulVecLin : Set (GeometricPoint 13)))) ≤ 2 := by
  intro hlow
  let L := LinearMap.ker (hessian F x).mulVecLin
  let B := submoduleCoordinateMatrix L
  let P : Fin 13 → GeometricPolynomial (finrank GeometricField L) :=
    fun i => restrict B (pderiv i F)
  have hP : ∀ i, (P i).IsHomogeneous 2 := fun i => homogeneous_restrict B _ hF.pderiv
  have himage : polynomialMap P '' Set.univ = gradient F '' (L : Set (GeometricPoint 13)) :=
    polynomialMap_restrict_submodule_image (fun i => pderiv i F) L
  have hdim : finrank GeometricField (Submodule.span GeometricField
      (polynomialMap P '' Set.univ)) = 3 := by
    rw [himage]
    exact hspan
  obtain ⟨D⟩ := exists_polynomialImageCoordinates P hdim
  have hDimage : affineDimension (geometricClosure (polynomialMap D.tuple '' Set.univ)) ≤ 2 := by
    rw [affineDimension_closure, D.image_dimension, himage, ← affineDimension_closure]
    exact hlow
  have hl := three_quadrics_low_image_common_radical GR AD D.tuple (D.homogeneous hP)
    D.independent hDimage
  rw [D.differentialRadical_eq] at hl
  have hu := thirteen_kernel_gradient_differential_radical_le_three F hF hsemi x hx hxL
  change finrank GeometricField (polynomialTupleDifferentialRadical P) ≤ 3 at hu
  change finrank GeometricField L ≤ finrank GeometricField
    (polynomialTupleDifferentialRadical P) + 2 at hl
  change finrank GeometricField L = 6 at hnullity
  omega

theorem thirteen_kernel_gradient_imageClosure_eq_span_of_nullity_six
    (GR : GenericRankOpenInput) (AD : AffineHypersurfaceDimensionInput)
    (F : GeometricPolynomial 13) (hF : F.IsHomogeneous 3) (hsemi : WeightSemistable F)
    (x : GeometricPoint 13) (hx : eval x F = 0)
    (hxL : x ∉ LinearMap.ker (hessian F x).mulVecLin)
    (hnullity : finrank GeometricField (LinearMap.ker (hessian F x).mulVecLin) = 6)
    (hspan : finrank GeometricField
      (kernelGradientSpan F (LinearMap.ker (hessian F x).mulVecLin)) = 3) :
    geometricClosure (gradient F ''
      (LinearMap.ker (hessian F x).mulVecLin : Set (GeometricPoint 13))) =
      (kernelGradientSpan F (LinearMap.ker (hessian F x).mulVecLin) : Set (GeometricPoint 13)) := by
  let L := LinearMap.ker (hessian F x).mulVecLin
  let B := submoduleCoordinateMatrix L
  let P : Fin 13 → GeometricPolynomial (finrank GeometricField L) :=
    fun i => restrict B (pderiv i F)
  have hP : ∀ i, (P i).IsHomogeneous 2 := fun i => homogeneous_restrict B _ hF.pderiv
  have himage : polynomialMap P '' Set.univ = gradient F '' (L : Set (GeometricPoint 13)) :=
    polynomialMap_restrict_submodule_image (fun i => pderiv i F) L
  have hdim : finrank GeometricField (Submodule.span GeometricField
      (polynomialMap P '' Set.univ)) = 3 := by rw [himage]; exact hspan
  obtain ⟨D⟩ := exists_polynomialImageCoordinates P hdim
  have hnot : ¬ affineDimension (geometricClosure (polynomialMap D.tuple '' Set.univ)) ≤ 2 := by
    rw [affineDimension_closure, D.image_dimension, himage, ← affineDimension_closure]
    exact thirteen_kernel_gradient_image_not_low_of_nullity_six GR AD F hF hsemi x hx hxL
      hnullity hspan
  have hdense := three_quadrics_dense_of_not_low_image GR AD D.tuple (D.homogeneous hP) hnot
  have he := D.imageClosure_eq_span_of_dense hdense
  rw [himage] at he
  exact he

end HessianTheorem11
