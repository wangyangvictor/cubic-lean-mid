import HessianTheorem11.Concentration

/-! Universal textbook generic smoothness input for arbitrary polynomial
maps in characteristic zero. The source and image are the actual reduced
affine varieties, and the differential is computed from formal derivatives.

Justification: restrict the source and its image closure to their smooth
loci; the induced dominant morphism is generically smooth in characteristic
zero (Hartshorne, Algebraic Geometry, III.10.7). A smooth morphism of smooth
varieties has surjective tangent map (e.g. Milne, Algebraic Geometry,
Definition 5.60 and Theorem 5.61). Intersect with any prescribed dense open.
No degree, tensor, Hessian, cone, incidence, or target dimension appears.
See GENERIC_IMAGE_TANGENT_INPUT.md for hypotheses and references. -/
noncomputable section
namespace HessianTheorem11

structure GenericImageTangentOpen {n m : ℕ} (Z : Set (GeometricPoint n))
    (P : Fin m → GeometricPolynomial n) (W : Set (GeometricPoint n)) where
  openSet : Set (GeometricPoint n)
  isOpen : RelativelyOpenSet Z openSet
  subset : openSet ⊆ W
  dense : geometricClosure openSet = Z
  nonempty : openSet.Nonempty
  image_tangent : ∀ x ∈ openSet,
    affineTangentSpace (geometricClosure (polynomialMap P '' Z)) (polynomialMap P x) =
      LinearMap.range ((polynomialMapDifferential P x).domRestrict (affineTangentSpace Z x))

structure GenericImageTangentInput : Prop where
  choose : ∀ {n m : ℕ} (Z : Set (GeometricPoint n)),
    AlgebraicallyClosedSet Z → GeometricallyIrreducible Z →
    ∀ (P : Fin m → GeometricPolynomial n) (W : Set (GeometricPoint n)),
      RelativelyOpenSet Z W → geometricClosure W = Z →
      Nonempty (GenericImageTangentOpen Z P W)

theorem exists_generic_image_tangent_in_rank_open
    (GI : GenericImageTangentInput) {n m a b : ℕ}
    (Z : Set (GeometricPoint n)) (hclosed : AlgebraicallyClosedSet Z)
    (hirred : GeometricallyIrreducible Z) (P : Fin m → GeometricPolynomial n)
    (M : GeometricPoint n →ₗ[GeometricField] Matrix (Fin a) (Fin b) GeometricField)
    (G : GenericRankOpen Z P M) :
    ∃ x ∈ G.openSet,
      affineTangentSpace (geometricClosure (polynomialMap P '' Z)) (polynomialMap P x) =
        LinearMap.range ((polynomialMapDifferential P x).domRestrict (affineTangentSpace Z x)) := by
  obtain ⟨H⟩ := GI.choose Z hclosed hirred P G.openSet G.isOpen G.dense
  obtain ⟨x, hx⟩ := H.nonempty
  exact ⟨x, H.subset hx, H.image_tangent x hx⟩

end HessianTheorem11
