import HessianTheorem11.ReducedGenericImageTangent
import HessianTheorem11.ReducedKernelTangent
import HessianTheorem11.ReducedAffineProduct

/-! Tangent-space and dimension calculations for actual products with
affine space. The calculation uses GR and actual product irreducibility. -/
noncomputable section
namespace HessianTheorem11.ReducedAffineProductDimension
open MvPolynomial Module ReducedKernelTangent ReducedGenericImageTangent

theorem tangent_univ {n : ℕ} (x : GeometricPoint n) :
    affineTangentSpace (Set.univ : Set (GeometricPoint n)) x = ⊤ := by
  apply top_unique
  intro v _
  apply mem_affineTangentSpace.mpr
  intro P hP
  have hp : P = 0 := MvPolynomial.funext (fun y => hP y (Set.mem_univ y))
  rw [hp]
  simp [polynomialDifferential_apply]

/-- Every actual affine line in a set supplies its direction as a tangent
vector; the proof is polynomial substitution and the chain rule. -/
theorem tangent_of_affine_line {n : ℕ} (Z : Set (GeometricPoint n))
    (x v : GeometricPoint n) (hline : ∀ a : GeometricField, x + a • v ∈ Z) :
    v ∈ affineTangentSpace Z x := by
  let P : Fin n → GeometricPolynomial 1 := fun i => C (x i) + C (v i) * X 0
  have hp (a : GeometricPoint 1) : polynomialMap P a = x + a 0 • v := by
    ext i
    simp [P, polynomialMap, mul_comm]
  have hmap : polynomialMap P '' Set.univ ⊆ Z := by
    rintro _ ⟨a, _, rfl⟩
    rw [hp]
    exact hline _
  have ht : (fun _ : Fin 1 => (1 : GeometricField)) ∈
      affineTangentSpace Set.univ (0 : GeometricPoint 1) := by
    rw [tangent_univ]
    trivial
  have h := differential_maps_tangent P Set.univ Z hmap 0 (fun _ => 1) ht
  have hd : polynomialMapDifferential P 0 (fun _ => 1) = v := by
    ext i
    simp [polynomialMapDifferential, P, ReducedTangentRank.differential_add,
      ReducedTangentRank.differential_mul]
  rw [hd, hp] at h
  simpa using h

def affineCylinder {n : ℕ} (Z : Set (GeometricPoint n)) (b : ℕ) :
    Set (GeometricPoint (n+b)) := baseProjection n b ⁻¹' Z

def vertical (n b : ℕ) : GeometricPoint b →ₗ[GeometricField] GeometricPoint (n+b) :=
  (splitEquiv n b).symm.toLinearMap.comp
    (LinearMap.inr GeometricField (GeometricPoint n) (GeometricPoint b))

@[simp] theorem base_vertical {n b : ℕ} (u : GeometricPoint b) :
    baseProjection n b (vertical n b u) = 0 := by
  change ((splitEquiv n b) ((splitEquiv n b).symm (0,u))).1 = 0
  simp

@[simp] theorem fiber_vertical {n b : ℕ} (u : GeometricPoint b) :
    fiberProjection n b (vertical n b u) = u := by
  change ((splitEquiv n b) ((splitEquiv n b).symm (0,u))).2 = u
  simp

theorem vertical_mem_tangent {n b : ℕ} (Z : Set (GeometricPoint n))
    (x : GeometricPoint (n+b)) (hx : x ∈ affineCylinder Z b) (u : GeometricPoint b) :
    vertical n b u ∈ affineTangentSpace (affineCylinder Z b) x := by
  apply tangent_of_affine_line
  intro a
  change baseProjection n b (x + a • vertical n b u) ∈ Z
  simpa using hx

/-- The kernel of the base projection on the actual product tangent space
is exactly its full vertical affine-space factor. -/
theorem tangent_projection_kernel_dimension {n b : ℕ}
    (Z : Set (GeometricPoint n)) (x : GeometricPoint (n+b))
    (hx : x ∈ affineCylinder Z b) :
    finrank GeometricField (LinearMap.ker ((baseProjection n b).domRestrict
      (affineTangentSpace (affineCylinder Z b) x))) = b := by
  let T := affineTangentSpace (affineCylinder Z b) x
  let A := (baseProjection n b).domRestrict T
  let L : LinearMap.ker A →ₗ[GeometricField] GeometricPoint b :=
    (fiberProjection n b).comp (T.subtype.comp (LinearMap.ker A).subtype)
  have hL : Function.Bijective L := by
    constructor
    · intro u v huv
      apply Subtype.ext
      apply Subtype.ext
      apply (splitEquiv n b).injective
      apply Prod.ext
      · exact (LinearMap.mem_ker.mp u.property).trans (LinearMap.mem_ker.mp v.property).symm
      · exact huv
    · intro u
      refine ⟨⟨⟨vertical n b u, vertical_mem_tangent Z x hx u⟩, ?_⟩, ?_⟩
      · exact base_vertical u
      · exact fiber_vertical u
  have h := (LinearEquiv.ofBijective L hL).finrank_eq
  simpa using h

theorem cylinder_image_base {n b : ℕ} (Z : Set (GeometricPoint n)) :
    polynomialMap (linearCoordinatePolynomials (baseProjection n b)) ''
      affineCylinder Z b = Z := by
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    simpa only [polynomialMap_linearCoordinatePolynomials] using hx
  · intro hz
    refine ⟨(splitEquiv n b).symm (z,0), ?_, ?_⟩
    · change ((splitEquiv n b) ((splitEquiv n b).symm (z,0))).1 ∈ Z
      simpa using hz
    · rw [polynomialMap_linearCoordinatePolynomials]
      change ((splitEquiv n b) ((splitEquiv n b).symm (z,0))).1 = z
      simp

theorem affineCylinder_dimension_of_irreducible (GR : GenericRankOpenInput)
    {n b : ℕ} (Z : Set (GeometricPoint n)) (hZ : AlgebraicallyClosedSet Z)
    (hprod : GeometricallyIrreducible (affineCylinder Z b)) :
    affineDimension (affineCylinder Z b) = affineDimension Z + (b : Dimension) := by
  have he : polynomialMap (linearCoordinatePolynomials (baseProjection n b)) =
      baseProjection n b := funext (polynomialMap_linearCoordinatePolynomials _)
  have hc : AlgebraicallyClosedSet (affineCylinder Z b) := by
    simpa only [he] using
      closed_polynomial_preimage (linearCoordinatePolynomials (baseProjection n b)) hZ
  obtain ⟨G⟩ := GR.choose (affineCylinder Z b) hc hprod
    (linearCoordinatePolynomials (baseProjection n b))
    (0 : GeometricPoint (n+b) →ₗ[GeometricField] Matrix (Fin 0) (Fin 0) GeometricField)
  obtain ⟨x, hx⟩ := G.nonempty
  have hdim := ((baseProjection n b).domRestrict
    (affineTangentSpace (affineCylinder Z b) x)).finrank_range_add_finrank_ker
  rw [tangent_projection_kernel_dimension Z x (G.subset hx), G.smooth x hx] at hdim
  have hr := G.differential_rank x hx
  rw [differential_linearCoordinates] at hr
  rw [hr] at hdim
  have hz := G.dimension_image
  rw [cylinder_image_base, affineDimension_closure] at hz
  rw [G.dimension_base, hz, ← hdim]
  norm_cast

theorem affineCylinder_eq_product_image {n b : ℕ} (Z : Set (GeometricPoint n)) :
    affineCylinder Z b = (pairCoordinateEquiv n b) ''
      ReducedAffineProduct.affineProduct (τ := Fin b) Z := by
  ext x
  constructor
  · intro hx
    refine ⟨(pairCoordinateEquiv n b).symm x, ?_, (pairCoordinateEquiv n b).apply_symm_apply x⟩
    have h := baseProjection_pair ((pairCoordinateEquiv n b).symm x)
    rw [LinearEquiv.apply_symm_apply] at h
    change pairLeft ((pairCoordinateEquiv n b).symm x) ∈ Z
    exact h ▸ hx
  · rintro ⟨p, hp, rfl⟩
    change baseProjection n b (pairCoordinateEquiv n b p) ∈ Z
    simpa only [baseProjection_pair] using hp

theorem affineCylinder_irreducible {n b : ℕ} (Z : Set (GeometricPoint n))
    (hi : GeometricallyIrreducible Z) : GeometricallyIrreducible (affineCylinder Z b) := by
  rw [affineCylinder_eq_product_image]
  let E := PolynomialCoordinateEquiv.ofLinearEquiv (pairCoordinateEquiv n b)
  have h := (E.geometricallyIrreducible_image_iff _).mpr
    (ReducedAffineProduct.affineProduct_irreducible (τ := Fin b) Z hi)
  simpa only [E, PolynomialCoordinateEquiv.ofLinearEquiv_forwardMap] using h

/-- Actual finite-coordinate product dimension from GR alone. Product
irreducibility is proved from polynomial specialization, not assumed. -/
theorem affineCylinder_dimension (GR : GenericRankOpenInput) {n b : ℕ}
    (Z : Set (GeometricPoint n)) (hZ : AlgebraicallyClosedSet Z)
    (hi : GeometricallyIrreducible Z) :
    affineDimension (affineCylinder Z b) = affineDimension Z + (b : Dimension) :=
  affineCylinder_dimension_of_irreducible GR Z hZ (affineCylinder_irreducible Z hi)

theorem affineProduct_dimension (GR : GenericRankOpenInput) {n b : ℕ}
    (Z : Set (GeometricPoint n)) (hZ : AlgebraicallyClosedSet Z)
    (hi : GeometricallyIrreducible Z) :
    affineDimension (ReducedAffineProduct.affineProduct (τ := Fin b) Z) =
      affineDimension Z + (b : Dimension) := by
  have h := affineCylinder_dimension (b := b) GR Z hZ hi
  rw [affineCylinder_eq_product_image] at h
  let E := PolynomialCoordinateEquiv.ofLinearEquiv (pairCoordinateEquiv n b)
  have he := E.affineDimension_image (ReducedAffineProduct.affineProduct (τ := Fin b) Z)
  simp only [E, PolynomialCoordinateEquiv.ofLinearEquiv_forwardMap] at he
  rwa [he] at h

end HessianTheorem11.ReducedAffineProductDimension
