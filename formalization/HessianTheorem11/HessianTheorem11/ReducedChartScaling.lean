import HessianTheorem11.ReducedAffineProductDimension
import HessianTheorem11.ReducedGenericImageTangent
import HessianTheorem11.ReducedKernelTangent
import HessianTheorem11.ReducedComponentDimension

/-! The actual scaling image of a closed irreducible normalized affine
chart has dimension one larger. Only GR is used. -/
noncomputable section
namespace HessianTheorem11.ReducedChartScaling
open MvPolynomial Module ReducedKernelTangent ReducedGenericImageTangent
  ReducedTangentRank

def scalarCoordinate (n : ℕ) : GeometricPoint (n+1) →ₗ[GeometricField] GeometricField :=
  (LinearMap.proj 0).comp (fiberProjection n 1)

def baseCoordinate {n : ℕ} (i : Fin n) :
    GeometricPoint (n+1) →ₗ[GeometricField] GeometricField :=
  (LinearMap.proj i).comp (baseProjection n 1)

def scalePolynomials (n : ℕ) : Fin n → GeometricPolynomial (n+1) :=
  fun i => linearPolynomial (scalarCoordinate n) * linearPolynomial (baseCoordinate i)

@[simp] theorem polynomialMap_scale (n : ℕ) (x : GeometricPoint (n+1)) :
    polynomialMap (scalePolynomials n) x = scalarCoordinate n x • baseProjection n 1 x := by
  ext i
  simp [polynomialMap, scalePolynomials, baseCoordinate]

@[simp] theorem differential_scale (n : ℕ) (x v : GeometricPoint (n+1)) :
    polynomialMapDifferential (scalePolynomials n) x v =
      scalarCoordinate n x • baseProjection n 1 v +
        scalarCoordinate n v • baseProjection n 1 x := by
  ext i
  simp [polynomialMapDifferential, scalePolynomials, differential_mul, baseCoordinate]
  ring

def cylinder {n : ℕ} (S : Set (GeometricPoint n)) : Set (GeometricPoint (n+1)) :=
  baseProjection n 1 ⁻¹' S

def scaledImage {n : ℕ} (S : Set (GeometricPoint n)) : Set (GeometricPoint n) :=
  {x | ∃ s ∈ S, ∃ a : GeometricField, a • s = x}

theorem cylinder_eq_bundle {n : ℕ} (S : Set (GeometricPoint n)) :
    cylinder S = (pairCoordinateEquiv n 1) '' kernelBundle
      (0 : GeometricPoint n →ₗ[GeometricField] Matrix (Fin 0) (Fin 1) GeometricField) S := by
  ext x
  constructor
  · intro hx
    refine ⟨(pairCoordinateEquiv n 1).symm x, ?_, (pairCoordinateEquiv n 1).apply_symm_apply x⟩
    refine ⟨?_, ?_⟩
    · have h := baseProjection_pair ((pairCoordinateEquiv n 1).symm x)
      rw [LinearEquiv.apply_symm_apply] at h
      exact h ▸ hx
    · ext i; exact Fin.elim0 i
  · rintro ⟨p, hp, rfl⟩
    change baseProjection n 1 (pairCoordinateEquiv n 1 p) ∈ S
    simpa only [baseProjection_pair] using hp.1

theorem cylinder_closed {n : ℕ} (S : Set (GeometricPoint n))
    (hS : AlgebraicallyClosedSet S) : AlgebraicallyClosedSet (cylinder S) := by
  have he : polynomialMap (linearCoordinatePolynomials (baseProjection n 1)) =
      baseProjection n 1 := funext (polynomialMap_linearCoordinatePolynomials _)
  simpa only [he] using
    closed_polynomial_preimage (linearCoordinatePolynomials (baseProjection n 1)) hS

theorem cylinder_irreducible {n : ℕ}
    (S : Set (GeometricPoint n))
    (hi : GeometricallyIrreducible S) : GeometricallyIrreducible (cylinder S) := by
  exact ReducedAffineProductDimension.affineCylinder_irreducible S hi

theorem cylinder_dimension (GR : GenericRankOpenInput) {n : ℕ}
    (S : Set (GeometricPoint n)) (hS : AlgebraicallyClosedSet S)
    (hi : GeometricallyIrreducible S) :
    affineDimension (cylinder S) = affineDimension S + 1 := by
  exact ReducedAffineProductDimension.affineCylinder_dimension GR S hS hi

theorem scale_image {n : ℕ} (S : Set (GeometricPoint n)) :
    polynomialMap (scalePolynomials n) '' cylinder S = scaledImage S := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨baseProjection n 1 y, hy, scalarCoordinate n y, (polynomialMap_scale n y).symm⟩
  · rintro ⟨s, hs, a, rfl⟩
    refine ⟨pairCoordinateEquiv n 1 (pairPoint s (fun _ => a)), ?_, ?_⟩
    · simpa [cylinder] using hs
    · simp [scalarCoordinate]

theorem tangent_coordinate_zero {n : ℕ} (S : Set (GeometricPoint n))
    (i : Fin n) (hi : ∀ s ∈ S, s i = 1) (x v : GeometricPoint (n+1))
    (hv : v ∈ affineTangentSpace (cylinder S) x) : baseCoordinate i v = 0 := by
  have hvan : linearPolynomial (baseCoordinate i) - 1 ∈
      vanishingIdeal GeometricField (cylinder S) := by
    intro y hy
    change eval y (linearPolynomial (baseCoordinate i) - 1) = 0
    simp only [map_sub, map_one, eval_linearPolynomial, baseCoordinate, LinearMap.comp_apply,
      LinearMap.proj_apply]
    exact sub_eq_zero.mpr (hi _ hy)
  have h := mem_affineTangentSpace.mp hv _ hvan
  have he : polynomialDifferential (linearPolynomial (baseCoordinate i) - 1) x v =
      polynomialDifferential (linearPolynomial (baseCoordinate i)) x v := by
    simp only [polynomialDifferential_apply, map_sub, pderiv_one, sub_zero]
  rw [he, differential_linearPolynomial] at h
  exact h

theorem differential_scale_injective {n : ℕ} (S : Set (GeometricPoint n))
    (i : Fin n) (hi : ∀ s ∈ S, s i = 1) (x : GeometricPoint (n+1))
    (hx : x ∈ cylinder S) (ht : scalarCoordinate n x ≠ 0) :
    Function.Injective ((polynomialMapDifferential (scalePolynomials n) x).domRestrict
      (affineTangentSpace (cylinder S) x)) := by
  apply (LinearMap.ker_eq_bot).mp
  apply eq_bot_iff.mpr
  intro v hv
  have hz : polynomialMapDifferential (scalePolynomials n) x v = 0 := hv
  rw [differential_scale] at hz
  have hvi := tangent_coordinate_zero S i hi x v v.property
  have hxi := hi _ hx
  have hscalar : scalarCoordinate n v = 0 := by
    have h := congrFun hz i
    simpa only [Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      show baseProjection n 1 v i = 0 from hvi, hxi, mul_zero, zero_add, mul_one,
      Pi.zero_apply] using h
  have hbase : baseProjection n 1 v = 0 := by
    rw [hscalar, zero_smul, add_zero] at hz
    exact (smul_eq_zero.mp hz).resolve_left ht
  apply Subtype.ext
  apply (splitEquiv n 1).injective
  apply Prod.ext
  · exact hbase
  · ext j
    have hj : j = 0 := Subsingleton.elim _ _
    subst j
    exact hscalar

/-- The scaling map on an irreducible normalized chart has generically
injective differential, so GR and the proved product dimension suffice. -/
theorem scaledImage_dimension_irreducible (GR : GenericRankOpenInput)
    {n : ℕ} (S : Set (GeometricPoint n))
    (hS : AlgebraicallyClosedSet S) (hiS : GeometricallyIrreducible S)
    (i : Fin n) (hnorm : ∀ s ∈ S, s i = 1) :
    affineDimension (scaledImage S) = affineDimension S + 1 := by
  obtain ⟨G⟩ := GR.choose (cylinder S) (cylinder_closed S hS)
    (cylinder_irreducible S hiS) (scalePolynomials n)
    (0 : GeometricPoint (n+1) →ₗ[GeometricField] Matrix (Fin 0) (Fin 0) GeometricField)
  have hex : ∃ x ∈ cylinder S, eval x (linearPolynomial (scalarCoordinate n)) ≠ 0 := by
    obtain ⟨s, hs⟩ := hiS.nonempty
    refine ⟨pairCoordinateEquiv n 1 (pairPoint s (fun _ => 1)), ?_, ?_⟩
    · simpa [cylinder] using hs
    · simp [scalarCoordinate]
  have hgeneric : ∃ x ∈ G.openSet, eval x (linearPolynomial (scalarCoordinate n)) ≠ 0 := by
    by_contra hn
    push_neg at hn
    obtain ⟨x, hx, he⟩ := hex
    exact he ((G.dense ▸ hx) _ hn)
  obtain ⟨x, hx, ht⟩ := hgeneric
  have hinj := differential_scale_injective S i hnorm x (G.subset hx)
    (by simpa only [eval_linearPolynomial] using ht)
  have he : G.imageDimension = G.baseDimension := by
    rw [← G.differential_rank x hx, LinearMap.finrank_range_of_inj hinj, G.smooth x hx]
  have hd := G.dimension_image
  rw [scale_image, affineDimension_closure, he, ← G.dimension_base] at hd
  exact hd.trans (cylinder_dimension GR S hS hiS)

end HessianTheorem11.ReducedChartScaling
