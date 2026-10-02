import CubicTenVariables.AffineProductGeometry

/-!
# The wholly singular product-family branch

The actual product theorem extends the incidence pairing equation to every
pair of points in the two projection closures. Its linear equation in the
normal variable annihilates the actual reduced tangent at every ambient
base point. A gradient-zero condition on the source extends to its point
image closure; for a homogeneous cubic Euler's identity retains F=0.
Every frame spanning the tangent annihilator therefore contains this whole
point-image closure in the image of the actual restricted hypersurface
singular locus. No generic contact or tangent-surjectivity premise is used.
-/

noncomputable section
namespace CubicTenVariables.SingularFamilyProduct
open MvPolynomial HessianTheorem11 Module PolynomialRestriction
open TerminalFiberCoordinates TerminalSectionIncidence AffineProductGeometry

/-- A linear equation vanishing on a set annihilates its actual reduced
Zariski tangent, at every ambient point. No smoothness is required. -/
theorem mem_tangent_annihilator_of_pairing_zero {n : ℕ}
    (Z : Set (GeometricPoint n)) (x v : GeometricPoint n)
    (hpair : ∀ z ∈ Z, dotProduct z x = 0) :
    x ∈ coordinatePairing.orthogonal (affineTangentSpace Z v) := by
  let B : Matrix Unit (Fin n) GeometricField := fun _ i => x i
  have hlin : linearForms B () ∈ vanishingIdeal GeometricField Z := by
    intro z hz
    change eval z (linearForms B ()) = 0
    rw [eval_linearForms]
    change dotProduct x z = 0
    rw [dotProduct_comm]
    exact hpair z hz
  intro w hw
  have hd := mem_affineTangentSpace.mp hw _ hlin
  change dotProduct w x = 0
  rw [dotProduct_comm]
  simpa only [polynomialDifferential_apply, pderiv_linearForms, eval_C, B, dotProduct] using hd

/-- Once the actual dimension hypothesis forces a product, the pairing
incidence holds for every pair from the actual two image closures. -/
theorem family_pairing_zero {n : ℕ} (Y : Set (GeometricPoint (n+n)))
    (hY : AlgebraicallyClosedSet Y) (hiY : GeometricallyIrreducible Y)
    (hdim : affineDimension (geometricClosure (polynomialMap (pointProjection n) '' Y)) +
      affineDimension (geometricClosure (polynomialMap (normalProjection n) '' Y)) ≤
        affineDimension Y)
    (hpair : ∀ y ∈ Y, dotProduct (polynomialMap (normalProjection n) y)
      (polynomialMap (pointProjection n) y) = 0)
    (x v : GeometricPoint n)
    (hx : x ∈ geometricClosure (polynomialMap (pointProjection n) '' Y))
    (hv : v ∈ geometricClosure (polynomialMap (normalProjection n) '' Y)) :
    dotProduct v x = 0 := by
  have he := eq_product_of_image_dimensions Y hY hiY hdim
  have hjoin : join x v ∈ Y := by
    rw [he]
    exact (join_mem_product _ _ x v).mpr ⟨hx, hv⟩
  simpa only [point_join, normal_join] using hpair (join x v) hjoin

/-- Every point of the first image closure annihilates the tangent of the
second image closure at every ambient point, including singular points. -/
theorem family_point_mem_tangent_annihilator {n : ℕ}
    (Y : Set (GeometricPoint (n+n)))
    (hY : AlgebraicallyClosedSet Y) (hiY : GeometricallyIrreducible Y)
    (hdim : affineDimension (geometricClosure (polynomialMap (pointProjection n) '' Y)) +
      affineDimension (geometricClosure (polynomialMap (normalProjection n) '' Y)) ≤
        affineDimension Y)
    (hpair : ∀ y ∈ Y, dotProduct (polynomialMap (normalProjection n) y)
      (polynomialMap (pointProjection n) y) = 0)
    (v x : GeometricPoint n)
    (hx : x ∈ geometricClosure (polynomialMap (pointProjection n) '' Y)) :
    x ∈ coordinatePairing.orthogonal
      (affineTangentSpace (geometricClosure (polynomialMap (normalProjection n) '' Y)) v) :=
  mem_tangent_annihilator_of_pairing_zero _ x v
    (fun z hz => family_pairing_zero Y hY hiY hdim hpair x z hx hz)

/-- The actual closed gradient-zero locus contains the closure of any
polynomial image on which the gradient vanishes. -/
theorem gradient_zero_on_image_closure {m n : ℕ} (F : GeometricPolynomial n)
    (P : Fin n → GeometricPolynomial m) (Y : Set (GeometricPoint m))
    (hgradient : ∀ y ∈ Y, gradient F (polynomialMap P y) = 0)
    (x : GeometricPoint n) (hx : x ∈ geometricClosure (polynomialMap P '' Y)) :
    gradient F x = 0 := by
  have hsub : polynomialMap P '' Y ⊆ BibleHyperplanes.singularCone F := by
    rintro _ ⟨y, hy, rfl⟩
    exact hgradient y hy
  exact geometricClosure_subset_closed hsub (BibleHyperplanes.singularCone_closed F) hx

/-- Euler retains the cubic equation on the gradient-zero locus. -/
theorem cubic_eval_zero_of_gradient_zero {n : ℕ} (F : GeometricPolynomial n)
    (hF : F.IsHomogeneous 3) (x : GeometricPoint n) (hx : gradient F x = 0) :
    eval x F = 0 := by
  have he := euler_cubic hF x
  change dotProduct x (gradient F x) = 3 * eval x F at he
  rw [hx, dotProduct_zero] at he
  exact (mul_eq_zero.mp he.symm).resolve_left (by norm_num)

/-- An actual singular point lying in the range of a frame remains a
singular point of the actual polynomial restriction. Both the equation
and the gradient are retained; frame injectivity is unnecessary here. -/
theorem mem_restricted_singular_image_of_mem_range {n d : ℕ}
    (F : GeometricPolynomial n) (B : Matrix (Fin n) (Fin d) GeometricField)
    (x : GeometricPoint n) (hx : x ∈ LinearMap.range B.mulVecLin)
    (hzero : eval x F = 0) (hgradient : gradient F x = 0) :
    x ∈ B.mulVec '' hypersurfaceSingularLocus (restrict B F) := by
  obtain ⟨u, hu⟩ := hx
  change B.mulVec u = x at hu
  refine ⟨u, ⟨?_, ?_⟩, hu⟩
  · rw [eval_restrict, hu]
    exact hzero
  · rw [BibleHyperplanes.gradient_restrict, hu, hgradient, Matrix.mulVec_zero]

/-- The entire point-image closure of a sufficiently large wholly
singular family belongs to the singular locus of the actual restriction
in any frame of the normal-image tangent annihilator. The conclusion
holds at every ambient normal v and retains F=0 via Euler's identity. -/
theorem family_mem_restricted_singular_image {n : ℕ}
    (F : GeometricPolynomial n) (hF : F.IsHomogeneous 3)
    (Y : Set (GeometricPoint (n+n)))
    (hY : AlgebraicallyClosedSet Y) (hiY : GeometricallyIrreducible Y)
    (hdim : affineDimension (geometricClosure (polynomialMap (pointProjection n) '' Y)) +
      affineDimension (geometricClosure (polynomialMap (normalProjection n) '' Y)) ≤
        affineDimension Y)
    (hpair : ∀ y ∈ Y, dotProduct (polynomialMap (normalProjection n) y)
      (polynomialMap (pointProjection n) y) = 0)
    (hgradient : ∀ y ∈ Y, gradient F (polynomialMap (pointProjection n) y) = 0)
    (v : GeometricPoint n) {d : ℕ} (B : Matrix (Fin n) (Fin d) GeometricField)
    (hB : LinearMap.range B.mulVecLin = coordinatePairing.orthogonal
      (affineTangentSpace (geometricClosure (polynomialMap (normalProjection n) '' Y)) v)) :
    geometricClosure (polynomialMap (pointProjection n) '' Y) ⊆
      B.mulVec '' hypersurfaceSingularLocus (restrict B F) := by
  intro x hx
  have hann := family_point_mem_tangent_annihilator Y hY hiY hdim hpair v x hx
  have hg := gradient_zero_on_image_closure F (pointProjection n) Y hgradient x hx
  exact mem_restricted_singular_image_of_mem_range F B x (hB ▸ hann)
    (cubic_eval_zero_of_gradient_zero F hF x hg) hg

end CubicTenVariables.SingularFamilyProduct
