import CubicTenVariables.TerminalRationalContact
import HessianTheorem11.LinearEmbeddingGeometry
import HessianTheorem11.UnconditionalFiberDimension

/-!
Actual point/normal coordinates preserve the dimension of every fixed-normal
fiber. The inverse is the polynomial section x ↦ (x,v), so this is stronger
than a set-theoretic bijection. Contact containment then transfers the full
fiber dimension to the singular locus of the actual rational restriction.
-/

noncomputable section
namespace CubicTenVariables.TerminalFiberCoordinates

open MvPolynomial HessianTheorem11 PolynomialRestriction
open TerminalSectionIncidence

/-- The point-coordinate projection in the actual two-block affine space. -/
def pointProjection (n : ℕ) : Fin n → GeometricPolynomial (n + n) :=
  fun i => X (Fin.castAdd n i)

/-- The normal-coordinate projection in the actual two-block affine space. -/
def normalProjection (n : ℕ) : Fin n → GeometricPolynomial (n + n) :=
  fun i => X (Fin.natAdd n i)

/-- The polynomial section with a fixed, actual normal. -/
def fixedNormalSection {n : ℕ} (v : GeometricPoint n) :
    Fin (n + n) → GeometricPolynomial n :=
  Fin.addCases X (fun i => C (v i))

@[simp] theorem pointProjection_apply {n : ℕ} (z : GeometricPoint (n + n)) (i : Fin n) :
    polynomialMap (pointProjection n) z i = z (Fin.castAdd n i) := by
  simp [pointProjection, polynomialMap]

@[simp] theorem normalProjection_apply {n : ℕ} (z : GeometricPoint (n + n)) (i : Fin n) :
    polynomialMap (normalProjection n) z i = z (Fin.natAdd n i) := by
  simp [normalProjection, polynomialMap]

@[simp] theorem pointProjection_section {n : ℕ} (v x : GeometricPoint n) :
    polynomialMap (pointProjection n) (polynomialMap (fixedNormalSection v) x) = x := by
  ext i
  simp [fixedNormalSection, polynomialMap, pointProjection]

@[simp] theorem normalProjection_section {n : ℕ} (v x : GeometricPoint n) :
    polynomialMap (normalProjection n) (polynomialMap (fixedNormalSection v) x) = v := by
  ext i
  simp only [fixedNormalSection, polynomialMap, normalProjection, eval_X,
    Fin.addCases_right, eval_C]

theorem section_pointProjection {n : ℕ} (v : GeometricPoint n)
    (z : GeometricPoint (n + n)) (hz : polynomialMap (normalProjection n) z = v) :
    polynomialMap (fixedNormalSection v) (polynomialMap (pointProjection n) z) = z := by
  ext i
  refine Fin.addCases ?_ ?_ i
  · intro j
    simp [fixedNormalSection, polynomialMap, pointProjection]
  · intro j
    have hj := congrFun hz j
    simpa only [fixedNormalSection, polynomialMap, normalProjection, eval_X,
      Fin.addCases_right, eval_C] using hj.symm

/-- Even an arbitrary subset of a fixed-normal fiber has the same reduced
Zariski dimension as its actual point image. No closedness is needed. -/
theorem fixed_normal_dimension {n : ℕ} (R : Set (GeometricPoint (n + n)))
    (v : GeometricPoint n) (hR : ∀ z ∈ R, polynomialMap (normalProjection n) z = v) :
    affineDimension (polynomialMap (pointProjection n) '' R) = affineDimension R := by
  have he : polynomialMap (fixedNormalSection v) ''
      (polynomialMap (pointProjection n) '' R) = R := by
    ext z
    constructor
    · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
      simpa only [section_pointProjection v y (hR y hy)] using hy
    · intro hz
      exact ⟨polynomialMap (pointProjection n) z, ⟨z, hz, rfl⟩,
        section_pointProjection v z (hR z hz)⟩
  have hd := affineDimension_image_of_polynomial_leftInverse
    (fixedNormalSection v) (pointProjection n) (pointProjection_section v)
    (polynomialMap (pointProjection n) '' R)
  rw [he] at hd
  exact hd.symm

/-- The actual source-open fiber, including empty fibers. -/
theorem fiber_dimension {n : ℕ} (U : Set (GeometricPoint (n + n)))
    (v : GeometricPoint n) :
    affineDimension (polynomialMap (pointProjection n) ''
      {y | y ∈ U ∧ polynomialMap (normalProjection n) y = v}) =
    affineDimension {y | y ∈ U ∧ polynomialMap (normalProjection n) y = v} :=
  fixed_normal_dimension _ v (fun _ hy => hy.2)

/-- Actual contact containment in an injective rational frame transfers
fiber dimension into the actual singular locus of that restriction. -/
theorem contact_fiber_dimension_le {n d : ℕ} (F : RationalPolynomial n)
    (U : Set (GeometricPoint (n + n))) (v : GeometricPoint n)
    (B : Matrix (Fin n) (Fin d) ℚ)
    (hB : Function.Injective (B.map (algebraMap ℚ GeometricField)).mulVec)
    (hcontact : ∀ y ∈ U, polynomialMap (normalProjection n) y = v →
      polynomialMap (pointProjection n) y ∈ (B.map (algebraMap ℚ GeometricField)).mulVec ''
        hypersurfaceSingularLocus (geometricPolynomial (restrict B F))) :
    affineDimension {y | y ∈ U ∧ polynomialMap (normalProjection n) y = v} ≤
      singularDimension (restrict B F) := by
  rw [← fiber_dimension U v]
  have hsub : polynomialMap (pointProjection n) ''
      {y | y ∈ U ∧ polynomialMap (normalProjection n) y = v} ⊆
      (B.map (algebraMap ℚ GeometricField)).mulVec '' singularLocus (restrict B F) := by
    rintro _ ⟨y, ⟨hy, hyv⟩, rfl⟩
    obtain ⟨x, hx, hxy⟩ := hcontact y hy hyv
    exact ⟨x, hx.2, hxy⟩
  have hd := affineDimension_mono hsub
  exact hd.trans_eq (affineDimension_linearMap_image
    (B.map (algebraMap ℚ GeometricField)).mulVecLin hB _)

/-- The source dimension inequality now reaches the actual rational
restriction. The family is supplied; no existence of a sufficiently large
incidence component is asserted here. -/
theorem source_dimension_le_restriction {n d : ℕ} (F : RationalPolynomial n)
    (Y U : Set (GeometricPoint (n + n)))
    (hY : AlgebraicallyClosedSet Y) (hiY : GeometricallyIrreducible Y)
    (hU : RelativelyOpenSet Y U) (v : GeometricPoint n)
    (hne : {y | y ∈ U ∧ polynomialMap (normalProjection n) y = v}.Nonempty)
    (B : Matrix (Fin n) (Fin d) ℚ)
    (hB : Function.Injective (B.map (algebraMap ℚ GeometricField)).mulVec)
    (hcontact : ∀ y ∈ U, polynomialMap (normalProjection n) y = v →
      polynomialMap (pointProjection n) y ∈ (B.map (algebraMap ℚ GeometricField)).mulVec ''
        hypersurfaceSingularLocus (geometricPolynomial (restrict B F))) :
    affineDimension Y ≤ affineDimension (polynomialMap (normalProjection n) '' Y) +
      singularDimension (restrict B F) := by
  obtain ⟨y, hy, hyv⟩ := hne
  have hf := UnconditionalFiberDimension.open_fiber_dimension
    (normalProjection n) Y U hY hiY hU y hy
  rw [hyv] at hf
  exact hf.trans (add_le_add_right (contact_fiber_dimension_le F U v B hB hcontact) _)

end CubicTenVariables.TerminalFiberCoordinates
