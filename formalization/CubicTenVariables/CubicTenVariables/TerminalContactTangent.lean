import HessianTheorem11.ReducedGenericImageTangent
import HessianTheorem11.ReducedDeterminantalDifferential
import HessianTheorem11.KernelGradientSpan
import HessianTheorem11.BibleHyperplanes

/-!
The contact-tangent calculation used in the rational terminal-stratum bound.
The incidence relations below are literal polynomial equations on a set Y;
their derivatives vanish on its actual reduced Zariski tangent space.
Surjectivity onto a specified base tangent space is an explicit pointwise
hypothesis. This module does not assert generic smoothness, the existence of
a rational point with that property, or a terminal-stratum dimension bound.
-/

noncomputable section
namespace CubicTenVariables.TerminalContactTangent
open MvPolynomial HessianTheorem11 Module
open HessianTheorem11.ReducedGenericImageTangent
open HessianTheorem11.ReducedDeterminantal

variable {m n : ℕ}

/-- The actual scalar product of two polynomial vector maps. -/
def pairingPolynomial (P Q : Fin n → GeometricPolynomial m) : GeometricPolynomial m :=
  ∑ i, Q i * P i

theorem eval_pairingPolynomial (P Q : Fin n → GeometricPolynomial m)
    (y : GeometricPoint m) :
    eval y (pairingPolynomial P Q) =
      dotProduct (polynomialMap Q y) (polynomialMap P y) := by
  simp [pairingPolynomial, dotProduct, polynomialMap]

theorem differential_pairingPolynomial (P Q : Fin n → GeometricPolynomial m)
    (y u : GeometricPoint m) :
    polynomialDifferential (pairingPolynomial P Q) y u =
      dotProduct (polynomialMapDifferential Q y u) (polynomialMap P y) +
      dotProduct (polynomialMap Q y) (polynomialMapDifferential P y u) := by
  change differentialAt y u (∑ i, Q i * P i) = _
  rw [map_sum]
  simp only [differentialAt_apply, ReducedTangentRank.differential_mul,
    Finset.sum_add_distrib]
  simp [dotProduct, polynomialMapDifferential, polynomialMap, mul_comm]

/-- Differentiate F(P)=0 and Q·P=0 at an actual tangent vector of Y. -/
theorem incidence_tangent_equations (F : GeometricPolynomial n)
    (P Q : Fin n → GeometricPolynomial m) (Y : Set (GeometricPoint m))
    (hF : ∀ y ∈ Y, eval (polynomialMap P y) F = 0)
    (hpair : ∀ y ∈ Y, dotProduct (polynomialMap Q y) (polynomialMap P y) = 0)
    (y u : GeometricPoint m) (hu : u ∈ affineTangentSpace Y y) :
    dotProduct (gradient F (polynomialMap P y)) (polynomialMapDifferential P y u) = 0 ∧
      dotProduct (polynomialMapDifferential Q y u) (polynomialMap P y) +
        dotProduct (polynomialMap Q y) (polynomialMapDifferential P y u) = 0 := by
  constructor
  · have hz : aeval P F ∈ vanishingIdeal GeometricField Y := by
      intro z hz
      change eval z (aeval P F) = 0
      rw [← eval_polynomialMap]
      exact hF z hz
    have hd := mem_affineTangentSpace.mp hu _ hz
    rw [differential_aeval] at hd
    simpa only [polynomialDifferential_apply, dotProduct, gradient] using hd
  · have hz : pairingPolynomial P Q ∈ vanishingIdeal GeometricField Y := by
      intro z hz
      change eval z (pairingPolynomial P Q) = 0
      rw [eval_pairingPolynomial]
      exact hpair z hz
    have hd := mem_affineTangentSpace.mp hu _ hz
    rwa [differential_pairingPolynomial] at hd

/-- At a nonsingular contact point, every lifted base tangent annihilates x. -/
theorem base_tangent_annihilates_point (F : GeometricPolynomial n)
    (P Q : Fin n → GeometricPolynomial m) (Y : Set (GeometricPoint m))
    (hF : ∀ y ∈ Y, eval (polynomialMap P y) F = 0)
    (hpair : ∀ y ∈ Y, dotProduct (polynomialMap Q y) (polynomialMap P y) = 0)
    (y : GeometricPoint m) (α : GeometricField) (hα : α ≠ 0)
    (hgrad : gradient F (polynomialMap P y) = α • polynomialMap Q y)
    (w : GeometricPoint n)
    (hw : w ∈ LinearMap.range ((polynomialMapDifferential Q y).domRestrict
      (affineTangentSpace Y y))) :
    dotProduct w (polynomialMap P y) = 0 := by
  obtain ⟨u, rfl⟩ := hw
  obtain ⟨hzero, hcontact⟩ := incidence_tangent_equations F P Q Y hF hpair y u u.property
  rw [hgrad, smul_dotProduct, smul_eq_mul] at hzero
  have hzero' := (mul_eq_zero.mp hzero).resolve_left hα
  simpa only [hzero', add_zero] using hcontact

/-- The point lies in the annihilator of the base tangent, and its gradient
annihilates that subspace. The equation F=0 at the point additionally follows
from hF whenever y belongs to Y. -/
theorem contact_restriction_singular (F : GeometricPolynomial n)
    (P Q : Fin n → GeometricPolynomial m) (Y : Set (GeometricPoint m))
    (hF : ∀ y ∈ Y, eval (polynomialMap P y) F = 0)
    (hpair : ∀ y ∈ Y, dotProduct (polynomialMap Q y) (polynomialMap P y) = 0)
    (y : GeometricPoint m) (α : GeometricField) (hα : α ≠ 0)
    (hgrad : gradient F (polynomialMap P y) = α • polynomialMap Q y)
    (T : Submodule GeometricField (GeometricPoint n))
    (hlift : T ≤ LinearMap.range ((polynomialMapDifferential Q y).domRestrict
      (affineTangentSpace Y y)))
    (hradial : polynomialMap Q y ∈ T) :
    polynomialMap P y ∈ coordinatePairing.orthogonal T ∧
      ∀ z ∈ coordinatePairing.orthogonal T,
        dotProduct z (gradient F (polynomialMap P y)) = 0 := by
  constructor
  · intro w hw
    exact base_tangent_annihilates_point F P Q Y hF hpair y α hα hgrad w (hlift hw)
  · intro z hz
    have hvz : dotProduct (polynomialMap Q y) z = 0 := hz _ hradial
    rw [hgrad, dotProduct_smul, dotProduct_comm, hvz, smul_zero]

/-- The annihilator has the expected complementary dimension. -/
theorem finrank_contact_annihilator (T : Submodule GeometricField (GeometricPoint n)) :
    finrank GeometricField (coordinatePairing.orthogonal T) =
      n - finrank GeometricField T := by
  rw [LinearMap.BilinForm.finrank_orthogonal coordinatePairing_nondegenerate
    coordinatePairing_reflexive]
  simp

/-- In every frame spanning the annihilator, the contact point is the
image of an actual critical point of the restricted polynomial. The
`singularCone` here is defined by gradient zero; no equation F=0 is asserted
without the additional condition y ∈ Y. -/
theorem contact_point_mem_restricted_singular_image (F : GeometricPolynomial n)
    (P Q : Fin n → GeometricPolynomial m) (Y : Set (GeometricPoint m))
    (hF : ∀ y ∈ Y, eval (polynomialMap P y) F = 0)
    (hpair : ∀ y ∈ Y, dotProduct (polynomialMap Q y) (polynomialMap P y) = 0)
    (y : GeometricPoint m) (α : GeometricField) (hα : α ≠ 0)
    (hgrad : gradient F (polynomialMap P y) = α • polynomialMap Q y)
    (T : Submodule GeometricField (GeometricPoint n))
    (hlift : T ≤ LinearMap.range ((polynomialMapDifferential Q y).domRestrict
      (affineTangentSpace Y y)))
    (hradial : polynomialMap Q y ∈ T)
    {d : ℕ} (B : Matrix (Fin n) (Fin d) GeometricField)
    (hB : LinearMap.range B.mulVecLin = coordinatePairing.orthogonal T) :
    polynomialMap P y ∈ B.mulVec ''
      BibleHyperplanes.singularCone (PolynomialRestriction.restrict B F) := by
  obtain ⟨hpoint, hsing⟩ :=
    contact_restriction_singular F P Q Y hF hpair y α hα hgrad T hlift hradial
  rw [BibleHyperplanes.frame_singular_image, hB]
  exact ⟨hpoint, hsing⟩

end CubicTenVariables.TerminalContactTangent
