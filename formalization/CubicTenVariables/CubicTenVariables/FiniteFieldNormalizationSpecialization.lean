import CubicTenVariables.PolynomialNormalizationSpecialization
import CubicTenVariables.GeometricEquationDimensionProved
import Mathlib.RingTheory.IntegralDomain

/-! An injective integral normalization retains its parameter dimension
after an arbitrary specialization into a finite field. The coefficient map
need not be surjective: its finite image is itself a field, and extension
from that image preserves the actual quotient dimension. -/

set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.FiniteFieldNormalizationSpecialization
open MvPolynomial PolynomialNormalizationSpecialization

/-- The number of actual normalization coordinates is bounded by the
dimension of every finite-field specialization, including extension fields. -/
theorem normalization_parameter_le
    {B L : Type*} [CommRing B] [Field L] [Finite L] {N d j : ℕ}
    (I : Ideal (MvPolynomial (Fin N) B)) (q : Fin d → MvPolynomial (Fin N) B)
    (hinj : Function.Injective (normalizationHom I q))
    (hint : (normalizationHom I q).toRingHom.IsIntegral)
    (ρ : B →+* L)
    (hdim : ringKrullDim (MvPolynomial (Fin N) L ⧸ I.map (MvPolynomial.map ρ)) ≤
      (j : WithBot ℕ∞)) : d ≤ j := by
  classical
  let K := ρ.range
  letI : Fintype K := Fintype.ofFinite K
  letI : Field K := Fintype.fieldOfDomain K
  let τ : K →+* L := ρ.range.subtype
  letI : Algebra K L := τ.toAlgebra
  let J := I.map (MvPolynomial.map ρ.rangeRestrict)
  have hcomp : τ.comp ρ.rangeRestrict = ρ := rfl
  have hmap : J.map (MvPolynomial.map (algebraMap K L)) =
      I.map (MvPolynomial.map ρ) := by
    change (I.map (MvPolynomial.map ρ.rangeRestrict)).map (MvPolynomial.map τ) = _
    rw [Ideal.map_map]
    congr 1
    apply RingHom.ext
    intro f
    exact (MvPolynomial.map_map ρ.rangeRestrict τ f).trans (by rw [hcomp])
  have heq := GeometricEquationDimensionProved.integralExtension_quotient_dimension
    (K := K) (L := L) J
  rw [hmap] at heq
  apply normalization_parameter_le_of_specialized_dimension_le I q hinj hint
    ρ.rangeRestrict ρ.rangeRestrict_surjective
  rw [← heq]
  exact hdim

end CubicTenVariables.FiniteFieldNormalizationSpecialization
