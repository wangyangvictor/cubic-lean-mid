import TranslatedDepthSeven.ProjectiveConeIdealStructure
import TranslatedDepthSeven.TranslatedProjectiveConeJoin

/-!
# The homogeneous-coordinate ideal of a translated projective cone

The homogeneous affine automorphism `(s,y) ↦ (s,s*y₀+r*y)` transports the
scheme-theoretic cone ideal.  Combining that transport with the polynomial-
extension description of the coordinate cone gives a literal quotient-ring
equivalence.  No assertion about closed points or irreducible components is
used.
-/

namespace TranslatedDepthSeven

noncomputable section

open MvPolynomial

universe u v

variable {K : Type u} [Field K] {σ : Type v}

/-- The ideal of the translated projective cone, defined directly as the
image of the coordinate-cone ideal under the homogeneous affine change. -/
def translatedProjectiveConeIdeal
    (y₀ : σ → K) (r : K) (hr : r ≠ 0)
    (I : Ideal (MvPolynomial σ K)) :
    Ideal (MvPolynomial (Option σ) K) :=
  (projectiveConeIdealExtension I).map
    (homogeneousAffinePolynomialChangeAlgEquiv y₀ r hr)

/-- The translated cone remains prime when the original homogeneous ideal
is prime. -/
theorem translatedProjectiveConeIdeal_isPrime
    (y₀ : σ → K) (r : K) (hr : r ≠ 0)
    (I : Ideal (MvPolynomial σ K)) (hI : I.IsPrime) :
    (translatedProjectiveConeIdeal y₀ r hr I).IsPrime := by
  letI : I.IsPrime := hI
  have hcone : (projectiveConeIdealExtension I).IsPrime :=
    projectiveConeIdealExtension_isPrime I hI
  letI : (projectiveConeIdealExtension I).IsPrime := hcone
  exact homogeneousAffinePolynomialChange_map_isPrime
    y₀ r hr (projectiveConeIdealExtension I)

/-- The translated cone coordinate ring is a polynomial ring in the vertex
coordinate over the original homogeneous coordinate ring. -/
def translatedProjectiveConeQuotientRingEquiv
    (y₀ : σ → K) (r : K) (hr : r ≠ 0)
    (I : Ideal (MvPolynomial σ K)) :
    (MvPolynomial (Option σ) K ⧸
        translatedProjectiveConeIdeal y₀ r hr I) ≃+*
      Polynomial (MvPolynomial σ K ⧸ I) :=
  (homogeneousAffinePolynomialChangeQuotientAlgEquiv
      y₀ r hr (projectiveConeIdealExtension I)).symm.toRingEquiv.trans
    (projectiveConeQuotientRingEquiv I)

/-- Applying the homogeneous affine change to a finite family of cone
equations generates exactly the translated cone ideal. -/
theorem finiteEquationIdeal_translated_renameSomeEquationFinset
    (y₀ : σ → K) (r : K) (hr : r ≠ 0)
    (equations : Finset (MvPolynomial σ K)) :
    finiteEquationIdeal
        (finiteFamilyHomogeneousAffineChange y₀ r hr
          (renameSomeEquationFinset equations)) =
      translatedProjectiveConeIdeal y₀ r hr
        (finiteEquationIdeal equations) := by
  rw [← map_finiteEquationIdeal_homogeneousAffineChange,
    finiteEquationIdeal_image_rename_some]
  rfl

end

end TranslatedDepthSeven
