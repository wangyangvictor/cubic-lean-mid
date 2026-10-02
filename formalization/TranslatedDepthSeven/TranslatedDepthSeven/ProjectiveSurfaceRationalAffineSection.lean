import TranslatedDepthSeven.ProjectiveSurfaceHypersurfaceBezoutInternal
import TranslatedDepthSeven.RationalAffineChartDegreeMassInternal
import TranslatedDepthSeven.ProjectiveHilbertDegreeCertificationInternal

/-!
# Rational affine components of a projective surface section

For an integral rational projective surface cut properly by one homogeneous
form, this file constructs the actual rational first-chart ideal and proves
that all of its minimal components are affine curves whose positive degrees
have total at most the Bézout product.  The proof uses only the already
internal Hilbert, dimension, hypersurface-degree, and chart-transfer
machinery.
-/

namespace TranslatedDepthSeven

noncomputable section

open MvPolynomial Published

attribute [local instance] MvPolynomial.gradedAlgebra

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 300000

/-- The rational first affine chart of the projective intersection
`V(I) ∩ V(G)`. -/
def rationalAffineChartIntersectionIdeal {N : ℕ}
    (I : Ideal (MvPolynomial (Fin (N + 1)) ℚ))
    (G : MvPolynomial (Fin (N + 1)) ℚ) :
    Ideal (MvPolynomial (Fin N) ℚ) :=
  (I ⊔ Ideal.span {G}).map (standardDehomogenizationHom ℚ N)

/-- Rational surface-section components in the first affine chart have
dimension one and total degree at most `d*a`.  There is no real-component
or geometric-primality input in this statement. -/
theorem projectiveSurface_rationalAffineSection_degreeMass
    {N d a : ℕ}
    (I : Ideal (MvPolynomial (Fin (N + 1)) ℚ))
    (G : MvPolynomial (Fin (N + 1)) ℚ)
    (hIprime : I.IsPrime)
    (hIhom : I.IsHomogeneous
      (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) ℚ))
    (hIprojective : HasProjectiveDimensionDegree I 2 d)
    (hGhom : G.IsHomogeneous a)
    (hGnot : G ∉ I) :
    ∃ componentDegree : Ideal (MvPolynomial (Fin N) ℚ) → ℕ,
      (∀ Q ∈ finiteMinimalPrimes
          (rationalAffineChartIntersectionIdeal I G),
        HasAffineHilbertDimensionDegree Q 1 (componentDegree Q)) ∧
      ∑ Q ∈ finiteMinimalPrimes
          (rationalAffineChartIntersectionIdeal I G), componentDegree Q ≤
        d * a := by
  classical
  let J := I ⊔ Ideal.span ({G} : Set (MvPolynomial (Fin (N + 1)) ℚ))
  have hlower : ∀ P ∈ finiteMinimalPrimes J,
      (2 : WithBot ℕ∞) ≤
        ringKrullDim (MvPolynomial (Fin (N + 1)) ℚ ⧸ P) := by
    intro P hP
    letI : I.IsPrime := hIprime
    obtain ⟨r, hr, hdimension⟩ :=
      finiteEquation_minimalComponent_dimension_lower ℚ
        (MvPolynomial (Fin (N + 1)) ℚ) I P ({G} : Finset _)
        (by
          simpa only [J, Finset.coe_singleton] using
            (mem_finiteMinimalPrimes_iff
              (I ⊔ Ideal.span ({G} : Set _)) P).mp hP)
        (n := 3) (by simpa using hIprojective.1)
    have hrLower : 2 ≤ r := by
      simp only [Finset.card_singleton] at hdimension
      omega
    rw [hr]
    exact_mod_cast hrLower
  obtain ⟨sourceDegree, hsource, hsourceMass⟩ :=
    projectiveSurface_section_rationalComponentDegreeMass_of_dimension_lower_bound
      (projectiveHilbertDegreeCertification_internal ℚ)
      I G hIprime hIhom hIprojective hGhom hGnot hlower
  have hJhom : J.IsHomogeneous
      (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) ℚ) := by
    apply hIhom.sup
    apply Ideal.homogeneous_span
    intro f hf
    obtain rfl := Set.mem_singleton_iff.mp hf
    exact ⟨a, hGhom⟩
  obtain ⟨componentDegree, hchart, hchartMass⟩ :=
    rationalAffineChart_componentDegreeMass_of_projectiveComponents
      J hJhom sourceDegree hsource
  refine ⟨componentDegree, ?_, hchartMass.trans hsourceMass⟩
  intro Q hQ
  exact hchart Q (by
    simpa only [rationalAffineChartIntersectionIdeal, J] using hQ)

end

end TranslatedDepthSeven
