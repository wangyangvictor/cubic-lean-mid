import TranslatedDepthSeven.StandardAlgebraicGeometry
import TranslatedDepthSeven.StrictRankAtMostSixPilaClosure
import TranslatedDepthSeven.StrictRankAtMostSixRealPrimePila

/-!
# Standard algebraic-geometric inputs for the strict low-rank endpoint

This file converts the textbook propositions named in
`StandardAlgebraicGeometry` into the literal interfaces used by the
strict rank-at-most-six proof.  The conversions themselves are elementary:
the degree-one part of a homogeneous ideal is identified with its coefficient
vectors, and the dimension occurring in the Hilbert polynomial is identified
from the Krull dimension of the homogeneous coordinate ring.
-/

namespace TranslatedDepthSeven

noncomputable section

open MvPolynomial Published

attribute [local instance] MvPolynomial.gradedAlgebra

set_option synthInstance.maxHeartbeats 300000

/-! ## The degree-one coefficient-space identification -/

theorem rationalLinearPolynomial_isHomogeneous {N : ℕ}
    (a : Fin N → ℚ) :
    (rationalLinearPolynomial a).IsHomogeneous 1 := by
  apply MvPolynomial.IsHomogeneous.sum Finset.univ _ 1
  intro i _hi
  exact MvPolynomial.isHomogeneous_C_mul_X _ _

theorem rationalLinearPolynomial_injective {N : ℕ} :
    Function.Injective
      (rationalLinearPolynomial :
        (Fin N → ℚ) →ₗ[ℚ] MvPolynomial (Fin N) ℚ) := by
  intro a b hab
  funext i
  have heval := congrArg
    (MvPolynomial.eval (fun j : Fin N ↦ if j = i then 1 else 0)) hab
  simpa [rationalLinearPolynomial] using heval

theorem rationalLinearPolynomial_coefficients_of_isHomogeneous_one
    {N : ℕ} (f : MvPolynomial (Fin N) ℚ)
    (hf : f.IsHomogeneous 1) :
    rationalLinearPolynomial
        (fun i ↦ (MvPolynomial.pderiv i f).coeff 0) = f := by
  have heuler : ∑ i : Fin N, X i * pderiv i f = f := by
    simpa using hf.sum_X_mul_pderiv
  have hderiv : ∀ i : Fin N,
      pderiv i f = C ((pderiv i f).coeff 0) := by
    intro i
    apply MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp
    exact (MvPolynomial.totalDegree_zero_iff_isHomogeneous (Fin N)).mpr
      (by simpa using hf.pderiv (i := i))
  rw [rationalLinearPolynomial]
  calc
    (∑ i : Fin N, C ((pderiv i f).coeff 0) * X i) =
        ∑ i : Fin N, X i * C ((pderiv i f).coeff 0) := by
      apply Finset.sum_congr rfl
      intro i _hi
      exact mul_comm _ _
    _ = ∑ i : Fin N, X i * pderiv i f := by
      apply Finset.sum_congr rfl
      intro i _hi
      exact congrArg (fun q ↦ X i * q) (hderiv i).symm
    _ = f := heuler

/-- The coefficient-vector model of linear equations and the ordinary
degree-one part of the ideal are canonically linearly equivalent. -/
noncomputable def rationalLinearFormsInIdealEquivDegreeOnePart
    {N : ℕ} (I : Ideal (MvPolynomial (Fin N) ℚ)) :
    rationalLinearFormsInIdeal I ≃ₗ[ℚ] StandardAG.degreeOnePartInIdeal I :=
  LinearEquiv.ofBijective
    { toFun := fun a ↦ ⟨rationalLinearPolynomial a.1,
        Submodule.mem_inf.mpr ⟨a.2,
          rationalLinearPolynomial_isHomogeneous a.1⟩⟩
      map_add' := by
        intro a b
        apply Subtype.ext
        exact map_add rationalLinearPolynomial a.1 b.1
      map_smul' := by
        intro q a
        apply Subtype.ext
        exact map_smul rationalLinearPolynomial q a.1 }
    ⟨by
      intro a b hab
      apply Subtype.ext
      apply rationalLinearPolynomial_injective
      exact congrArg Subtype.val hab,
    by
      intro f
      have hfhomogeneous : (f.1).IsHomogeneous 1 :=
        (Submodule.mem_inf.mp f.2).2
      let a : Fin N → ℚ := fun i ↦ (pderiv i f.1).coeff 0
      have haI : rationalLinearPolynomial a ∈ I := by
        rw [rationalLinearPolynomial_coefficients_of_isHomogeneous_one
          f.1 hfhomogeneous]
        exact (Submodule.mem_inf.mp f.2).1
      refine ⟨⟨a, haI⟩, ?_⟩
      apply Subtype.ext
      exact rationalLinearPolynomial_coefficients_of_isHomogeneous_one
        f.1 hfhomogeneous⟩

theorem finrank_rationalLinearFormsInIdeal_eq_degreeOnePart
    {N : ℕ} (I : Ideal (MvPolynomial (Fin N) ℚ)) :
    Module.finrank ℚ (rationalLinearFormsInIdeal I) =
      Module.finrank ℚ (StandardAG.degreeOnePartInIdeal I) :=
  LinearEquiv.finrank_eq (rationalLinearFormsInIdealEquivDegreeOnePart I)

/-! ## Exact adapters from the textbook propositions -/

namespace StandardAG

/-- The standard algebraic-closure criterion for geometric integrality, in
the one direction needed here.  For a rational polynomial ideal, primeness
after coefficient extension to `Qbar` implies primeness after coefficient
extension to every field.  This is a proposition naming a textbook result,
not an axiom or an application-specific counting interface. -/
def QbarCoefficientExtensionPrimeImpliesGeometricallyPrime : Prop :=
  ∀ (N : ℕ) (I : Ideal (MvPolynomial (Fin N) ℚ)),
    (I.map (MvPolynomial.map (algebraMap ℚ Qbar))).IsPrime →
      GeometricallyPrimeMvPolynomialIdeal I

end StandardAG

/-- Hilbert--Serre, as stated in `StandardAG`, gives the exact
dimension--degree certificate used in the strict low-rank proof.  The only
conversion is uniqueness of the natural number determined by the Krull
dimension of the homogeneous coordinate ring. -/
theorem projectiveHilbertDimensionDegree_of_standardCertification
    (hHilbert : StandardAG.ProjectiveHilbertDegreeCertification ℚ) :
    ∀ (N r : ℕ) (I : Ideal (MvPolynomial (Fin (N + 1)) ℚ)),
      I.IsPrime →
      I.IsHomogeneous
        (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) ℚ) →
      ¬ projectiveIrrelevantIdeal ℚ N ≤ I →
      ringKrullDim (MvPolynomial (Fin (N + 1)) ℚ ⧸ I) = r + 1 →
        ∃ d : ℕ, HasProjectiveDimensionDegree I r d := by
  intro N r I hprime hhomogeneous hnonempty hdimension
  obtain ⟨r', d, P, hcertificate⟩ :=
    hHilbert N I hprime hhomogeneous hnonempty
  have hr : r' = r := by
    have hsWithBot : (r' : WithBot ℕ∞) + 1 = (r : WithBot ℕ∞) + 1 :=
      hcertificate.1.symm.trans hdimension
    have hs : r' + 1 = r + 1 := by
      exact_mod_cast hsWithBot
    omega
  subst r'
  exact ⟨d, hcertificate.toPublished⟩

/-- The coordinate-ring degree--span inequality in `StandardAG` is exactly
the coefficient-vector inequality used to choose the two rational
hyperplanes.  The apparently different finite-dimensional spaces are
identified by `rationalLinearFormsInIdealEquivDegreeOnePart`. -/
theorem rationalLinearFormDegreeSpan_of_standardInequality
    (hDegreeSpan : StandardAG.ProjectiveDegreeSpanInequality ℚ) :
    ∀ (N r d : ℕ)
      (I : Ideal (MvPolynomial (Fin (N + 1)) ℚ)),
      I.IsPrime →
      (I.map (MvPolynomial.map (algebraMap ℚ (AlgebraicClosure ℚ)))).IsPrime →
      I.IsHomogeneous
        (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) ℚ) →
      IsSaturatedByProjectiveIrrelevantIdeal I →
      HasProjectiveDimensionDegree I r d →
      N + 1 - r - d ≤
        Module.finrank ℚ (rationalLinearFormsInIdeal I) := by
  intro N r d I hprime hgeometric hhomogeneous _hsaturated hprojective
  have hspan := hDegreeSpan N r d I hprime hgeometric hhomogeneous hprojective
  rw [← finrank_rationalLinearFormsInIdeal_eq_degreeOnePart I] at hspan
  omega

/-! ## Closed low-rank theorem -/

/-- The strict rank-at-most-six contribution, closed using only the printed
Pila theorem and two standard algebraic-geometric propositions.  There is
no componentwise qualification hypothesis and no strengthened Pila
interface: all component data are constructed internally by the preceding
exact reduction. -/
theorem exists_strictRankAtMostSix_card_le_thirteenThirds_of_standardAG
    (hPila : Pila1995TheoremA)
    (hHilbert : StandardAG.ProjectiveHilbertDegreeCertification ℚ)
    (hQbar :
      StandardAG.QbarCoefficientExtensionPrimeImpliesGeometricallyPrime)
    (equations : Finset (MvPolynomial (Fin 13) ℤ)) (degree : ℕ)
    (hGeometricallyPrime : GeometricallyPrimeMvPolynomialIdeal
      (rationalDepthSevenEquationIdeal equations))
    (hI : IsIntegralProjectiveVariety
      (N := 12) (rationalDepthSevenEquationIdeal equations) 5 degree) :
    ∃ CF₀ : ℕ, ∀ CF : ℕ, CF₀ ≤ CF →
      ∀ epsilon : ℝ, 0 < epsilon →
        ∃ C : ℝ, 0 < C ∧
          ∀ (p : Parameters) (x₀ : IntVector 13),
            ((depthSevenNormalizedRankAtMostSixFinset
                p x₀ equations CF).card : ℝ) ≤
              C * ((2 * surfaceTangentNaturalSide p + 1 : ℕ) : ℝ) ^
                ((13 / 3 : ℝ) + epsilon) := by
  exact exists_strictRankAtMostSix_card_le_thirteenThirds
    hPila
    (projectiveHilbertDimensionDegree_of_standardCertification hHilbert)
    hQbar equations degree hGeometricallyPrime hI

/-- The strict rank-at-most-six contribution with the algebraic-closure
criterion narrowed to exactly the coefficient field used by Pila.  The
older all-fields version above remains available for compatibility. -/
theorem exists_strictRankAtMostSix_card_le_thirteenThirds_of_standardAG_realPrime
    (hPila : Pila1995TheoremA)
    (hHilbert : StandardAG.ProjectiveHilbertDegreeCertification ℚ)
    (hQbarToReal :
      ∀ (N : ℕ) (I : Ideal (MvPolynomial (Fin N) ℚ)),
        (I.map (MvPolynomial.map (algebraMap ℚ Qbar))).IsPrime →
          (I.map (MvPolynomial.map (algebraMap ℚ ℝ))).IsPrime)
    (equations : Finset (MvPolynomial (Fin 13) ℤ)) (degree : ℕ)
    (hGeometricallyPrime : GeometricallyPrimeMvPolynomialIdeal
      (rationalDepthSevenEquationIdeal equations))
    (hI : IsIntegralProjectiveVariety
      (N := 12) (rationalDepthSevenEquationIdeal equations) 5 degree) :
    ∃ CF₀ : ℕ, ∀ CF : ℕ, CF₀ ≤ CF →
      ∀ epsilon : ℝ, 0 < epsilon →
        ∃ C : ℝ, 0 < C ∧
          ∀ (p : Parameters) (x₀ : IntVector 13),
            ((depthSevenNormalizedRankAtMostSixFinset
                p x₀ equations CF).card : ℝ) ≤
              C * ((2 * surfaceTangentNaturalSide p + 1 : ℕ) : ℝ) ^
                ((13 / 3 : ℝ) + epsilon) := by
  exact exists_strictRankAtMostSix_card_le_thirteenThirds_of_qbarToReal
    hPila
    (projectiveHilbertDimensionDegree_of_standardCertification hHilbert)
    hQbarToReal equations degree hGeometricallyPrime hI

end

end TranslatedDepthSeven
