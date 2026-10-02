import Mathlib.FieldTheory.Galois.GaloisClosure
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.Algebra.MvPolynomial.Eval

/-!
# A finite Galois field containing finitely many polynomial coefficients
-/

namespace TranslatedDepthSeven

noncomputable section

universe u

variable {σ : Type u}

/-- The finite set of all coefficients occurring in a finite polynomial
family over `Qbar`. -/
def polynomialFamilyCoefficients
    (E : Finset (MvPolynomial σ (AlgebraicClosure ℚ))) :
    Finset (AlgebraicClosure ℚ) := by
  classical
  exact E.biUnion MvPolynomial.coeffs

theorem mem_polynomialFamilyCoefficients
    (E : Finset (MvPolynomial σ (AlgebraicClosure ℚ)))
    {f : MvPolynomial σ (AlgebraicClosure ℚ)} (hf : f ∈ E)
    {c : AlgebraicClosure ℚ} (hc : c ∈ f.coeffs) :
    c ∈ polynomialFamilyCoefficients E := by
  classical
  exact Finset.mem_biUnion.mpr ⟨f, hf, hc⟩

/-- The finite Galois intermediate field obtained by adjoining all
coefficients of the family and then taking their normal closure. -/
def polynomialFamilyGaloisField
    (E : Finset (MvPolynomial σ (AlgebraicClosure ℚ))) :
    FiniteGaloisIntermediateField ℚ (AlgebraicClosure ℚ) :=
  FiniteGaloisIntermediateField.adjoin ℚ
    (polynomialFamilyCoefficients E)

theorem coefficient_mem_polynomialFamilyGaloisField
    (E : Finset (MvPolynomial σ (AlgebraicClosure ℚ)))
    {f : MvPolynomial σ (AlgebraicClosure ℚ)} (hf : f ∈ E)
    {c : AlgebraicClosure ℚ} (hc : c ∈ f.coeffs) :
    c ∈ (polynomialFamilyGaloisField E :
      IntermediateField ℚ (AlgebraicClosure ℚ)) := by
  apply FiniteGaloisIntermediateField.subset_adjoin ℚ
    (polynomialFamilyCoefficients E : Set (AlgebraicClosure ℚ))
  exact mem_polynomialFamilyCoefficients E hf hc

/-- Every automorphism of the finite Galois coefficient field extends to an
automorphism of `Qbar`. -/
theorem exists_qbarAlgEquiv_extending
    (E : Finset (MvPolynomial σ (AlgebraicClosure ℚ)))
    (τ : polynomialFamilyGaloisField E ≃ₐ[ℚ]
      polynomialFamilyGaloisField E) :
    ∃ g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
      ∀ x : polynomialFamilyGaloisField E,
        g (x : AlgebraicClosure ℚ) = (τ x : AlgebraicClosure ℚ) := by
  obtain ⟨g, hg⟩ :=
    AlgEquiv.restrictNormalHom_surjective (AlgebraicClosure ℚ) τ
  refine ⟨g, ?_⟩
  intro x
  have hx := congrArg (fun e : polynomialFamilyGaloisField E ≃ₐ[ℚ]
      polynomialFamilyGaloisField E ↦ (e x : AlgebraicClosure ℚ)) hg
  dsimp only at hx
  rw [AlgEquiv.restrictNormalHom_apply] at hx
  exact hx

end

end TranslatedDepthSeven
