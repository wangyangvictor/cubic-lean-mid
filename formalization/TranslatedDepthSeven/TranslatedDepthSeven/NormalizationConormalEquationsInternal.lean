import TranslatedDepthSeven.LinearPolynomialComplementDirectionsInternal

/-!
# Bounded normalization equations with diagonal directional derivatives

The source equations lie in the given prime ideal, are homogeneous of
degrees at most the projective degree, and have linearly independent
generic differentials.  The latter assertion is expressed here by an
exact diagonal directional-derivative identity with nonzero diagonal
entries in the source quotient.  Ideal generation is not asserted.
-/

namespace TranslatedDepthSeven

noncomputable section

open MvPolynomial Published

attribute [local instance] MvPolynomial.gradedAlgebra

set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 500000

/-- Substitution of the formal normalization equation agrees in the
source quotient with its univariate evaluation. -/
theorem quotient_aeval_linearNormalization_option
    {K : Type*} [Field K] {N : ℕ}
    (I : Ideal (MvPolynomial (Fin (N + 1)) K))
    (D : HomogeneousLinearNormalizationData I)
    (w : MvPolynomial (Fin (N + 1)) K)
    (p : Polynomial (MvPolynomial (Fin D.parameterCount) K)) :
    letI : Algebra (MvPolynomial (Fin D.parameterCount) K)
      (MvPolynomial (Fin (N + 1)) K ⧸ I) := D.hom.toRingHom.toAlgebra
    Ideal.Quotient.mk I
      (aeval (fun i : Option (Fin D.parameterCount) ↦ i.elim w D.forms)
        ((optionEquivLeft K (Fin D.parameterCount)).symm p)) =
      Polynomial.aeval (Ideal.Quotient.mk I w) p := by
  letI : Algebra (MvPolynomial (Fin D.parameterCount) K)
    (MvPolynomial (Fin (N + 1)) K ⧸ I) := D.hom.toRingHom.toAlgebra
  let mk := Ideal.Quotient.mkₐ K I
  let l : Option (Fin D.parameterCount) → MvPolynomial (Fin (N + 1)) K :=
    fun i ↦ i.elim w D.forms
  have hcomp : mk.comp (aeval l) =
      ((Polynomial.aeval (mk w)).restrictScalars K).comp
        (optionEquivLeft K (Fin D.parameterCount)).toAlgHom := by
    apply MvPolynomial.algHom_ext
    intro i
    cases i with
    | none =>
        simp only [AlgHom.comp_apply, MvPolynomial.aeval_X]
        change mk w = Polynomial.aeval (mk w)
          ((optionEquivLeft K (Fin D.parameterCount)) (X none))
        rw [optionEquivLeft_X_none, Polynomial.aeval_X]
    | some i =>
        simp only [AlgHom.comp_apply, MvPolynomial.aeval_X]
        change mk (D.forms i) = Polynomial.aeval (mk w)
          ((optionEquivLeft K (Fin D.parameterCount)) (X (some i)))
        rw [optionEquivLeft_X_some, Polynomial.aeval_C]
        change mk (D.forms i) = D.hom (X i)
        simp [HomogeneousLinearNormalizationData.hom, mk]
  have h := DFunLike.congr_fun hcomp
    ((optionEquivLeft K (Fin D.parameterCount)).symm p)
  change mk (aeval l ((optionEquivLeft K (Fin D.parameterCount)).symm p)) =
    Polynomial.aeval (mk w)
      ((optionEquivLeft K (Fin D.parameterCount))
        ((optionEquivLeft K (Fin D.parameterCount)).symm p)) at h
  rw [AlgEquiv.apply_symm_apply] at h
  exact h

/-- A homogeneous family of bounded equations with an exact diagonal
matrix of constant directional derivatives and no zero generic diagonal
entry. The family has the full affine codimension of the cone. -/
theorem exists_bounded_normalization_equations_diagonal_derivatives
    {K : Type*} [Field K] [CharZero K] {N r d : ℕ}
    (I : Ideal (MvPolynomial (Fin (N + 1)) K))
    (hIprime : I.IsPrime)
    (hIhom : I.IsHomogeneous (homogeneousSubmodule (Fin (N + 1)) K))
    (hdegree : HasProjectiveDimensionDegree I r d)
    (D : HomogeneousLinearNormalizationData I) :
    ∃ (F g : Fin (N + 1 - D.parameterCount) → MvPolynomial (Fin (N + 1)) K)
      (v : Fin (N + 1 - D.parameterCount) → Fin (N + 1) → K)
      (degrees : Fin (N + 1 - D.parameterCount) → ℕ),
      (∀ j, degrees j ≤ d) ∧
      (∀ j, (F j).IsHomogeneous (degrees j)) ∧
      (∀ j, F j ∈ I) ∧
      (∀ j, g j ∉ I) ∧
      (∀ i j, constantPolynomialDirectionalDerivative (v i) (F j) =
        if i = j then g j else 0) := by
  classical
  let B := MvPolynomial (Fin D.parameterCount) K
  let A := MvPolynomial (Fin (N + 1)) K ⧸ I
  letI : Algebra B A := D.hom.toRingHom.toAlgebra
  obtain ⟨w, v, hwhom, hvparam, hvw⟩ :=
    exists_linearNormalization_complementary_forms_and_directions I D
  have hequations (j : Fin (N + 1 - D.parameterCount)) :=
    exists_bounded_homogeneous_normalization_equation_with_nonzero_derivative
      I hIprime hIhom hdegree D (w j) (hwhom j)
  choose p hpmonic hpdegree hphom hpzero hpnonzero using hequations
  let l (j : Fin (N + 1 - D.parameterCount)) :
      Option (Fin D.parameterCount) → MvPolynomial (Fin (N + 1)) K :=
    fun i ↦ i.elim (w j) D.forms
  let F j := aeval (l j) ((optionEquivLeft K (Fin D.parameterCount)).symm (p j))
  let g j := aeval (l j)
    ((optionEquivLeft K (Fin D.parameterCount)).symm (p j).derivative)
  refine ⟨F, g, v, fun j ↦ (p j).natDegree, hpdegree, ?_, ?_, ?_, ?_⟩
  · intro j
    have hl (i : Option (Fin D.parameterCount)) : (l j i).IsHomogeneous 1 := by
      cases i with
      | none => exact hwhom j
      | some i => exact D.forms_isHomogeneous i
    simpa [F] using (hphom j).aeval (l j) hl
  · intro j
    apply (Ideal.Quotient.eq_zero_iff_mem).1
    rw [show Ideal.Quotient.mk I (F j) =
      Polynomial.aeval (Ideal.Quotient.mk I (w j)) (p j) from
        quotient_aeval_linearNormalization_option I D (w j) (p j)]
    exact hpzero j
  · intro j hgj
    apply hpnonzero j
    rw [← quotient_aeval_linearNormalization_option I D (w j) (p j).derivative]
    exact (Ideal.Quotient.eq_zero_iff_mem).2 hgj
  · intro i j
    change constantPolynomialDirectionalDerivative (v i)
      (aeval (l j) ((optionEquivLeft K (Fin D.parameterCount)).symm (p j))) = _
    rw [derivation_aeval_option_of_parameter_zero _ (l j)
      (fun k ↦ hvparam i k), pderiv_none_optionEquivLeft_symm]
    change g j * constantPolynomialDirectionalDerivative (v i) (w j) = _
    rw [hvw]
    split_ifs <;> simp

end

end TranslatedDepthSeven
