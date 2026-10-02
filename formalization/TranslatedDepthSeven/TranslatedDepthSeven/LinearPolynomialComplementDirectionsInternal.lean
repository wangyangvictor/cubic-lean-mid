import TranslatedDepthSeven.NormalizationDirectionalDerivativeInternal
import TranslatedDepthSeven.IndependentFamilyComplementDualInternal

/-!
# Complementary constant directions for linear normalization

The linear normalization forms are linearly independent even before
passing to the quotient.  Extending them inside the degree-one vector
space supplies complementary linear forms and constant coordinate
directions with the exact Kronecker pairing.
-/

namespace TranslatedDepthSeven

noncomputable section

open MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 300000

/-- Every functional on the degree-one piece is evaluation of the
constant directional derivative. -/
theorem constantPolynomialDirectionalDerivative_of_linear_dual
    {K : Type*} [Field K] {n : ℕ}
    (ell : Module.Dual K (homogeneousSubmodule (Fin n) K 1))
    (w : homogeneousSubmodule (Fin n) K 1) :
    constantPolynomialDirectionalDerivative
      (fun i ↦ ell ⟨X i, isHomogeneous_X K i⟩) w = C (ell w) := by
  classical
  let x (i : Fin n) : homogeneousSubmodule (Fin n) K 1 :=
    ⟨X i, isHomogeneous_X K i⟩
  have hderiv (i : Fin n) :
      pderiv i (w : MvPolynomial (Fin n) K) =
        C ((pderiv i (w : MvPolynomial (Fin n) K)).coeff 0) := by
    apply eq_C_coeff_zero_of_isHomogeneous_zero
    simpa using w.property.pderiv (i := i)
  have heuler :
      ∑ i : Fin n, ((pderiv i (w : MvPolynomial (Fin n) K)).coeff 0) • x i = w := by
    apply Subtype.ext
    simp only [Submodule.coe_sum, Submodule.coe_smul, x, smul_eq_C_mul]
    change (∑ i : Fin n, C ((pderiv i (w : MvPolynomial (Fin n) K)).coeff 0) * X i) = _
    calc
      _ = ∑ i : Fin n, X i * pderiv i (w : MvPolynomial (Fin n) K) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [hderiv i]
        simp only [coeff_C, if_true]
        exact mul_comm _ _
      _ = _ := by simpa using w.property.sum_X_mul_pderiv
  rw [constantPolynomialDirectionalDerivative_eq_sum]
  conv_rhs => rw [← heuler]
  simp only [map_sum, map_smul, smul_eq_mul, map_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [hderiv]
  simp only [coeff_C, if_true, x]
  exact mul_comm _ _

/-- Injectivity of the polynomial parameter algebra implies linear
independence of its displayed linear forms. -/
theorem homogeneousLinearNormalization_forms_linearIndependent
    {K : Type*} [Field K] {N : ℕ}
    (I : Ideal (MvPolynomial (Fin (N + 1)) K))
    (D : HomogeneousLinearNormalizationData I) :
    LinearIndependent K
      (fun i : Fin D.parameterCount ↦
        (⟨D.forms i, D.forms_isHomogeneous i⟩ :
          homogeneousSubmodule (Fin (N + 1)) K 1)) := by
  have h : LinearIndependent K
      (fun i : Fin D.parameterCount ↦ D.hom (X i)) :=
    (MvPolynomial.linearIndependent_X (Fin D.parameterCount) K).map'
      D.hom.toLinearMap (LinearMap.ker_eq_bot.mpr D.hom_injective)
  apply LinearIndependent.of_comp
    ((Ideal.Quotient.mkₐ K I).toLinearMap.comp
      (homogeneousSubmodule (Fin (N + 1)) K 1).subtype)
  simpa [Function.comp_def, HomogeneousLinearNormalizationData.hom] using h

/-- The exact complementary forms and constant directions.  The index
size is the ambient dimension minus the number of normalization forms. -/
theorem exists_linearNormalization_complementary_forms_and_directions
    {K : Type*} [Field K] {N : ℕ}
    (I : Ideal (MvPolynomial (Fin (N + 1)) K))
    (D : HomogeneousLinearNormalizationData I) :
    ∃ (w : Fin (N + 1 - D.parameterCount) → MvPolynomial (Fin (N + 1)) K)
      (v : Fin (N + 1 - D.parameterCount) → Fin (N + 1) → K),
      (∀ j, (w j).IsHomogeneous 1) ∧
      (∀ j i, constantPolynomialDirectionalDerivative (v j) (D.forms i) = 0) ∧
      (∀ i j, constantPolynomialDirectionalDerivative (v i) (w j) =
        if i = j then 1 else 0) := by
  classical
  let V := homogeneousSubmodule (Fin (N + 1)) K 1
  let u : Fin D.parameterCount → V :=
    fun i ↦ ⟨D.forms i, D.forms_isHomogeneous i⟩
  have hdim : Module.finrank K V = N + 1 := by
    simpa [V] using finrank_mvPolynomial_homogeneousSubmodule_fin K (N + 1) 1
  obtain ⟨b, ell, hb, hzero, hpair⟩ :=
    exists_complementary_basis_and_dual_functionals u
      (homogeneousLinearNormalization_forms_linearIndependent I D)
  let e : Fin (N + 1 - D.parameterCount) ≃
      Fin (Module.finrank K V - D.parameterCount) :=
    Equiv.cast (congrArg Fin (congrArg (fun n ↦ n - D.parameterCount) hdim.symm))
  refine ⟨fun j ↦ (b (Sum.inr (e j))).val,
    fun j i ↦ ell (e j) ⟨X i, isHomogeneous_X K i⟩, ?_, ?_, ?_⟩
  · intro j
    exact (b (Sum.inr (e j))).property
  · intro j i
    have h := constantPolynomialDirectionalDerivative_of_linear_dual (ell (e j)) (u i)
    rw [hzero, map_zero] at h
    exact h
  · intro i j
    have h := constantPolynomialDirectionalDerivative_of_linear_dual
      (ell (e i)) (b (Sum.inr (e j)))
    rw [hpair] at h
    simpa only [e.injective.eq_iff, apply_ite C, map_one, map_zero] using h

end

end TranslatedDepthSeven
