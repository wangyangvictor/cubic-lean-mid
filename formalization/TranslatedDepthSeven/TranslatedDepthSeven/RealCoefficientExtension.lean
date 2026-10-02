import Mathlib
import TranslatedDepthSeven.GeometricPrimeness

/-!
# Faithful flatness of real coefficient extension

The coefficient map

`\mathbb Q[X_i] \longrightarrow \mathbb R[X_i]`

is faithfully flat.  The proof is completely explicit.  First, `\mathbb R`
is a nonzero free `\mathbb Q`-module, hence faithfully flat.  Faithful
flatness survives base change to `\mathbb Q[X_i]`.  Finally, the resulting
tensor product is identified with `\mathbb R[X_i]` by commuting the tensor
factors and applying the standard multivariate-polynomial tensor
equivalence.

The explicit linear equivalence below is intentional: the canonical
tensor-product scalar action and the scalar action inherited through an
`AlgEquiv` are propositionally equal but not definitionally identical in
Mathlib.  Writing the scalar calculation avoids an instance-dependent
coincidence.
-/

namespace TranslatedDepthSeven

noncomputable section

open scoped TensorProduct

set_option synthInstance.maxHeartbeats 500000
set_option maxHeartbeats 1000000

noncomputable local instance realMvPolynomialCoefficientAlgebra
    {σ : Type*} :
    Algebra (MvPolynomial σ ℚ) (MvPolynomial σ ℝ) :=
  MvPolynomial.algebraMvPolynomial

/-- The explicit `\mathbb Q[X_i]`-linear tensor description of
`\mathbb R[X_i]`. -/
noncomputable def realMvPolynomialTensorLinearEquiv
    {σ : Type*} :
    MvPolynomial σ ℝ ≃ₗ[MvPolynomial σ ℚ]
      ((MvPolynomial σ ℚ) ⊗[ℚ] ℝ) := by
  let eAlg : ((MvPolynomial σ ℚ) ⊗[ℚ] ℝ) ≃ₐ[ℚ]
      MvPolynomial σ ℝ :=
    (Algebra.TensorProduct.comm ℚ (MvPolynomial σ ℚ) ℝ).trans
      ((MvPolynomial.algebraTensorAlgEquiv ℚ ℝ (σ := σ)).restrictScalars ℚ)
  exact
    { eAlg.symm.toEquiv with
      map_add' := eAlg.symm.map_add
      map_smul' := by
        intro a b
        simp [eAlg, Algebra.smul_def]
        change (algebraMap (MvPolynomial σ ℚ)
          ((MvPolynomial σ ℚ) ⊗[ℚ] ℝ)) a *
            (Algebra.TensorProduct.comm ℚ (MvPolynomial σ ℚ) ℝ).symm
              ((MvPolynomial.algebraTensorAlgEquiv ℚ ℝ
                (σ := σ)).symm b) = _
        exact (Algebra.smul_def a _).symm }

/-- Real multivariate polynomials are faithfully flat over rational
multivariate polynomials under coefficient extension. -/
noncomputable instance realMvPolynomial_faithfullyFlat
    {σ : Type*} :
    Module.FaithfullyFlat (MvPolynomial σ ℚ) (MvPolynomial σ ℝ) := by
  letI : Module.FaithfullyFlat ℚ ℝ := inferInstance
  letI : Module.FaithfullyFlat (MvPolynomial σ ℚ)
      ((MvPolynomial σ ℚ) ⊗[ℚ] ℝ) := inferInstance
  exact Module.FaithfullyFlat.of_linearEquiv
    (MvPolynomial σ ℚ) ((MvPolynomial σ ℚ) ⊗[ℚ] ℝ)
      realMvPolynomialTensorLinearEquiv

/-- Extending a rational polynomial ideal to real coefficients and then
contracting it recovers the original ideal exactly. -/
theorem realMvPolynomial_comap_map_eq
    {σ : Type*} (I : Ideal (MvPolynomial σ ℚ)) :
    (I.map (algebraMap (MvPolynomial σ ℚ)
      (MvPolynomial σ ℝ))).comap
        (algebraMap (MvPolynomial σ ℚ) (MvPolynomial σ ℝ)) = I := by
  exact Ideal.comap_map_eq_self_of_faithfullyFlat I

/-- The preceding contraction identity, written using the literal
coefficientwise polynomial map used elsewhere in this development. -/
theorem realMvPolynomial_comap_map_coefficients_eq
    {σ : Type*} (I : Ideal (MvPolynomial σ ℚ)) :
    (I.map (MvPolynomial.map (algebraMap ℚ ℝ))).comap
        (MvPolynomial.map (algebraMap ℚ ℝ)) = I := by
  simpa only [MvPolynomial.algebraMap_apply] using
    (realMvPolynomial_comap_map_eq I)

/-- Geometric primeness supplies primeness after the particular coefficient
extension from `\mathbb Q` to `\mathbb R` used by Pila's theorem.  This is
an immediate specialization of the literal base-change definition, not an
extra geometric input. -/
theorem realCoefficientExtension_isPrime_of_geometricallyPrime
    {σ : Type} (I : Ideal (MvPolynomial σ ℚ))
    (hI : GeometricallyPrimeMvPolynomialIdeal I) :
    (I.map (MvPolynomial.map (algebraMap ℚ ℝ))).IsPrime := by
  exact hI ℝ

end

end TranslatedDepthSeven
