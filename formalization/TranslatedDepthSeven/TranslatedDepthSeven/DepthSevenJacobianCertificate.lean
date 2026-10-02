import TranslatedDepthSeven.FixedConeResidueCount
import TranslatedDepthSeven.JacobianCertificatePolynomialHeight
import TranslatedDepthSeven.AffineJacobianTransform

/-!
# Pointwise Jacobian certificates for the literal equation family

This file turns the rational rank-seven condition for the fixed finite
equation family into the exact nonzero integer deleted from the auxiliary
prime reservoir.  All height constants are finite suprema of literal
supports, degrees, and coefficients of the supplied equations.
-/

namespace TranslatedDepthSeven

noncomputable section

open MvPolynomial

/-- Maximum support cardinality in a finite integral equation family. -/
def equationFamilySupportBound {N : ℕ}
    (equations : Finset (MvPolynomial (Fin N) ℤ)) : ℕ :=
  equations.sup fun f ↦ f.support.card

/-- Maximum total degree in a finite integral equation family. -/
def equationFamilyDegreeBound {N : ℕ}
    (equations : Finset (MvPolynomial (Fin N) ℤ)) : ℕ :=
  equations.sup MvPolynomial.totalDegree

/-- Maximum absolute value of every coefficient which occurs in a finite
integral equation family. -/
def equationFamilyCoefficientBound {N : ℕ}
    (equations : Finset (MvPolynomial (Fin N) ℤ)) : ℕ :=
  equations.sup fun f ↦ f.support.sup fun μ ↦ (f.coeff μ).natAbs

theorem support_card_le_equationFamilySupportBound
    {N : ℕ} {equations : Finset (MvPolynomial (Fin N) ℤ)}
    {f : MvPolynomial (Fin N) ℤ} (hf : f ∈ equations) :
    f.support.card ≤ equationFamilySupportBound equations := by
  exact Finset.le_sup (f := fun g ↦ g.support.card) hf

theorem totalDegree_le_equationFamilyDegreeBound
    {N : ℕ} {equations : Finset (MvPolynomial (Fin N) ℤ)}
    {f : MvPolynomial (Fin N) ℤ} (hf : f ∈ equations) :
    f.totalDegree ≤ equationFamilyDegreeBound equations := by
  exact Finset.le_sup (f := MvPolynomial.totalDegree) hf

theorem coeff_natAbs_le_equationFamilyCoefficientBound
    {N : ℕ} {equations : Finset (MvPolynomial (Fin N) ℤ)}
    {f : MvPolynomial (Fin N) ℤ} (hf : f ∈ equations)
    {μ : Fin N →₀ ℕ} (hμ : μ ∈ f.support) :
    (f.coeff μ).natAbs ≤ equationFamilyCoefficientBound equations := by
  exact (Finset.le_sup (f := fun ν ↦ (f.coeff ν).natAbs) hμ).trans
    (Finset.le_sup (f := fun g ↦
      g.support.sup fun ν ↦ (g.coeff ν).natAbs) hf)

/-- The literal rank condition defining the rank-seven (affine
dimension-six) part of the fixed cone at an integral point. -/
def IsDepthSevenJacobianRegularAt
    (equations : Finset (MvPolynomial (Fin 13) ℤ))
    (x : IntVector 13) : Prop :=
  7 ≤ ((integralJacobianMatrix (indexedFinsetFamily equations) x).map
    (Int.castRingHom ℚ)).rank

/-- A rank-seven point supplies an honest nonzero `7 x 7` Jacobian minor,
with its size bounded entirely by the fixed equation family and the displayed
coordinate bound for the point. -/
theorem exists_depthSeven_bounded_nonzero_jacobianMinor
    (equations : Finset (MvPolynomial (Fin 13) ℤ))
    (x : IntVector 13) (Y : ℕ)
    (hregular : IsDepthSevenJacobianRegularAt equations x)
    (hx : ∀ j, (x j).natAbs ≤ Y) :
    ∃ rows : Fin 7 → Fin equations.card,
      ∃ cols : Fin 7 → Fin 13,
        Function.Injective rows ∧ Function.Injective cols ∧
        integralJacobianMinor (indexedFinsetFamily equations) x rows cols ≠ 0 ∧
        (integralJacobianMinor
          (indexedFinsetFamily equations) x rows cols).natAbs ≤
          Nat.factorial 7 *
            (equationFamilySupportBound equations *
              equationFamilyDegreeBound equations *
              equationFamilyCoefficientBound equations *
              max 1 Y ^ equationFamilyDegreeBound equations) ^ 7 := by
  classical
  have hmem (i : Fin equations.card) :
      indexedFinsetFamily equations i ∈ equations := by
    change (equations.equivFin.symm i).1 ∈ equations
    exact (equations.equivFin.symm i).2
  apply exists_bounded_nonzero_integralJacobianMinor_of_polynomial_bounds
    (indexedFinsetFamily equations) x hregular
  · intro i
    exact support_card_le_equationFamilySupportBound
      (hmem i)
  · intro i μ hμ
    exact coeff_natAbs_le_equationFamilyCoefficientBound
      (hmem i) hμ
  · intro i
    exact totalDegree_le_equationFamilyDegreeBound
      (hmem i)
  · exact hx

/-- The corresponding normalized minor is nonzero for every positive affine
scale, and its exact factorization is visible. -/
theorem exists_depthSeven_transformed_nonzero_jacobianMinor
    (equations : Finset (MvPolynomial (Fin 13) ℤ))
    (x₀ z : IntVector 13) (m Y : ℕ) (hm : 0 < m)
    (hregular : IsDepthSevenJacobianRegularAt equations
      (integralAffineMap x₀ z m))
    (hx : ∀ j, (integralAffineMap x₀ z m j).natAbs ≤ Y) :
    ∃ rows : Fin 7 → Fin equations.card,
      ∃ cols : Fin 7 → Fin 13,
        integralJacobianMinor
          (integralAffineTransformFamily x₀ m
            (indexedFinsetFamily equations)) z rows cols ≠ 0 := by
  obtain ⟨rows, cols, _hrows, _hcols, hminor, _hbound⟩ :=
    exists_depthSeven_bounded_nonzero_jacobianMinor
      equations (integralAffineMap x₀ z m) Y hregular hx
  refine ⟨rows, cols, ?_⟩
  rw [integralJacobianMinor_transform]
  exact mul_ne_zero (pow_ne_zero 7 (by exact_mod_cast hm.ne')) hminor

end

end TranslatedDepthSeven
