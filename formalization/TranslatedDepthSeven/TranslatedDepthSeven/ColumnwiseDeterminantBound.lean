import Mathlib.LinearAlgebra.Matrix.AbsoluteValue

/-!
# A columnwise determinant bound

The affine determinant method needs the product of the individual monomial
bounds, not the power of one worst bound.  The following is the direct
columnwise version of `Matrix.det_le`; its proof is the Leibniz formula and
the triangle inequality.
-/

namespace TranslatedDepthSeven

noncomputable section

open Matrix Equiv Finset
open scoped BigOperators Nat

universe u v

/-- If column `j` is bounded by `x j`, the determinant is bounded by
`n! * ∏ j, x j`. -/
theorem det_le_prod_column_bounds
    {R : Type u} {S : Type v}
    [CommRing R] [Nontrivial R]
    [CommRing S] [LinearOrder S] [IsStrictOrderedRing S]
    {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n R} {abv : AbsoluteValue R S} {x : n → S}
    (hx : ∀ i j, abv (A i j) ≤ x j) :
    abv A.det ≤ (Fintype.card n)! • ∏ j, x j := by
  calc
    abv A.det =
        abv (∑ σ : Equiv.Perm n,
          Equiv.Perm.sign σ • ∏ i, A (σ i) i) :=
      congrArg abv (Matrix.det_apply A)
    _ ≤ ∑ σ : Equiv.Perm n,
        abv (Equiv.Perm.sign σ • ∏ i, A (σ i) i) :=
      abv.sum_le _ _
    _ = ∑ σ : Equiv.Perm n, ∏ i, abv (A (σ i) i) := by
      apply Finset.sum_congr rfl
      intro σ _
      rw [abv.map_units_int_smul, abv.map_prod]
    _ ≤ ∑ _σ : Equiv.Perm n, ∏ i, x i := by
      gcongr
      exact hx _ _
    _ = (Fintype.card n)! • ∏ j, x j := by
      simp [Fintype.card_perm]

/-- Integer form with natural absolute values and explicit factorial. -/
theorem det_natAbs_le_factorial_mul_prod_column_bounds
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℤ) (C : ι → ℕ)
    (hentry : ∀ i j, (A i j).natAbs ≤ C j) :
    A.det.natAbs ≤ (Fintype.card ι).factorial * ∏ j, C j := by
  have hentryZ : ∀ i j, |A i j| ≤ (C j : ℤ) := by
    intro i j
    rw [Int.abs_eq_natAbs]
    exact_mod_cast hentry i j
  have h := det_le_prod_column_bounds
    (A := A) (abv := (AbsoluteValue.abs : AbsoluteValue ℤ ℤ))
    (x := fun j ↦ (C j : ℤ)) hentryZ
  simp only [nsmul_eq_mul] at h
  change |A.det| ≤ ((Fintype.card ι).factorial : ℤ) *
    ∏ j, (C j : ℤ) at h
  rw [Int.abs_eq_natAbs] at h
  exact_mod_cast h

end

end TranslatedDepthSeven
