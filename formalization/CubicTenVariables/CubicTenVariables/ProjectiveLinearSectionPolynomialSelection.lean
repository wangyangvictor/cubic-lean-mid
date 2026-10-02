import CubicTenVariables.ProjectiveLinearSectionVariance
import Mathlib.Algebra.MvPolynomial.SchwartzZippel

/-! # Selecting a linear section outside a polynomial zero set

The polynomial is a literal, supplied nonzero polynomial in the entries of
an ordered tuple of linear equations. Schwartz--Zippel shows that its
nonvanishing set contains more than half of all tuples when `q > 2D`.
The variance identity then selects a tuple with a controlled point count.
No existence of a discriminant or geometric smoothness assertion is assumed
or proved here. Zero parameters are allowed in the polynomial counting step.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace CubicTenVariables.ProjectiveLinearSectionVariance

variable {K : Type*} [Field K] [Fintype K] {m n k D : ℕ}

/-- A nonzero polynomial of degree at most `D` does not vanish at more than
half of the full affine parameter space if the field has more than `2D`
elements. This includes a polynomial in zero variables. -/
theorem card_polynomial_nonvanishing_gt_half
    (Δ : MvPolynomial (Fin m) K) (hΔ : Δ ≠ 0)
    (hdegree : Δ.totalDegree ≤ D) (hq : 2 * D < Nat.card K) :
    Fintype.card (Fin m → K) <
      2 * (Finset.univ.filter fun x : Fin m → K => MvPolynomial.eval x Δ ≠ 0).card := by
  classical
  let Z := Finset.univ.filter fun x : Fin m → K => MvPolynomial.eval x Δ = 0
  have hratio : (Z.card : ℚ≥0) / (Nat.card K : ℚ≥0) ^ m ≤
      (Δ.totalDegree : ℚ≥0) / Nat.card K := by
    simpa [Z, Nat.card_eq_fintype_card] using
      (MvPolynomial.schwartz_zippel_totalDegree hΔ (Finset.univ : Finset K))
  have hqpos : (0 : ℚ≥0) < Nat.card K := by
    exact_mod_cast (Nat.card_pos : 0 < Nat.card K)
  have hsmall : (Δ.totalDegree : ℚ≥0) / Nat.card K < 1 / 2 := by
    apply (div_lt_div_iff₀ hqpos (by norm_num)).mpr
    have hd : 2 * Δ.totalDegree < Nat.card K := lt_of_le_of_lt
      (Nat.mul_le_mul_left 2 hdegree) hq
    norm_num only [one_mul]
    exact_mod_cast (by omega : Δ.totalDegree * 2 < Nat.card K)
  have hz : 2 * Z.card < Fintype.card (Fin m → K) := by
    have hz' := (div_lt_iff₀ (pow_pos hqpos m)).mp (hratio.trans_lt hsmall)
    have hz'' : (2 : ℚ≥0) * Z.card < (Nat.card K : ℚ≥0) ^ m := by
      calc
        (2 : ℚ≥0) * Z.card < 2 * ((1 / 2) * (Nat.card K : ℚ≥0) ^ m) :=
          mul_lt_mul_of_pos_left hz' (by norm_num)
        _ = (Nat.card K : ℚ≥0) ^ m := by norm_num [← mul_assoc]
    simpa [Nat.card_eq_fintype_card] using (show 2 * Z.card < Nat.card K ^ m by
      exact_mod_cast hz'')
  have hpartition := Finset.filter_card_add_filter_neg_card_eq_card
    (s := Finset.univ) (fun x : Fin m → K => MvPolynomial.eval x Δ = 0)
  change Z.card +
    (Finset.univ.filter fun x : Fin m → K => MvPolynomial.eval x Δ ≠ 0).card =
    Fintype.card (Fin m → K) at hpartition
  omega

/-- The literal affine zero-count estimate for a supplied nonzero
polynomial in `m+1` variables. For a ten-variable cubic this gives `3q^9`. -/
theorem card_affine_polynomial_zeros_le_degree_mul
    (F : MvPolynomial (Fin (m + 1)) K) (hF : F ≠ 0)
    (hdegree : F.totalDegree ≤ D) :
    (Finset.univ.filter fun x : Fin (m + 1) → K => MvPolynomial.eval x F = 0).card ≤
      D * Nat.card K ^ m := by
  classical
  let Z := Finset.univ.filter fun x : Fin (m + 1) → K => MvPolynomial.eval x F = 0
  have hratio : (Z.card : ℚ≥0) / (Nat.card K : ℚ≥0) ^ (m + 1) ≤
      (F.totalDegree : ℚ≥0) / Nat.card K := by
    simpa [Z, Nat.card_eq_fintype_card] using
      (MvPolynomial.schwartz_zippel_totalDegree hF (Finset.univ : Finset K))
  have hqpos : (0 : ℚ≥0) < Nat.card K := by
    exact_mod_cast (Nat.card_pos : 0 < Nat.card K)
  have hmul := (div_le_div_iff₀ (pow_pos hqpos (m + 1)) hqpos).mp hratio
  have hcount : (Z.card : ℚ≥0) ≤ F.totalDegree * (Nat.card K : ℚ≥0) ^ m := by
    apply (mul_le_mul_iff_left₀ hqpos).mp
    simpa [pow_succ, mul_comm, mul_left_comm, mul_assoc] using hmul
  have hcountNat : Z.card ≤ F.totalDegree * Nat.card K ^ m := by exact_mod_cast hcount
  exact hcountNat.trans (Nat.mul_le_mul_right _ hdegree)

/-- Flatten the entries of an ordered tuple of normals. The entry `(j,i)`
corresponds to `finProdFinEquiv (j,i)` in `Fin (k*n)`. -/
def normalTupleCoordinates : (Fin k → Fin n → K) ≃ (Fin (k * n) → K) where
  toFun γ a := γ (finProdFinEquiv.symm a).1 (finProdFinEquiv.symm a).2
  invFun x j i := x (finProdFinEquiv (j, i))
  left_inv γ := by funext j i; simp
  right_inv x := by
    funext a
    change x (finProdFinEquiv (finProdFinEquiv.symm a)) = x a
    rw [Equiv.apply_symm_apply]

/-- The literal nonvanishing tuples, including all possible zero or
dependent normals whenever the supplied polynomial is nonzero there. -/
def polynomialNonvanishingTuples (Δ : MvPolynomial (Fin (k * n)) K) :
    Finset (Fin k → Fin n → K) :=
  Finset.univ.filter fun γ => MvPolynomial.eval (normalTupleCoordinates γ) Δ ≠ 0

@[simp]
theorem mem_polynomialNonvanishingTuples
    (Δ : MvPolynomial (Fin (k * n)) K) (γ : Fin k → Fin n → K) :
    γ ∈ polynomialNonvanishingTuples Δ ↔
      MvPolynomial.eval (normalTupleCoordinates γ) Δ ≠ 0 := by
  simp [polynomialNonvanishingTuples]

/-- The good tuples occupy more than half of the full affine tuple space;
there is no conditioning on independence of the equations. -/
theorem card_polynomialNonvanishingTuples_gt_half
    (Δ : MvPolynomial (Fin (k * n)) K) (hΔ : Δ ≠ 0)
    (hdegree : Δ.totalDegree ≤ D) (hq : 2 * D < Nat.card K) :
    Fintype.card (Fin k → Fin n → K) < 2 * (polynomialNonvanishingTuples Δ).card := by
  have hcount : (polynomialNonvanishingTuples Δ).card =
      (Finset.univ.filter fun x : Fin (k * n) → K => MvPolynomial.eval x Δ ≠ 0).card := by
    apply Finset.card_equiv normalTupleCoordinates
    intro γ
    simp
  rw [hcount, Fintype.card_congr (normalTupleCoordinates (K := K) (k := k) (n := n))]
  exact card_polynomial_nonvanishing_gt_half Δ hΔ hdegree hq

/-- Select a polynomial-nonvanishing tuple with the variance bound for an
arbitrary finite set of actual projective points. Smoothness of any section
requires a separate geometric assertion about the polynomial. -/
theorem exists_polynomial_nonvanishing_section (hn : 2 ≤ n)
    (S : Finset (Projectivization K (Fin n → K)))
    (Δ : MvPolynomial (Fin (k * n)) K) (hΔ : Δ ≠ 0)
    (hdegree : Δ.totalDegree ≤ D) (hq : 2 * D < Nat.card K) :
    ∃ γ : Fin k → Fin n → K,
      MvPolynomial.eval (normalTupleCoordinates γ) Δ ≠ 0 ∧
      ((S.card : ℝ) - (Nat.card K : ℝ) ^ k * (sectionCount S γ : ℝ)) ^ 2 ≤
        2 * (S.card : ℝ) * ((Nat.card K : ℝ) ^ k - 1) := by
  obtain ⟨γ, hγ, hbound⟩ := exists_good_section_of_card hn S
    (polynomialNonvanishingTuples Δ)
    (card_polynomialNonvanishingTuples_gt_half Δ hΔ hdegree hq)
  exact ⟨γ, (mem_polynomialNonvanishingTuples Δ γ).mp hγ, hbound⟩

end CubicTenVariables.ProjectiveLinearSectionVariance
