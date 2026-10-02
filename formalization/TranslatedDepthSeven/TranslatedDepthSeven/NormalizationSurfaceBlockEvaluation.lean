import TranslatedDepthSeven.AffinePlaneMonomialEvaluation
import TranslatedDepthSeven.LinearNormalizationMonomialIndependence
import TranslatedDepthSeven.SquarefreeDeterminantAssembly

/-!
# Evaluation of a complete surface-normalization block

If `G_i` are auxiliary module elements and `m_u` runs through the complete
degree-`k` monomial block in three normalization variables, the determinant
method uses the products `G_i m_u`.  This file proves their common
homogeneous degree and the exact columnwise determinant estimate.  The
normalization variables contribute the sharp exponent
`card(I) * affinePlaneMonomialWeight k`; the auxiliary elements contribute
only their displayed individual evaluation bounds.
-/

namespace TranslatedDepthSeven

noncomputable section

open MvPolynomial
open scoped BigOperators

universe u v

/-- The ambient polynomial representing one element of the complete
normalization block. -/
def normalizationSurfaceBlockForm
    {σ : Type*} {R : Type u} [CommSemiring R]
    {I : Type v} (L : Fin 3 → MvPolynomial σ R)
    (G : I → MvPolynomial σ R) (k : ℕ)
    (p : I × AffinePlaneMonomialIndex k) : MvPolynomial σ R :=
  G p.1 * MvPolynomial.aeval L
    (affinePlaneHomogeneousMonomial R k p.2)

/-- If the auxiliary elements have common degree `b` and the normalization
coordinates are linear, every element of the block has common degree
`b+k`. -/
theorem normalizationSurfaceBlockForm_isHomogeneous
    {σ : Type*} {R : Type u} [CommSemiring R]
    {I : Type v} (L : Fin 3 → MvPolynomial σ R)
    (G : I → MvPolynomial σ R) (b k : ℕ)
    (hL : ∀ i, (L i).IsHomogeneous 1)
    (hG : ∀ i, (G i).IsHomogeneous b)
    (p : I × AffinePlaneMonomialIndex k) :
    (normalizationSurfaceBlockForm L G k p).IsHomogeneous (b + k) := by
  apply (hG p.1).mul
  simpa using
    (affinePlaneHomogeneousMonomial_isHomogeneous R k p.2).aeval L hL

/-- A pointwise bound for one column of the complete normalization block. -/
theorem eval_normalizationSurfaceBlockForm_natAbs_le
    {σ : Type*} {I : Type v}
    (L : Fin 3 → MvPolynomial σ ℤ)
    (G : I → MvPolynomial σ ℤ)
    (y : σ → ℤ) (D : I → ℕ) (R k : ℕ)
    (p : I × AffinePlaneMonomialIndex k)
    (hG : (MvPolynomial.eval y (G p.1)).natAbs ≤ D p.1)
    (hzero : MvPolynomial.eval y (L 0) = 1)
    (hone : (MvPolynomial.eval y (L 1)).natAbs ≤ R)
    (htwo : (MvPolynomial.eval y (L 2)).natAbs ≤ R) :
    (MvPolynomial.eval y
      (normalizationSurfaceBlockForm L G k p)).natAbs ≤
        D p.1 * R ^ affinePlaneMonomialIndexWeight p.2 := by
  rw [normalizationSurfaceBlockForm, map_mul, Int.natAbs_mul]
  exact Nat.mul_le_mul hG
    (eval_aeval_affinePlaneHomogeneousMonomial_natAbs_le
      L y R k p.2 hzero hone htwo)

/-- The product of all column bounds in a complete rank-`e`
normalization block. -/
theorem prod_normalizationSurfaceBlock_bounds
    {I : Type v} [Fintype I]
    (D : I → ℕ) (R k : ℕ) :
    ∏ p : I × AffinePlaneMonomialIndex k,
        (D p.1 * R ^ affinePlaneMonomialIndexWeight p.2) =
      (∏ i, D i) ^ affinePlaneMonomialCount k *
        R ^ (Fintype.card I * affinePlaneMonomialWeight k) := by
  classical
  rw [Fintype.prod_prod_type]
  simp_rw [Finset.prod_mul_distrib]
  congr 1
  · simp only [Finset.prod_const, Finset.card_univ,
      card_affinePlaneMonomialIndex]
    exact Finset.prod_pow Finset.univ (affinePlaneMonomialCount k) D
  · simp_rw [Finset.prod_pow_eq_pow_sum Finset.univ
      affinePlaneMonomialIndexWeight R,
      sum_affinePlaneMonomialIndexWeight]
    rw [Finset.prod_const, Finset.card_univ, ← pow_mul]
    congr 1
    exact Nat.mul_comm _ _

/-- The square evaluation determinant for the complete normalization block
has the exact total affine-weight bound. -/
theorem det_normalizationSurfaceBlockEvaluation_natAbs_le
    {σ : Type*} {I : Type v} [Fintype I] [DecidableEq I]
    (L : Fin 3 → MvPolynomial σ ℤ)
    (G : I → MvPolynomial σ ℤ)
    (D : I → ℕ) (R k : ℕ)
    (y : I × AffinePlaneMonomialIndex k → σ → ℤ)
    (hG : ∀ v i, (MvPolynomial.eval (y v) (G i)).natAbs ≤ D i)
    (hzero : ∀ v, MvPolynomial.eval (y v) (L 0) = 1)
    (hone : ∀ v, (MvPolynomial.eval (y v) (L 1)).natAbs ≤ R)
    (htwo : ∀ v, (MvPolynomial.eval (y v) (L 2)).natAbs ≤ R) :
    let A : Matrix (I × AffinePlaneMonomialIndex k)
        (I × AffinePlaneMonomialIndex k) ℤ :=
      Matrix.of (fun v p ↦ MvPolynomial.eval (y v)
        (normalizationSurfaceBlockForm L G k p))
    A.det.natAbs ≤
      (Fintype.card (I × AffinePlaneMonomialIndex k)).factorial *
        (∏ i, D i) ^ affinePlaneMonomialCount k *
          R ^ (Fintype.card I * affinePlaneMonomialWeight k) := by
  classical
  dsimp only
  have hdet := det_natAbs_le_factorial_mul_prod_column_bounds
    (Matrix.of (fun v p ↦ MvPolynomial.eval (y v)
      (normalizationSurfaceBlockForm L G k p)))
    (fun p ↦ D p.1 * R ^ affinePlaneMonomialIndexWeight p.2)
    (fun v p ↦ eval_normalizationSurfaceBlockForm_natAbs_le
      L G (y v) D R k p (hG v p.1) (hzero v) (hone v) (htwo v))
  rw [prod_normalizationSurfaceBlock_bounds] at hdet
  simpa only [mul_assoc] using hdet

/-- The complete global determinant comparison for a surface-normalization
block.  Once each prime dividing the square-free modulus supplies the stated
local divisibility, the explicit normalization-block height estimate forces
the integral evaluation determinant to vanish. -/
theorem det_normalizationSurfaceBlockEvaluation_eq_zero
    {σ : Type*} {I : Type v} [Fintype I] [DecidableEq I]
    (L : Fin 3 → MvPolynomial σ ℤ)
    (G : I → MvPolynomial σ ℤ)
    (D : I → ℕ) (R k q r : ℕ)
    (y : I × AffinePlaneMonomialIndex k → σ → ℤ)
    (hq : Squarefree q)
    (hlocal : ∀ p, p.Prime → p ∣ q →
      (p : ℤ) ^ r ∣
        (Matrix.of (fun v u ↦ MvPolynomial.eval (y v)
          (normalizationSurfaceBlockForm L G k u))).det)
    (hG : ∀ v i, (MvPolynomial.eval (y v) (G i)).natAbs ≤ D i)
    (hzero : ∀ v, MvPolynomial.eval (y v) (L 0) = 1)
    (hone : ∀ v, (MvPolynomial.eval (y v) (L 1)).natAbs ≤ R)
    (htwo : ∀ v, (MvPolynomial.eval (y v) (L 2)).natAbs ≤ R)
    (hlarge :
      (Fintype.card (I × AffinePlaneMonomialIndex k)).factorial *
          (∏ i, D i) ^ affinePlaneMonomialCount k *
            R ^ (Fintype.card I * affinePlaneMonomialWeight k) < q ^ r) :
    (Matrix.of (fun v u ↦ MvPolynomial.eval (y v)
      (normalizationSurfaceBlockForm L G k u))).det = 0 := by
  classical
  let A : Matrix (I × AffinePlaneMonomialIndex k)
      (I × AffinePlaneMonomialIndex k) ℤ :=
    Matrix.of (fun v u ↦ MvPolynomial.eval (y v)
      (normalizationSurfaceBlockForm L G k u))
  apply det_eq_zero_of_squarefree_local_divisibility_and_column_bounds
    A (fun u ↦ D u.1 * R ^ affinePlaneMonomialIndexWeight u.2)
      q r hq
  · simpa only [A] using hlocal
  · intro v u
    exact eval_normalizationSurfaceBlockForm_natAbs_le
      L G (y v) D R k u (hG v u.1) (hzero v) (hone v) (htwo v)
  · rw [prod_normalizationSurfaceBlock_bounds]
    simpa only [mul_assoc] using hlarge

end

end TranslatedDepthSeven
