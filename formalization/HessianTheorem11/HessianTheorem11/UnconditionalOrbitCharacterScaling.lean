import HessianTheorem11.UnconditionalOrbitDiagonalCharacters

/-! Exact evaluation identities for coefficient-equation eigenvectors
under arbitrary determinant-one diagonals. -/
noncomputable section
namespace HessianTheorem11.UnconditionalOrbitIdeal
open MvPolynomial
variable {K : Type*} [Field K] {n d : ℕ}

theorem eval_monomial_coefficientDiagonal (δ : Fin n → Kˣ)
    (x : DegreeIndex n d → K) (e : DegreeIndex n d →₀ ℕ) (c : K) :
    eval (fun m => (coefficientDiagonal δ m : K) * x m) (monomial e c) =
      ((diagonalCharacterFactor δ e : Kˣ) : K) * eval x (monomial e c) := by
  classical
  rw [eval_monomial,eval_monomial]
  rw [Finsupp.prod_fintype _ _ (by simp),Finsupp.prod_fintype _ _ (by simp)]
  simp only [mul_pow,Finset.prod_mul_distrib]
  have h := congrArg (fun u : Kˣ => (u : K)) (coefficientDiagonal_monomial δ e)
  simp only [Units.coe_prod,Units.val_pow_eq_pow_val] at h
  rw [h]
  ring

/-- Every polynomial whose supported monomials share a character is an
actual diagonal eigenvector, over any field and at every coefficient point. -/
theorem eval_characterPolynomial_coefficientDiagonal (hn : 0 < n)
    (δ : Fin n → Kˣ) (hδ : ∏ i, δ i = 1) (x : DegreeIndex n d → K)
    (P : MvPolynomial (DegreeIndex n d) K) (e : DegreeIndex n d →₀ ℕ)
    (hP : ∀ f ∈ P.support, equationCharacter f = equationCharacter e) :
    eval (fun m => (coefficientDiagonal δ m : K) * x m) P =
      ((diagonalCharacterFactor δ e : Kˣ) : K) * eval x P := by
  classical
  calc
    _ = ∑ f ∈ P.support,
        eval (fun m => (coefficientDiagonal δ m : K) * x m) (monomial f (coeff f P)) := by
      simpa only [map_sum] using congrArg (eval (fun m => (coefficientDiagonal δ m : K) * x m)) P.as_sum
    _ = ∑ f ∈ P.support, ((diagonalCharacterFactor δ e : Kˣ) : K) * eval x (monomial f (coeff f P)) := by
      apply Finset.sum_congr rfl
      intro f hf
      rw [eval_monomial_coefficientDiagonal,diagonalCharacterFactor_eq hn δ hδ f e (hP f hf)]
    _ = _ := by rw [← Finset.mul_sum,← map_sum,← P.as_sum]

theorem eval_characterPart_coefficientDiagonal (hn : 0 < n)
    (δ : Fin n → Kˣ) (hδ : ∏ i, δ i = 1) (x : DegreeIndex n d → K)
    (P : MvPolynomial (DegreeIndex n d) K) (e : DegreeIndex n d →₀ ℕ) :
    eval (fun m => (coefficientDiagonal δ m : K) * x m) (characterPart P (equationCharacter e)) =
      ((diagonalCharacterFactor δ e : Kˣ) : K) * eval x (characterPart P (equationCharacter e)) := by
  apply eval_characterPolynomial_coefficientDiagonal hn δ hδ x _ e
  intro f hf
  have hc := mem_support_iff.mp hf
  rw [coeff_characterPart] at hc
  split_ifs at hc with he
  · exact he
  · exact (hc rfl).elim

theorem diagonalCharacterFactor_pow (δ : Fin n → Kˣ) (hδ : ∏ i, δ i = 1)
    (e : DegreeIndex n d →₀ ℕ) :
    diagonalCharacterFactor δ e ^ n = ∏ i, δ i ^ equationCharacter e i := by
  classical
  simp only [diagonalCharacterFactor,equationCharacter,zpow_sub,Finset.prod_mul_distrib,Finset.prod_inv_distrib]
  rw [Finset.prod_zpow,hδ,one_zpow,inv_one,mul_one,← Finset.prod_pow]
  apply Finset.prod_congr rfl
  intro i _
  rw [mul_comm (n : ℤ),zpow_mul,zpow_natCast]

/-- The nth-power version uses exactly the centered integral character
and therefore feeds valuation-group inequalities without choosing a root. -/
theorem eval_characterPolynomial_coefficientDiagonal_pow (hn : 0 < n)
    (δ : Fin n → Kˣ) (hδ : ∏ i, δ i = 1) (x : DegreeIndex n d → K)
    (P : MvPolynomial (DegreeIndex n d) K) (e : DegreeIndex n d →₀ ℕ)
    (hP : ∀ f ∈ P.support, equationCharacter f = equationCharacter e) :
    (eval (fun m => (coefficientDiagonal δ m : K) * x m) P) ^ n =
      (eval x P) ^ n * ∏ i, (δ i : K) ^ equationCharacter e i := by
  rw [eval_characterPolynomial_coefficientDiagonal hn δ hδ x P e hP,mul_pow]
  have h := congrArg (fun u : Kˣ => (u : K)) (diagonalCharacterFactor_pow δ hδ e)
  simp only [Units.val_pow_eq_pow_val,Units.coe_prod,Units.val_zpow_eq_zpow_val] at h
  rw [h,mul_comm]

end HessianTheorem11.UnconditionalOrbitIdeal
