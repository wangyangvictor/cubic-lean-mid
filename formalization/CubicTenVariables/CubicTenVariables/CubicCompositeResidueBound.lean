import CubicTenVariables.CubicPrimeFactorLocalBound
import CubicTenVariables.CompositeResidueProducts
import CubicTenVariables.PrimeFactorEpsilonBound

/-!
# The ten-variable composite c/d root-count bound

The source's literal squarefree factors and vector gcds are used. The
finite prime-factor assembly and epsilon absorption are proved internally.
The unrestricted prime-power root bound is proved by finite differencing.
-/

noncomputable section
namespace CubicTenVariables.CubicCompositeResidueBound
open MvPolynomial SquarefreeResidueFactors PolynomialRootPrimeFactorization
open scoped BigOperators

/-- Before epsilon absorption, the overhead consists exactly of factors
K times the prime valuations of the quotient c/d. -/
theorem exists_finite_product_bound
    
    (F : MvPolynomial (Fin 10) ℤ) (hF : F.IsHomogeneous 3)
    (hA : HessianTheorem11.Anisotropic (map (Int.castRingHom ℚ) F)) :
    ∃ K : ℕ, 1 ≤ K ∧
      ∀ (c d : ℕ) (_hc : 0 < c) (_hd : Squarefree d) (hdc : d ∣ c)
        (k : Fin 10 → ℤ), (d : ℤ) ∣ eval k F →
        count F k c d hdc ≤
          (c/d)^9 * vectorGcd (d2 c d) (fun i => eval k (pderiv i F)) *
            vectorGcd (d2 c d) k *
              (∏ p ∈ (c/d).primeFactors, K*(c/d).factorization p) := by
  obtain ⟨K,hK,hlocal⟩ :=
    CubicPrimeFactorLocalBound.exists_uniform_prime_factor_bound  F hF hA
  refine ⟨K,hK,?_⟩
  intro c d hc hd hdc k hk
  rw [count_eq_prod_primeFactors F k c d hc.ne' hdc]
  have hprod := CompositeResidueProducts.prod_le_of_local_bounds
    (quotient_pos c d hc hd hdc).ne' hc.ne' (d2_pos c d hc hd hdc).ne'
    (Nat.div_dvd_of_dvd hdc) ((d2_dvd_left c d hc hd hdc).trans hdc)
    (fun p => count F k (p^c.factorization p) (Nat.gcd (p^c.factorization p) d)
      (Nat.gcd_dvd_left _ _))
    (fun p => vectorGcd p (fun i => eval k (pderiv i F)))
    (fun p => vectorGcd p k) (hlocal c d hc hd hdc k hk)
  simpa only [prod_primeFactors_vectorGcd (d2 c d) (d2_squarefree c d hc hd hdc)]
    using hprod

/-- The manuscript's full composite estimate for the actual constrained
root cardinality. The implied constant precedes c, d and the center k. -/
theorem exists_composite_root_bound
    
    (F : MvPolynomial (Fin 10) ℤ) (hF : F.IsHomogeneous 3)
    (hA : HessianTheorem11.Anisotropic (map (Int.castRingHom ℚ) F))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ A : ℝ, 1 ≤ A ∧
      ∀ (c d : ℕ) (_hc : 0 < c) (_hd : Squarefree d) (hdc : d ∣ c)
        (k : Fin 10 → ℤ), (d : ℤ) ∣ eval k F →
        (count F k c d hdc : ℝ) ≤
          A * ((c/d : ℕ) : ℝ) ^ (9 + ε) *
            vectorGcd (d2 c d) (fun i => eval k (pderiv i F)) * vectorGcd (d2 c d) k := by
  obtain ⟨K,hK,hfinite⟩ := exists_finite_product_bound  F hF hA
  obtain ⟨A,hA1,habsorb⟩ := PrimeFactorEpsilonBound.exists_uniform_prime_factor_bound K hK ε hε
  refine ⟨A,hA1,?_⟩
  intro c d hc hd hdc k hk
  have hm : 0 < c/d := quotient_pos c d hc hd hdc
  have hmR : (0 : ℝ) < (c/d : ℕ) := by exact_mod_cast hm
  have hf : (count F k c d hdc : ℝ) ≤
      ((c/d : ℕ) : ℝ)^9 *
        vectorGcd (d2 c d) (fun i => eval k (pderiv i F)) * vectorGcd (d2 c d) k *
          ((∏ p ∈ (c/d).primeFactors, K*(c/d).factorization p : ℕ) : ℝ) := by
    exact_mod_cast hfinite c d hc hd hdc k hk
  calc
    _ ≤ ((c/d : ℕ) : ℝ)^9 *
        vectorGcd (d2 c d) (fun i => eval k (pderiv i F)) * vectorGcd (d2 c d) k *
          ((∏ p ∈ (c/d).primeFactors, K*(c/d).factorization p : ℕ) : ℝ) := hf
    _ ≤ ((c/d : ℕ) : ℝ)^9 *
        vectorGcd (d2 c d) (fun i => eval k (pderiv i F)) * vectorGcd (d2 c d) k *
          (A * ((c/d : ℕ) : ℝ)^ε) :=
      mul_le_mul_of_nonneg_left (habsorb (c/d) hm) (by positivity)
    _ = _ := by
      rw [Real.rpow_add hmR]
      norm_num
      ring

/-- Literal finite-filter form, with no abstract count or local estimate
left as an argument. Positivity of d follows from its squarefreeness. -/
theorem exists_literal_composite_root_bound
    
    (F : MvPolynomial (Fin 10) ℤ) (hF : F.IsHomogeneous 3)
    (hA : HessianTheorem11.Anisotropic (map (Int.castRingHom ℚ) F))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ A : ℝ, 1 ≤ A ∧
      ∀ (c d : ℕ) (hc : 0 < c),
        letI : NeZero c := ⟨hc.ne'⟩
        ∀ (_hd : Squarefree d) (hdc : d ∣ c) (k : Fin 10 → ℤ),
          (d : ℤ) ∣ eval k F →
          ((Finset.univ.filter fun z : Fin 10 → ZMod c =>
            eval₂ (Int.castRingHom (ZMod c)) z F = 0 ∧
              ∀ i, ZMod.castHom hdc (ZMod d) (z i) = (k i : ZMod d)).card : ℝ) ≤
            A * ((c/d : ℕ) : ℝ) ^ (9 + ε) *
              vectorGcd (d2 c d) (fun i => eval k (pderiv i F)) * vectorGcd (d2 c d) k := by
  obtain ⟨A,hA1,hbound⟩ := exists_composite_root_bound  F hF hA ε hε
  refine ⟨A,hA1,?_⟩
  intro c d hc
  letI : NeZero c := ⟨hc.ne'⟩
  intro hd hdc k hk
  simpa only [count_eq_card] using hbound c d hc hd hdc k hk

end CubicTenVariables.CubicCompositeResidueBound
