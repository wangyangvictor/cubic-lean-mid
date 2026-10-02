import CubicTenVariables.LocalizedRestrictedMultiplicativity

/-! Ordinary complete-sum CRT at the unchanged integer frequency.
These are specializations of the proved localized identities to modulus-one
localization and the full residue set. Homogeneity supplies the actual unit
change of variables that removes the CRT frequency twists. -/

set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.CompleteSumMultiplicativity
open MvPolynomial LocalizedFinitePrimeAssembly
open scoped BigOperators

variable {n d : ℕ}

/-- The literal complete sums multiply at the same v. The statement also
includes zero and unit moduli with their actual finite-sum normalizations. -/
theorem mul (F : MvPolynomial (Fin n) ℤ) (hF : F.IsHomogeneous d)
    (q₀ q₁ : ℕ) (hcop : q₀.Coprime q₁) (v : Fin n → ℤ) :
    completeCubicSum F (q₀*q₁) v = completeCubicSum F q₀ v * completeCubicSum F q₁ v := by
  by_cases h₀ : q₀ = 0
  · simp [h₀]
  by_cases h₁ : q₁ = 0
  · simp [h₁]
  letI : NeZero q₀ := ⟨h₀⟩
  letI : NeZero q₁ := ⟨h₁⟩
  simpa only [localizedCompleteCubicSum_univ_one] using
    LocalizedRestrictedMultiplicativity.localized_mul_outside F hF q₀ q₁ 1
      (by simpa only [Nat.mul_one] using hcop) Set.univ (ResidueUnitInvariant.univ n 1) v

theorem norm_mul (F : MvPolynomial (Fin n) ℤ) (hF : F.IsHomogeneous d)
    (q₀ q₁ : ℕ) (hcop : q₀.Coprime q₁) (v : Fin n → ℤ) :
    ‖completeCubicSum F (q₀*q₁) v‖ = ‖completeCubicSum F q₀ v‖ * ‖completeCubicSum F q₁ v‖ := by
  rw [mul F hF q₀ q₁ hcop v, _root_.norm_mul]

/-- Finite prime-power factorization includes exponent-zero factors and
the empty prime set. All factors retain the original integer frequency. -/
theorem prime_powers_product (F : MvPolynomial (Fin n) ℤ) (hF : F.IsHomogeneous d)
    (s : Finset ℕ) (k : ℕ → ℕ) (hprimes : ∀ p ∈ s, p.Prime) (v : Fin n → ℤ) :
    completeCubicSum F (∏ p ∈ s, p^(k p)) v =
      ∏ p ∈ s, completeCubicSum F (p^(k p)) v := by
  have h := LocalizedRestrictedMultiplicativity.localized_product F hF s k (fun _ => 0)
    (fun _ => Set.univ) hprimes (fun p _ => ResidueUnitInvariant.univ n (p^0)) v
  have hM : modulus s (fun _ => 0) = 1 := by
    exact Finset.prod_eq_one (fun p _ => pow_zero p)
  have hΩ : restriction s (fun _ => 0) (fun p => (Set.univ : Set (Fin n → ZMod (p^0)))) =
      Set.univ := by
    ext x
    simp only [restriction,restrictionAt,Set.mem_setOf_eq,Set.mem_univ,implies_true]
  rw [hΩ,hM,localizedCompleteCubicSum_univ_one] at h
  exact h.trans (Finset.prod_congr rfl (fun p _ =>
    localizedCompleteCubicSum_univ_one F (p^(k p)) v))

/-- Factorization over an arbitrary finite prime superset of the support. -/
theorem factorization (F : MvPolynomial (Fin n) ℤ) (hF : F.IsHomogeneous d)
    (q : ℕ) (hq : q ≠ 0) (s : Finset ℕ) (hs : q.primeFactors ⊆ s)
    (hprimes : ∀ p ∈ s, p.Prime) (v : Fin n → ℤ) :
    completeCubicSum F q v = ∏ p ∈ s, completeCubicSum F (p^(q.factorization p)) v := by
  have h := prime_powers_product F hF s q.factorization hprimes v
  have he : (∏ p ∈ s, p^(q.factorization p)) = q :=
    LocalizedRestrictedMultiplicativity.modulus_factorization_eq q hq s hs
  rwa [he] at h

theorem prime_factorization (F : MvPolynomial (Fin n) ℤ) (hF : F.IsHomogeneous d)
    (q : ℕ) (hq : q ≠ 0) (v : Fin n → ℤ) :
    completeCubicSum F q v =
      ∏ p ∈ q.primeFactors, completeCubicSum F (p^(q.factorization p)) v :=
  factorization F hF q hq q.primeFactors (by rfl)
    (fun _ hp => Nat.prime_of_mem_primeFactors hp) v

theorem norm_prime_factorization (F : MvPolynomial (Fin n) ℤ) (hF : F.IsHomogeneous d)
    (q : ℕ) (hq : q ≠ 0) (v : Fin n → ℤ) :
    ‖completeCubicSum F q v‖ =
      ∏ p ∈ q.primeFactors, ‖completeCubicSum F (p^(q.factorization p)) v‖ := by
  rw [prime_factorization F hF q hq v, norm_prod]

/-- A squarefree factor contributes exactly its ordinary prime sums. -/
theorem squarefree_product (F : MvPolynomial (Fin n) ℤ) (hF : F.IsHomogeneous d)
    (q : ℕ) (hq : Squarefree q) (v : Fin n → ℤ) :
    completeCubicSum F q v = ∏ p ∈ q.primeFactors, completeCubicSum F p v := by
  rw [prime_factorization F hF q hq.ne_zero v]
  apply Finset.prod_congr rfl
  intro p hp
  rw [Nat.factorization_eq_one_of_squarefree hq (Nat.prime_of_mem_primeFactors hp)
    (Nat.dvd_of_mem_primeFactors hp), pow_one]

/-- Squaring a squarefree factor contributes exactly its prime-square sums. -/
theorem squarefree_square_product (F : MvPolynomial (Fin n) ℤ)
    (hF : F.IsHomogeneous d) (q : ℕ) (hq : Squarefree q) (v : Fin n → ℤ) :
    completeCubicSum F (q^2) v = ∏ p ∈ q.primeFactors, completeCubicSum F (p^2) v := by
  have h := prime_powers_product F hF q.primeFactors (fun _ => 2)
    (fun _ hp => Nat.prime_of_mem_primeFactors hp) v
  simpa only [Finset.prod_pow, Nat.prod_primeFactors_of_squarefree hq] using h

/-- The exact ordinary/square-prime decomposition needed by the cube-free
conductor argument, with both squarefree factors and their coprimality explicit. -/
theorem squarefree_pair_product (F : MvPolynomial (Fin n) ℤ)
    (hF : F.IsHomogeneous d) (a b : ℕ) (ha : Squarefree a) (hb : Squarefree b)
    (hab : a.Coprime b) (v : Fin n → ℤ) :
    completeCubicSum F (a*b^2) v =
      (∏ p ∈ a.primeFactors, completeCubicSum F p v) *
      (∏ p ∈ b.primeFactors, completeCubicSum F (p^2) v) := by
  rw [mul F hF a (b^2) (hab.pow_right 2) v,
    squarefree_product F hF a ha v,squarefree_square_product F hF b hb v]

theorem norm_squarefree_pair_product (F : MvPolynomial (Fin n) ℤ)
    (hF : F.IsHomogeneous d) (a b : ℕ) (ha : Squarefree a) (hb : Squarefree b)
    (hab : a.Coprime b) (v : Fin n → ℤ) :
    ‖completeCubicSum F (a*b^2) v‖ =
      (∏ p ∈ a.primeFactors, ‖completeCubicSum F p v‖) *
      (∏ p ∈ b.primeFactors, ‖completeCubicSum F (p^2) v‖) := by
  rw [squarefree_pair_product F hF a b ha hb hab v,_root_.norm_mul,norm_prod,norm_prod]

end CubicTenVariables.CompleteSumMultiplicativity
