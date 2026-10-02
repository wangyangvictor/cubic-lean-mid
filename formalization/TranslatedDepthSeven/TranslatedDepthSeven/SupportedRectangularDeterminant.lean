import TranslatedDepthSeven.ArbitrarySurfacePolynomialDeterminant

/-! The rectangular determinant expansion only needs a weight bound on
injective choices whose selected entries in the right factor are nonzero.
This retains the residue-class support condition in a block factorization. -/

namespace TranslatedDepthSeven
noncomputable section
open scoped BigOperators

/-- A selected-column determinant isolates the factor independent of the
permutation. This also makes cancellation for repeated columns explicit. -/
theorem rectangular_det_choice_sum
    {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι κ ℤ) (N : Matrix κ ι ℤ) (f : ι → κ) :
    (∑ σ : Equiv.Perm ι,
      Equiv.Perm.sign σ * ∏ i, M (σ i) (f i) * N (f i) i) =
      (Matrix.of (fun i j => M i (f j))).det * ∏ j, N (f j) j := by
  simp [Finset.prod_mul_distrib, ← mul_assoc, ← Finset.sum_mul,
    Matrix.det_apply', Matrix.of_apply]

/-- Nonzero supported choices suffice for the total-weight condition.
Off-block choices vanish; repeated choices cancel by the determinant. -/
theorem pow_dvd_det_rectangular_mul_of_supported_injective_weight
    {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ]
    (M : Matrix ι κ ℤ) (N : Matrix κ ι ℤ)
    (p : ℤ) (weight : κ → ℕ) (exponent : ℕ)
    (hN : ∀ a j, p ^ weight a ∣ N a j)
    (hweight : ∀ f : ι → κ, Function.Injective f →
      (∀ j, N (f j) j ≠ 0) → exponent ≤ ∑ j, weight (f j)) :
    p ^ exponent ∣ (M * N).det := by
  classical
  rw [det_rectangular_mul_expansion]
  apply Finset.dvd_sum
  intro f _
  rw [rectangular_det_choice_sum]
  by_cases hinj : Function.Injective f
  · by_cases hn : ∀ j, N (f j) j ≠ 0
    · have hprod : p ^ (∑ j, weight (f j)) ∣ ∏ j, N (f j) j := by
        have h := Finset.prod_dvd_prod_of_dvd (s := Finset.univ)
          (fun j => p ^ weight (f j)) (fun j => N (f j) j)
          (fun j _ => hN (f j) j)
        simpa only [Finset.prod_pow_eq_pow_sum] using h
      exact dvd_mul_of_dvd_right
        ((pow_dvd_pow p (hweight f hinj hn)).trans hprod) _
    · push_neg at hn
      obtain ⟨j, hj⟩ := hn
      rw [Finset.prod_eq_zero (f := fun j => N (f j) j) (Finset.mem_univ j) hj, mul_zero]
      exact dvd_zero _
  · rw [Function.Injective] at hinj
    push_neg at hinj
    obtain ⟨i, j, hij, hne⟩ := hinj
    rw [Matrix.det_zero_of_column_eq hne (fun k => by simp [hij]), zero_mul]
    exact dvd_zero _

/-- Distinct primes may contribute different exponents. -/
theorem primePowerProduct_dvd_of_local_divisibility
    (P : Finset ℕ) (e : ℕ → ℕ) (a : ℤ)
    (hP : ∀ p ∈ P, p.Prime)
    (hlocal : ∀ p ∈ P, (p : ℤ) ^ e p ∣ a) :
    (∏ p ∈ P, (p : ℤ) ^ e p) ∣ a := by
  apply Finset.prod_dvd_of_coprime _ hlocal
  intro p hp q hq hne
  exact (Nat.Coprime.pow (e p) (e q)
    ((Nat.coprime_primes (hP p hp) (hP q hq)).2 hne)).isCoprime

end
end TranslatedDepthSeven
