import CubicTenVariables.CubicPrimeFrogOneSharp
import CubicTenVariables.SquarefreeHessianMass

/-! Sharp squarefree half-Hessian root bounds, from the actual prime p^10
estimate and the existing exact CRT identity. No literature input. -/
set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.GcdWeightedHessianSharp
open MvPolynomial HessianTheorem11 SquarefreeResidueFactors PrimeFrogZeroMass
open WeightedHessianRootCRT SquarefullWeightedSums GcdWeightedHessianCRT
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {v : ℕ}

/-- A totalized scalar function, used only for the elementary factorization induction. -/
private def totalMass (F : MvPolynomial (Fin v) ℤ) (d : ℕ) : ℝ :=
  if hd : d = 0 then 0 else @gcdRootMass v F d ⟨hd⟩

private theorem totalMass_eq (F : MvPolynomial (Fin v) ℤ) (d : ℕ) [NeZero d] :
    totalMass F d = gcdRootMass F d := by simp only [totalMass, dif_neg (NeZero.ne d)]

private theorem totalMass_mul (F : MvPolynomial (Fin v) ℤ)
    (m n : ℕ) (hc : m.Coprime n) : totalMass F (m*n) = totalMass F m * totalMass F n := by
  by_cases hm : m = 0
  · subst m; simp [totalMass]
  by_cases hn : n = 0
  · subst n; simp [totalMass]
  letI : NeZero m := ⟨hm⟩
  letI : NeZero n := ⟨hn⟩
  simpa only [totalMass_eq] using gcdRootMass_mul F hc

private theorem totalMass_squarefree (F : MvPolynomial (Fin v) ℤ)
    (d : ℕ) (hd : Squarefree d) : totalMass F d = ∏ p ∈ d.primeFactors, totalMass F p := by
  have h := Nat.multiplicative_factorization (totalMass F) (totalMass_mul F)
    (by rw [totalMass_eq, gcdRootMass_one]) hd.ne_zero
  rw [Nat.prod_factorization_eq_prod_primeFactors] at h
  rw [h]
  apply Finset.prod_congr rfl
  intro p hp
  rw [Nat.factorization_eq_one_of_squarefree hd (Nat.prime_of_mem_primeFactors hp)
    (Nat.dvd_of_mem_primeFactors hp), pow_one]

/-- The prime j=1 theorem is a bound for exactly this literal full gcd mass. -/
theorem exists_uniform_prime_bound (F : MvPolynomial (Fin 10) ℤ)
    (hF : F.IsHomogeneous 3) (hA : Anisotropic (map (Int.castRingHom ℚ) F)) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (p : ℕ) (hp : p.Prime),
      letI : NeZero p := ⟨hp.ne_zero⟩
      gcdRootMass F p ≤ C*(p : ℝ)^(10 : ℝ) := by
  obtain ⟨C,hC,hbound⟩ := CubicPrimeFrogOneSharp.exists_uniform_sqrt_bound F hF hA
  refine ⟨C,hC,?_⟩
  intro p hp
  letI : NeZero p := ⟨hp.ne_zero⟩
  have hh := hbound p hp true true
  rw [show (p : ℝ)^(10 : ℝ) = (p : ℝ)^(10 : ℕ) from Real.rpow_natCast (p : ℝ) 10]
  simpa only [PrimeFrogOneMass.oneMass, PrimeFrogOneMass.optionalRootWeight_true_true,
    Finset.sum_filter, gcdRootMass, kernelWeight, mul_comm] using hh

/-- One constant covers every positive squarefree modulus, including one.
All primes are included; no literature or prime-exception input occurs. -/
theorem exists_uniform_squarefree_bound (F : MvPolynomial (Fin 10) ℤ)
    (hF : F.IsHomogeneous 3) (hA : Anisotropic (map (Int.castRingHom ℚ) F))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (d : ℕ) [NeZero d], Squarefree d →
      gcdRootMass F d ≤ C*(d : ℝ)^(10+ε) := by
  obtain ⟨C,hC,hprime⟩ := exists_uniform_prime_bound F hF hA
  let K : ℕ := ⌈C⌉₊
  have hK : C ≤ (K : ℝ) := Nat.le_ceil C
  have hK1 : 1 ≤ K := Nat.one_le_ceil_iff.mpr (zero_lt_one.trans_le hC)
  obtain ⟨B,hB,hcoeff⟩ := PrimeFactorEpsilonBound.exists_uniform_prime_factor_bound K hK1 ε hε
  refine ⟨B,hB,?_⟩
  intro d hd0 hd
  have hdpos : 0 < d := Nat.pos_of_ne_zero (NeZero.ne d)
  have hdR : 0 < (d : ℝ) := by exact_mod_cast hdpos
  have hlocal (p : ℕ) (hp : p ∈ d.primeFactors) :
      totalMass F p ≤ (K : ℝ)*(p : ℝ)^(10 : ℝ) := by
    have hp' := Nat.prime_of_mem_primeFactors hp
    letI : NeZero p := ⟨hp'.ne_zero⟩
    rw [totalMass_eq]
    exact (hprime p hp').trans
      (mul_le_mul_of_nonneg_right hK (Real.rpow_nonneg (Nat.cast_nonneg p) _))
  have hc : (∏ p ∈ d.primeFactors, (K : ℝ)) ≤ B*(d : ℝ)^ε := by
    have h := hcoeff d hdpos
    have he : ((∏ p ∈ d.primeFactors, K*d.factorization p : ℕ) : ℝ) =
        ∏ p ∈ d.primeFactors, (K : ℝ) := by
      rw [Nat.cast_prod]
      apply Finset.prod_congr rfl
      intro p hp
      rw [Nat.factorization_eq_one_of_squarefree hd (Nat.prime_of_mem_primeFactors hp)
        (Nat.dvd_of_mem_primeFactors hp), Nat.mul_one]
    rwa [he] at h
  have hpowers : (∏ p ∈ d.primeFactors, (p : ℝ)^(10 : ℝ)) =
      (d : ℝ)^(10 : ℝ) := by
    rw [Real.finset_prod_rpow _ _ (fun p _ => Nat.cast_nonneg p)]
    congr 1
    rw [← Nat.cast_prod, Nat.prod_primeFactors_of_squarefree hd]
  rw [← totalMass_eq, totalMass_squarefree F d hd]
  calc
    _ ≤ ∏ p ∈ d.primeFactors, (K : ℝ)*(p : ℝ)^(10 : ℝ) := by
      apply Finset.prod_le_prod
      · intro p hp
        letI : NeZero p := ⟨(Nat.prime_of_mem_primeFactors hp).ne_zero⟩
        rw [totalMass_eq]
        exact gcdRootMass_nonneg F p
      · exact hlocal
    _ = (∏ p ∈ d.primeFactors, (K : ℝ)) * (d : ℝ)^(10 : ℝ) := by
      rw [Finset.prod_mul_distrib, hpowers]
    _ ≤ (B*(d : ℝ)^ε) * (d : ℝ)^(10 : ℝ) :=
      mul_le_mul_of_nonneg_right hc (Real.rpow_nonneg hdR.le _)
    _ = _ := by rw [mul_assoc, ← Real.rpow_add hdR]; congr 2; ring

/-- The sharp root-filtered half-Hessian mass, with both gcds discarded. -/
theorem exists_uniform_root_mass_bound (F : MvPolynomial (Fin 10) ℤ)
    (hF : F.IsHomogeneous 3) (hA : Anisotropic (map (Int.castRingHom ℚ) F))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (d : ℕ) [NeZero d], Squarefree d →
      WeightedHessianRootCRT.rootMass F d ≤ C*(d : ℝ)^(10+ε) := by
  obtain ⟨C,hC,hbound⟩ := exists_uniform_squarefree_bound F hF hA ε hε
  exact ⟨C,hC,fun d _ hd => (SquarefreeHessianMass.rootMass_le_gcdRootMass F d).trans (hbound d hd)⟩

end CubicTenVariables.GcdWeightedHessianSharp
