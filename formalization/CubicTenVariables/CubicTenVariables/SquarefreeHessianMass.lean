import CubicTenVariables.CubicFiniteFieldMass
import CubicTenVariables.GcdWeightedHessianCRT

/-! Squarefree bounds for the two literal finite Hessian masses in the
onion estimate. All primes are included, and no literature premise occurs. -/

noncomputable section
namespace CubicTenVariables.SquarefreeHessianMass
open MvPolynomial HessianTheorem11 HessianKernelCRT WeightedHessianRootCRT
open SquarefreeResidueFactors PrimeFrogZeroMass
open scoped BigOperators
attribute [local instance] Classical.propDecidable

variable {v m n : ℕ}

/-- The unrestricted mass counts all Hessian incidence pairs, with no
polynomial-zero restriction on the base point. -/
def kernelMass (F : MvPolynomial (Fin v) ℤ) (d : ℕ) [NeZero d] : ℕ :=
  ∑ x : Fin v → ZMod d, hessianKernelCard F d x

theorem kernelMass_mul (F : MvPolynomial (Fin v) ℤ) [NeZero m] [NeZero n]
    (hc : m.Coprime n) : kernelMass F (m*n) = kernelMass F m * kernelMass F n := by
  unfold kernelMass
  simp only [hessianKernelCard_mul F hc]
  exact WeightedCRTAdapters.sum_crt_product hc (hessianKernelCard F m)
    (hessianKernelCard F n)

@[simp] theorem kernelMass_one (F : MvPolynomial (Fin v) ℤ) : kernelMass F 1 = 1 := by
  have hk (x : Fin v → ZMod 1) : hessianKernelCard F 1 x = 1 := by
    unfold hessianKernelCard
    have hz (z : Fin v → ZMod 1) :
        (hessian (map (Int.castRingHom (ZMod 1)) F) x).mulVec z = 0 :=
      Subsingleton.elim _ _
    simp only [hz, Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.filter_true,
      Finset.card_univ, Fintype.card_fun, Fintype.card_fin, ZMod.card, one_pow]
  simp [kernelMass, hk]

private def totalMass (F : MvPolynomial (Fin v) ℤ) (d : ℕ) : ℕ :=
  if hd : d = 0 then 0 else @kernelMass v F d ⟨hd⟩

private theorem totalMass_eq (F : MvPolynomial (Fin v) ℤ) (d : ℕ) [NeZero d] :
    totalMass F d = kernelMass F d := by simp only [totalMass, dif_neg (NeZero.ne d)]

private theorem totalMass_mul (F : MvPolynomial (Fin v) ℤ)
    (m n : ℕ) (hc : m.Coprime n) : totalMass F (m*n) = totalMass F m * totalMass F n := by
  by_cases hm : m = 0
  · subst m; simp [totalMass]
  by_cases hn : n = 0
  · subst n; simp [totalMass]
  letI : NeZero m := ⟨hm⟩
  letI : NeZero n := ⟨hn⟩
  simpa only [totalMass_eq] using kernelMass_mul F hc

private theorem totalMass_squarefree (F : MvPolynomial (Fin v) ℤ)
    (d : ℕ) (hd : Squarefree d) : totalMass F d = ∏ p ∈ d.primeFactors, totalMass F p := by
  have h := Nat.multiplicative_factorization (totalMass F) (totalMass_mul F)
    (by rw [totalMass_eq, kernelMass_one]) hd.ne_zero
  rw [Nat.prod_factorization_eq_prod_primeFactors] at h
  rw [h]
  apply Finset.prod_congr rfl
  intro p hp
  rw [Nat.factorization_eq_one_of_squarefree hd (Nat.prime_of_mem_primeFactors hp)
    (Nat.dvd_of_mem_primeFactors hp), pow_one]

/-- A single constant covers every squarefree modulus, including one and
primes of bad reduction, for the full unrestricted Hessian kernel mass. -/
theorem exists_uniform_kernel_mass_bound (F : MvPolynomial (Fin 10) ℤ)
    (hF : F.IsHomogeneous 3) (hA : Anisotropic (map (Int.castRingHom ℚ) F))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (d : ℕ) [NeZero d], Squarefree d →
      ((∑ x : Fin 10 → ZMod d, hessianKernelCard F d x : ℕ) : ℝ) ≤
        C*(d : ℝ)^(12+ε) := by
  obtain ⟨K,hK,hprime⟩ := CubicFiniteFieldMass.exists_uniform_hessian_kernel_mass_bound F hF hA
  obtain ⟨B,hB,hcoeff⟩ := PrimeFactorEpsilonBound.exists_uniform_prime_factor_bound K hK ε hε
  refine ⟨B,hB,?_⟩
  intro d _ hd
  have hdR : 0 < (d : ℝ) := by exact_mod_cast NeZero.pos d
  have hlocal (p : ℕ) (hp : p ∈ d.primeFactors) :
      (totalMass F p : ℝ) ≤ (K : ℝ)*(p : ℝ)^(12 : ℝ) := by
    letI : Fact p.Prime := ⟨Nat.prime_of_mem_primeFactors hp⟩
    rw [totalMass_eq]
    have hh := hprime p
    norm_cast
  have hc : (∏ p ∈ d.primeFactors, (K : ℝ)) ≤ B*(d : ℝ)^ε := by
    have h := hcoeff d (NeZero.pos d)
    have he : ((∏ p ∈ d.primeFactors, K*d.factorization p : ℕ) : ℝ) =
        ∏ p ∈ d.primeFactors, (K : ℝ) := by
      rw [Nat.cast_prod]
      apply Finset.prod_congr rfl
      intro p hp
      rw [Nat.factorization_eq_one_of_squarefree hd (Nat.prime_of_mem_primeFactors hp)
        (Nat.dvd_of_mem_primeFactors hp), Nat.mul_one]
    rwa [he] at h
  have hpowers : (∏ p ∈ d.primeFactors, (p : ℝ)^(12 : ℝ)) =
      (d : ℝ)^(12 : ℝ) := by
    rw [Real.finset_prod_rpow _ _ (fun p _ => Nat.cast_nonneg p)]
    congr 1
    rw [← Nat.cast_prod, Nat.prod_primeFactors_of_squarefree hd]
  change (kernelMass F d : ℝ) ≤ _
  rw [← totalMass_eq, totalMass_squarefree F d hd, Nat.cast_prod]
  calc
    _ ≤ ∏ p ∈ d.primeFactors, (K : ℝ)*(p : ℝ)^(12 : ℝ) := by
      apply Finset.prod_le_prod
      · intros; exact Nat.cast_nonneg _
      · exact hlocal
    _ = (∏ p ∈ d.primeFactors, (K : ℝ)) * (d : ℝ)^(12 : ℝ) := by
      rw [Finset.prod_mul_distrib, hpowers]
    _ ≤ (B*(d : ℝ)^ε) * (d : ℝ)^(12 : ℝ) :=
      mul_le_mul_of_nonneg_right hc (Real.rpow_nonneg hdR.le _)
    _ = _ := by rw [mul_assoc, ← Real.rpow_add hdR]; congr 2; ring

/-- Each literal vector gcd is positive at a positive modulus. -/
theorem one_le_rootWeight (F : MvPolynomial (Fin v) ℤ) (d : ℕ) [NeZero d]
    (x : Fin v → ZMod d) : 1 ≤ rootWeight F d x :=
  Nat.mul_pos (vectorGcd_pos d (NeZero.pos d) _) (vectorGcd_pos d (NeZero.pos d) _)

/-- Dropping both gcd factors only decreases the actual nonnegative
square-root Hessian root mass. -/
theorem rootMass_le_gcdRootMass (F : MvPolynomial (Fin v) ℤ) (d : ℕ) [NeZero d] :
    WeightedHessianRootCRT.rootMass F d ≤ SquarefullWeightedSums.gcdRootMass F d := by
  unfold WeightedHessianRootCRT.rootMass SquarefullWeightedSums.gcdRootMass
  apply Finset.sum_le_sum
  intro x _
  split_ifs
  · exact le_mul_of_one_le_right (kernelWeight_nonneg F d x)
      (by exact_mod_cast one_le_rootWeight F d x)
  · exact le_rfl

/-- The companion squarefree bound retains exactly the polynomial-zero
condition and the square-root kernel weight, with no literature input. -/
theorem exists_uniform_root_mass_bound (F : MvPolynomial (Fin 10) ℤ)
    (hF : F.IsHomogeneous 3) (hA : Anisotropic (map (Int.castRingHom ℚ) F))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (d : ℕ) [NeZero d], Squarefree d →
      WeightedHessianRootCRT.rootMass F d ≤ C*(d : ℝ)^((21 : ℝ)/2+ε) := by
  obtain ⟨C,hC,hbound⟩ := GcdWeightedHessianCRT.exists_uniform_squarefree_bound F hF hA ε hε
  exact ⟨C,hC,fun d _ hd => (rootMass_le_gcdRootMass F d).trans (hbound d hd)⟩

end CubicTenVariables.SquarefreeHessianMass
