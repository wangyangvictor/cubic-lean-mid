import CubicTenVariables.SquarefullModulusDecomposition
import CubicTenVariables.SquarefreeResidueFactors
import Mathlib.Tactic

/-! A positive five-parameter decomposition of cube-full moduli. Prime
exponents are partitioned by their residue modulo four, with exponent three
separate. This preserves the manuscript's exact d2 factor. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace CubicTenVariables.CubefullRefinedParameters
open scoped BigOperators
open SquarefullModulusDecomposition

def powers : Fin 5 → ℕ := ![4,3,5,6,7]

def localExp (k : ℕ) : Fin 5 → ℕ :=
  ![if k = 3 then 0 else k / 4 - (if k % 4 = 0 then 0 else 1),
    if k = 3 then 1 else 0,
    if k ≠ 3 ∧ k % 4 = 1 then 1 else 0,
    if k % 4 = 2 then 1 else 0,
    if k ≠ 3 ∧ k % 4 = 3 then 1 else 0]

@[simp] theorem localExp_zero (i : Fin 5) : localExp 0 i = 0 := by
  fin_cases i <;> norm_num [localExp]

theorem local_reconstruction (k : ℕ) (hk : 3 ≤ k) :
    ∑ i : Fin 5, powers i * localExp k i = k := by
  simp [powers, localExp, Fin.sum_univ_succ]
  split_ifs <;> omega

theorem local_weight (k : ℕ) (hk : k = 0 ∨ 3 ≤ k) :
    min (k % 2) (k / 2 - k % 2) = localExp k 2 + localExp k 4 := by
  simp [localExp]
  split_ifs <;> omega

/-- The source weight: primes of odd exponent at least five. -/
def weight (r : ℕ) : ℕ := SquarefreeResidueFactors.d2 (c r) (d r)

/-- Five actual positive integer parameters of the original modulus. -/
def parameters (r : ℕ) (i : Fin 5) : ℕ :=
  ∏ p ∈ r.primeFactors, p ^ localExp (r.factorization p) i

def modulus (t : Fin 5 → ℕ) : ℕ := ∏ i, t i ^ powers i

theorem parameters_pos (r : ℕ) (i : Fin 5) : 0 < parameters r i :=
  Finset.prod_pos (fun _p hp => pow_pos (Nat.prime_of_mem_primeFactors hp).pos _)

theorem modulus_pos (t : Fin 5 → ℕ) (ht : ∀ i, 0 < t i) : 0 < modulus t :=
  Finset.prod_pos (fun i _ => pow_pos (ht i) _)

theorem factorization_parameters (r p : ℕ) (i : Fin 5) :
    (parameters r i).factorization p = localExp (r.factorization p) i := by
  rw [parameters, CubeFullSmithParameters.factorization_prime_power_prod _
    (fun q hq => Nat.prime_of_mem_primeFactors hq)]
  by_cases hp : p ∈ r.primeFactors
  · simp [hp]
  · have hz : r.factorization p = 0 := Finsupp.notMem_support_iff.mp hp
    simp [hp, hz]

/-- Reconstruction makes the canonical parameter map injective. -/
theorem reconstruction (r : ℕ) (hr : 0 < r) (hcube : CubeFullSmithParameters.CubeFull r) :
    modulus (parameters r) = r := by
  apply Nat.eq_of_factorization_eq (modulus_pos _ (parameters_pos r)).ne' hr.ne'
  intro p
  rw [modulus, Nat.factorization_prod_apply (fun i _ => pow_ne_zero _ (parameters_pos r i).ne')]
  simp only [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul, factorization_parameters]
  by_cases hp : p ∈ r.primeFactors
  · exact local_reconstruction _ (hcube p hp)
  · have hz : r.factorization p = 0 := Finsupp.notMem_support_iff.mp hp
    simp [hz]

theorem parameters_injOn : Set.InjOn parameters
    {r | 0 < r ∧ CubeFullSmithParameters.CubeFull r} := by
  intro r hr s hs he
  calc
    r = modulus (parameters r) := (reconstruction r hr.1 hr.2).symm
    _ = modulus (parameters s) := congrArg modulus he
    _ = s := reconstruction s hs.1 hs.2

/-- Exact identification of the d2 in the existing squarefull formalization. -/
theorem weight_eq (r : ℕ) (hcube : CubeFullSmithParameters.CubeFull r) :
    weight r = parameters r 2 * parameters r 4 := by
  have hdv := d_dvd_c r (squareFull_of_cubeFull r hcube)
  have hd2 := SquarefreeResidueFactors.d2_pos (c r) (d r) (c_pos r) (d_squarefree r) hdv
  apply Nat.eq_of_factorization_eq hd2.ne' (Nat.mul_pos (parameters_pos r 2) (parameters_pos r 4)).ne'
  intro p
  rw [SquarefreeResidueFactors.d2_eq_gcd (c r) (d r) (c_pos r) (d_squarefree r) hdv,
    Nat.factorization_gcd (d_pos r).ne'
      (SquarefreeResidueFactors.quotient_pos (c r) (d r) (c_pos r) (d_squarefree r) hdv).ne',
    Nat.factorization_div hdv, Finsupp.inf_apply, Finsupp.tsub_apply,
    factorization_c, factorization_d,
    Nat.factorization_mul (parameters_pos r 2).ne' (parameters_pos r 4).ne',
    Finsupp.add_apply, factorization_parameters, factorization_parameters]
  apply local_weight
  by_cases hp : p ∈ r.primeFactors
  · exact Or.inr (hcube p hp)
  · exact Or.inl (Finsupp.notMem_support_iff.mp hp)

/-- The intrinsic prime-product interpretation of the existing source d2. -/
theorem weight_eq_prime_product (r : ℕ) (hcube : CubeFullSmithParameters.CubeFull r) :
    weight r = ∏ p ∈ r.primeFactors.filter
      (fun p => r.factorization p % 2 = 1 ∧ 5 ≤ r.factorization p), p := by
  rw [weight_eq r hcube, parameters, parameters, ← Finset.prod_mul_distrib, Finset.prod_filter]
  apply Finset.prod_congr rfl
  intro p hp
  have hk := hcube p hp
  have he : localExp (r.factorization p) 2 + localExp (r.factorization p) 4 =
      if r.factorization p % 2 = 1 ∧ 5 ≤ r.factorization p then 1 else 0 := by
    simp [localExp]
    split_ifs <;> omega
  rw [← pow_add, he]
  split_ifs <;> simp

end CubicTenVariables.CubefullRefinedParameters
