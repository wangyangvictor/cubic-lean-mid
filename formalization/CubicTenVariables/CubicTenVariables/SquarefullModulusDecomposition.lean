import CubicTenVariables.CubeFullSmithParameters
import Mathlib.Data.Nat.Squarefree

/-! Canonical square-part and squarefree-part decomposition of an actual
modulus. Positivity of the original modulus is stated separately, and
squarefullness supplies the additional divisibility needed for Onion. -/

noncomputable section
namespace CubicTenVariables.SquarefullModulusDecomposition
open scoped BigOperators

/-- Every prime occurring in r has exponent at least two. -/
def SquareFull (r : ℕ) : Prop := ∀ p ∈ r.primeFactors, 2 ≤ r.factorization p

/-- The canonical square-root of the square part. -/
def c (r : ℕ) : ℕ := ∏ p ∈ r.primeFactors, p^(r.factorization p / 2)

/-- The canonical squarefree part: exactly primes of odd exponent. -/
def d (r : ℕ) : ℕ :=
  ∏ p ∈ r.primeFactors.filter (fun p => r.factorization p % 2 = 1), p

theorem c_pos (r : ℕ) : 0 < c r :=
  Finset.prod_pos (fun _p hp => pow_pos (Nat.prime_of_mem_primeFactors hp).pos _)

theorem d_pos (r : ℕ) : 0 < d r :=
  Finset.prod_pos (fun _p hp => (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1).pos)

@[simp] theorem c_one : c 1 = 1 := by simp [c]
@[simp] theorem d_one : d 1 = 1 := by simp [d]
@[simp] theorem squareFull_one : SquareFull 1 := by simp [SquareFull]

theorem factorization_c (r p : ℕ) : (c r).factorization p = r.factorization p / 2 := by
  rw [c, CubeFullSmithParameters.factorization_prime_power_prod _
    (fun q hq => Nat.prime_of_mem_primeFactors hq)]
  by_cases hp : p ∈ r.primeFactors
  · simp [hp]
  · have hz : r.factorization p = 0 := Finsupp.notMem_support_iff.mp hp
    simp [hp,hz]

theorem factorization_d (r p : ℕ) : (d r).factorization p = r.factorization p % 2 := by
  have h := CubeFullSmithParameters.factorization_prime_power_prod
    (r.primeFactors.filter (fun q => r.factorization q % 2 = 1))
    (fun q hq => Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hq).1)
    (fun _ => 1) p
  simp only [pow_one, Finset.mem_filter] at h
  change (d r).factorization p = _ at h
  rw [h]
  by_cases hp : p ∈ r.primeFactors
  · simp only [hp,true_and]
    have hm := Nat.mod_lt (r.factorization p) (by norm_num : 0 < 2)
    split_ifs <;> omega
  · have hz : r.factorization p = 0 := Finsupp.notMem_support_iff.mp hp
    simp [hp,hz]

/-- The canonical odd-prime product is squarefree for every input. -/
theorem d_squarefree (r : ℕ) : Squarefree (d r) := by
  apply (Nat.squarefree_iff_factorization_le_one (d_pos r).ne').mpr
  intro p
  rw [factorization_d]
  have h := Nat.mod_lt (r.factorization p) (by norm_num : 0 < 2)
  omega

/-- Reconstruction holds for every positive integer, without squarefullness. -/
theorem eq_c_sq_mul_d (r : ℕ) (hr : 0 < r) : r = (c r)^2*d r := by
  apply Nat.eq_of_factorization_eq hr.ne' (by positivity [c_pos r,d_pos r])
  intro p
  rw [Nat.factorization_mul (pow_ne_zero _ (c_pos r).ne') (d_pos r).ne',
    Finsupp.add_apply, Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul,
    factorization_c, factorization_d]
  omega

/-- Squarefullness means that every odd occurring exponent is at least three,
so its prime also occurs in the canonical square part. -/
theorem d_dvd_c (r : ℕ) (hr : SquareFull r) : d r ∣ c r := by
  apply (Nat.factorization_le_iff_dvd (d_pos r).ne' (c_pos r).ne').mp
  intro p
  rw [factorization_d, factorization_c]
  by_cases hp : p ∈ r.primeFactors
  · have h := hr p hp
    have hm := Nat.mod_lt (r.factorization p) (by norm_num : 0 < 2)
    omega
  · have hz : r.factorization p = 0 := Finsupp.notMem_support_iff.mp hp
    simp [hz]

theorem squareFull_of_cubeFull (r : ℕ) (hr : CubeFullSmithParameters.CubeFull r) :
    SquareFull r := fun p hp => (by norm_num : 2 ≤ 3).trans (hr p hp)

/-- Actual positive moduli with the same canonical pair are equal. -/
theorem eq_of_parameters_eq (r s : ℕ) (hr : 0 < r) (hs : 0 < s)
    (h : (c r,d r) = (c s,d s)) : r = s := by
  obtain ⟨hc,hd⟩ := Prod.mk.inj h
  calc
    r = (c r)^2*d r := eq_c_sq_mul_d r hr
    _ = (c s)^2*d s := by rw [hc,hd]
    _ = s := (eq_c_sq_mul_d s hs).symm

theorem parameters_injOn : Set.InjOn (fun r => (c r,d r)) {r : ℕ | 0 < r} := by
  intro r hr s hs h
  exact eq_of_parameters_eq r s hr hs h

theorem parameters_injective :
    Function.Injective (fun r : {r : ℕ // 0 < r} => (c r.val,d r.val)) := by
  intro r s h
  exact Subtype.ext (eq_of_parameters_eq r.val s.val r.property s.property h)

end CubicTenVariables.SquarefullModulusDecomposition
