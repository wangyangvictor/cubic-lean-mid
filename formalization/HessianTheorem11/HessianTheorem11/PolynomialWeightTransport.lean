import HessianTheorem11.CubicWeights
import HessianTheorem11.PolynomialRestriction

/-!+# Transport of polynomial support weights

A linear substitution cannot lower monomial weight when every nonzero matrix
entry replaces a source variable by a target variable of at least its weight.
The proof follows actual polynomial support through sums, products, powers,
and the monomial expansion.  Source and target dimensions and weights may differ.
No nonvanishing, invertibility, homogeneity, or geometric assumption is used.
-/

namespace HessianTheorem11.PolynomialWeightTransport

open MvPolynomial PolynomialRestriction
open scoped Pointwise

noncomputable section

variable {K : Type*} [CommRing K]

def HasWeightLowerBound {n : ℕ} (F : MvPolynomial (Fin n) K)
    (w : Fin n → ℤ) (bound : ℤ) : Prop :=
  ∀ d ∈ F.support, bound ≤ monomialWeight w d

theorem lowerBound_zero {n : ℕ} (w : Fin n → ℤ) (bound : ℤ) :
    HasWeightLowerBound (0 : MvPolynomial (Fin n) K) w bound := by
  intro d hd
  simp at hd

theorem lowerBound_monomial {n : ℕ} (w : Fin n → ℤ)
    (d : Fin n →₀ ℕ) (c : K) {bound : ℤ} (hbound : bound ≤ monomialWeight w d) :
    HasWeightLowerBound (monomial d c) w bound := by
  intro e he
  have heq := Finset.mem_singleton.mp (support_monomial_subset he)
  simpa [heq] using hbound

theorem lowerBound_C {n : ℕ} (w : Fin n → ℤ) (c : K) :
    HasWeightLowerBound (C c) w 0 := by
  apply lowerBound_monomial
  simp [monomialWeight]

theorem lowerBound_mul {n : ℕ} (w : Fin n → ℤ)
    {P Q : MvPolynomial (Fin n) K} {p q : ℤ}
    (hP : HasWeightLowerBound P w p) (hQ : HasWeightLowerBound Q w q) :
    HasWeightLowerBound (P * Q) w (p + q) := by
  classical
  intro d hd
  obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_add.mp (support_mul P Q hd)
  rw [monomialWeight_add]
  exact add_le_add (hP a ha) (hQ b hb)

theorem lowerBound_pow {n : ℕ} (w : Fin n → ℤ)
    {P : MvPolynomial (Fin n) K} {p : ℤ}
    (hP : HasWeightLowerBound P w p) (k : ℕ) :
    HasWeightLowerBound (P ^ k) w ((k : ℤ) * p) := by
  induction k with
  | zero => simpa using lowerBound_C w (1 : K)
  | succ k ih =>
      simpa [pow_succ, Nat.cast_add, add_mul] using lowerBound_mul w ih hP

theorem lowerBound_prod {n : ℕ} {ι : Type*} (w : Fin n → ℤ)
    (s : Finset ι) (P : ι → MvPolynomial (Fin n) K) (bound : ι → ℤ)
    (hP : ∀ i ∈ s, HasWeightLowerBound (P i) w (bound i)) :
    HasWeightLowerBound (∏ i ∈ s, P i) w (∑ i ∈ s, bound i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using lowerBound_C w (1 : K)
  | @insert i s hi ih =>
      simp only [Finset.prod_insert hi, Finset.sum_insert hi]
      exact lowerBound_mul w (hP i (Finset.mem_insert_self _ _))
        (ih (fun j hj => hP j (Finset.mem_insert_of_mem hj)))

theorem lowerBound_sum {n : ℕ} {ι : Type*} (w : Fin n → ℤ)
    (s : Finset ι) (P : ι → MvPolynomial (Fin n) K) (bound : ℤ)
    (hP : ∀ i ∈ s, HasWeightLowerBound (P i) w bound) :
    HasWeightLowerBound (∑ i ∈ s, P i) w bound := by
  classical
  intro d hd
  obtain ⟨i, hi, hdi⟩ := Finset.mem_biUnion.mp (MvPolynomial.support_sum hd)
  exact hP i hi d hdi

theorem lowerBound_linearForms {n m : ℕ}
    (B : Matrix (Fin n) (Fin m) K) (v : Fin n → ℤ) (w : Fin m → ℤ)
    (entry_weights : ∀ i j, B i j ≠ 0 → v i ≤ w j) (i : Fin n) :
    HasWeightLowerBound (linearForms B i) w (v i) := by
  classical
  apply lowerBound_sum
  intro j _
  by_cases zero : B i j = 0
  · simpa [zero] using lowerBound_zero (K := K) w (v i)
  · have hterm : C (B i j) * X j =
        monomial (Finsupp.single j 1) (B i j) := by
      simp only [C_apply, X, monomial_mul, zero_add, mul_one]
    rw [hterm]
    apply lowerBound_monomial
    simpa [monomialWeight_single] using entry_weights i j zero

theorem lowerBound_restrict_monomial {n m : ℕ}
    (B : Matrix (Fin n) (Fin m) K) (v : Fin n → ℤ) (w : Fin m → ℤ)
    (entry_weights : ∀ i j, B i j ≠ 0 → v i ≤ w j)
    (d : Fin n →₀ ℕ) (c : K) :
    HasWeightLowerBound (restrict B (monomial d c)) w (monomialWeight v d) := by
  classical
  have hp : HasWeightLowerBound
      (∏ i ∈ d.support, linearForms B i ^ d i) w
      (∑ i ∈ d.support, (d i : ℤ) * v i) :=
    lowerBound_prod w d.support (fun i => linearForms B i ^ d i)
      (fun i => (d i : ℤ) * v i)
      (fun i _ => lowerBound_pow w (lowerBound_linearForms B v w entry_weights i) (d i))
  have hsum : (∑ i ∈ d.support, (d i : ℤ) * v i) = monomialWeight v d := by
    unfold monomialWeight
    apply Finset.sum_subset (Finset.subset_univ _)
    intro i _ hi
    have hz : d i = 0 := Finsupp.notMem_support_iff.mp hi
    simp [hz]
  rw [hsum] at hp
  have hm := lowerBound_mul w (lowerBound_C w c) hp
  change HasWeightLowerBound (aeval (linearForms B) (monomial d c)) w (monomialWeight v d)
  rw [aeval_monomial]
  simpa only [Finsupp.prod, zero_add] using hm

theorem hasPositiveWeights_restrict_of_entry_weights {n m : ℕ}
    (B : Matrix (Fin n) (Fin m) K) (v : Fin n → ℤ) (w : Fin m → ℤ)
    (entry_weights : ∀ i j, B i j ≠ 0 → v i ≤ w j)
    (F : MvPolynomial (Fin n) K) (positive : HasPositiveWeights F v) :
    HasPositiveWeights (restrict B F) w := by
  classical
  intro e he
  have expansion : restrict B F =
      ∑ d ∈ F.support, restrict B (monomial d (coeff d F)) := by
    simpa only [restrict, map_sum] using congrArg (restrict B) F.as_sum
  rw [expansion] at he
  obtain ⟨d, hd, he⟩ := Finset.mem_biUnion.mp (MvPolynomial.support_sum he)
  exact lt_of_lt_of_le (positive d hd)
    (lowerBound_restrict_monomial B v w entry_weights d (coeff d F) e he)

theorem hasNonnegativeWeights_restrict_of_entry_weights {n m : ℕ}
    (B : Matrix (Fin n) (Fin m) K) (v : Fin n → ℤ) (w : Fin m → ℤ)
    (entry_weights : ∀ i j, B i j ≠ 0 → v i ≤ w j)
    (F : MvPolynomial (Fin n) K) (nonnegative : HasNonnegativeWeights F v) :
    HasNonnegativeWeights (restrict B F) w := by
  classical
  intro e he
  have expansion : restrict B F =
      ∑ d ∈ F.support, restrict B (monomial d (coeff d F)) := by
    simpa only [restrict, map_sum] using congrArg (restrict B) F.as_sum
  rw [expansion] at he
  obtain ⟨d, hd, he⟩ := Finset.mem_biUnion.mp (MvPolynomial.support_sum he)
  exact (nonnegative d hd).trans
    (lowerBound_restrict_monomial B v w entry_weights d (coeff d F) e he)

theorem restrict_linearForms {n m l : ℕ}
    (B : Matrix (Fin n) (Fin m) K) (A : Matrix (Fin m) (Fin l) K) (i : Fin n) :
    restrict A (linearForms B i) = linearForms (B * A) i := by
  classical
  simp only [restrict, linearForms, map_sum, map_mul, aeval_C, aeval_X,
    Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro j _
  simp [mul_assoc]

/-- Restriction composition follows the order of coordinate matrix products. -/
theorem restrict_restrict {n m l : ℕ}
    (B : Matrix (Fin n) (Fin m) K) (A : Matrix (Fin m) (Fin l) K)
    (F : MvPolynomial (Fin n) K) :
    restrict A (restrict B F) = restrict (B * A) F := by
  change aeval (linearForms A) (aeval (linearForms B) F) = aeval (linearForms (B * A)) F
  rw [MvPolynomial.comp_aeval_apply]
  have forms : (fun i => aeval (linearForms A) (linearForms B i)) =
      linearForms (B * A) := funext (restrict_linearForms B A)
  rw [forms]

@[simp] theorem restrict_one {n : ℕ} (F : MvPolynomial (Fin n) K) :
    restrict (1 : Matrix (Fin n) (Fin n) K) F = F := by
  classical
  have forms : linearForms (1 : Matrix (Fin n) (Fin n) K) = X := by
    ext i
    simp [linearForms, Matrix.one_apply]
  simp only [restrict, forms, aeval_X_left_apply]

theorem hasPositiveWeights_restrict_triangular {n : ℕ}
    (B : Matrix (Fin n) (Fin n) K) (w : Fin n → ℤ)
    (entry_weights : ∀ i j, B i j ≠ 0 → w i ≤ w j)
    (F : MvPolynomial (Fin n) K) (positive : HasPositiveWeights F w) :
    HasPositiveWeights (restrict B F) w :=
  hasPositiveWeights_restrict_of_entry_weights B w w entry_weights F positive

/-- If both changes of coordinates respect the weight filtration, positivity
is independent of the splitting. -/
theorem hasPositiveWeights_restrict_iff {n : ℕ}
    (B A : Matrix (Fin n) (Fin n) K) (inverse : B * A = 1) (w : Fin n → ℤ)
    (entryB : ∀ i j, B i j ≠ 0 → w i ≤ w j)
    (entryA : ∀ i j, A i j ≠ 0 → w i ≤ w j)
    (F : MvPolynomial (Fin n) K) :
    HasPositiveWeights (restrict B F) w ↔ HasPositiveWeights F w := by
  constructor
  · intro positive
    have ht := hasPositiveWeights_restrict_triangular A w entryA (restrict B F) positive
    simpa only [restrict_restrict, inverse, restrict_one] using ht
  · exact hasPositiveWeights_restrict_triangular B w entryB F

end

end HessianTheorem11.PolynomialWeightTransport
