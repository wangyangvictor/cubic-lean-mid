import HessianTheorem11.UnconditionalOrbitTargetWeights
import HessianTheorem11.UnconditionalWeightTransport

/-! Quantitative upper weight bounds for equations on coefficient space.
A substitution with nonincreasing entry weights cannot raise such a bound. -/
noncomputable section
namespace HessianTheorem11.UnconditionalOrbitWeights
open MvPolynomial PolynomialRestriction
open scoped Pointwise
variable {K σ τ : Type*} [Field K] [Fintype σ] [Fintype τ]
  [DecidableEq σ] [DecidableEq τ]

theorem exponentWeight_eq_sum (w : σ → ℤ) (e : σ →₀ ℕ) :
    exponentWeight w e = ∑ i, (e i : ℤ) * w i := by
  exact Finsupp.sum_fintype _ _ (by simp)

theorem exponentWeight_add (w : σ → ℤ) (e f : σ →₀ ℕ) :
    exponentWeight w (e+f) = exponentWeight w e + exponentWeight w f := by
  simp [exponentWeight_eq_sum,add_mul,Finset.sum_add_distrib]

def UpperBound (P : MvPolynomial σ K) (w : σ → ℤ) (b : ℤ) : Prop :=
  ∀ e ∈ P.support, exponentWeight w e ≤ b

theorem upper_zero (w : σ → ℤ) (b : ℤ) : UpperBound (0 : MvPolynomial σ K) w b := by
  intro e he
  simp at he

theorem upper_monomial (w : σ → ℤ) (e : σ →₀ ℕ) (c : K) (b : ℤ)
    (hb : exponentWeight w e ≤ b) : UpperBound (monomial e c) w b := by
  intro f hf
  have h := Finset.mem_singleton.mp (support_monomial_subset hf)
  simpa [h] using hb

theorem upper_C (w : σ → ℤ) (c : K) : UpperBound (C c) w 0 := by
  apply upper_monomial
  simp [exponentWeight_eq_sum]

theorem upper_mul (w : σ → ℤ) {P Q : MvPolynomial σ K} {a b : ℤ}
    (hP : UpperBound P w a) (hQ : UpperBound Q w b) : UpperBound (P*Q) w (a+b) := by
  intro e he
  obtain ⟨f,hf,g,hg,rfl⟩ := Finset.mem_add.mp (support_mul P Q he)
  rw [exponentWeight_add]
  exact add_le_add (hP f hf) (hQ g hg)

theorem upper_pow (w : σ → ℤ) {P : MvPolynomial σ K} {a : ℤ}
    (hP : UpperBound P w a) (k : ℕ) : UpperBound (P^k) w ((k:ℤ)*a) := by
  induction k with
  | zero => simpa using upper_C w (1 : K)
  | succ k ih => simpa [pow_succ,Nat.cast_add,add_mul] using upper_mul w ih hP

theorem upper_prod {ι : Type*} (w : σ → ℤ) (s : Finset ι)
    (P : ι → MvPolynomial σ K) (a : ι → ℤ)
    (hP : ∀ i ∈ s, UpperBound (P i) w (a i)) :
    UpperBound (∏ i ∈ s, P i) w (∑ i ∈ s, a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using upper_C w (1 : K)
  | @insert i s hi ih =>
    simp only [Finset.prod_insert hi,Finset.sum_insert hi]
    exact upper_mul w (hP i (Finset.mem_insert_self _ _))
      (ih fun j hj => hP j (Finset.mem_insert_of_mem hj))

theorem upper_sum {ι : Type*} (w : σ → ℤ) (s : Finset ι)
    (P : ι → MvPolynomial σ K) (a : ℤ) (hP : ∀ i ∈ s, UpperBound (P i) w a) :
    UpperBound (∑ i ∈ s, P i) w a := by
  classical
  intro e he
  obtain ⟨i,hi,he⟩ := Finset.mem_biUnion.mp (MvPolynomial.support_sum he)
  exact hP i hi e he

theorem upper_linearForms (B : Matrix σ τ K) (v : σ → ℤ) (w : τ → ℤ)
    (hB : ∀ i j, B i j ≠ 0 → w j ≤ v i) (i : σ) : UpperBound (linearForms B i) w (v i) := by
  apply upper_sum
  intro j _
  by_cases hz : B i j = 0
  · simpa [hz] using upper_zero (K := K) w (v i)
  · have ht : C (B i j) * X j = monomial (Finsupp.single j 1) (B i j) := by
      simp only [C_apply,X,monomial_mul,zero_add,mul_one]
    rw [ht]
    apply upper_monomial
    simpa [exponentWeight_eq_sum,Finsupp.single_apply] using hB i j hz

theorem upper_restrict_monomial (B : Matrix σ τ K) (v : σ → ℤ) (w : τ → ℤ)
    (hB : ∀ i j, B i j ≠ 0 → w j ≤ v i) (e : σ →₀ ℕ) (c : K) :
    UpperBound (restrict B (monomial e c)) w (exponentWeight v e) := by
  have hp := upper_prod w e.support (fun i => linearForms B i ^ e i)
    (fun i => (e i : ℤ) * v i) (fun i _ => upper_pow w (upper_linearForms B v w hB i) (e i))
  have hm := upper_mul w (upper_C w c) hp
  change UpperBound (aeval (linearForms B) (monomial e c)) w _
  rw [aeval_monomial]
  simpa only [Finsupp.prod,zero_add,exponentWeight,Finsupp.sum] using hm

theorem upper_restrict (B : Matrix σ τ K) (v : σ → ℤ) (w : τ → ℤ)
    (hB : ∀ i j, B i j ≠ 0 → w j ≤ v i) (P : MvPolynomial σ K) (a : ℤ)
    (hP : UpperBound P v a) : UpperBound (restrict B P) w a := by
  classical
  intro e he
  have hx : restrict B P = ∑ f ∈ P.support, restrict B (monomial f (coeff f P)) := by
    simpa only [restrict,map_sum] using congrArg (restrict B) P.as_sum
  rw [hx] at he
  obtain ⟨f,hf,he⟩ := Finset.mem_biUnion.mp (MvPolynomial.support_sum he)
  exact (upper_restrict_monomial B v w hB f (coeff f P) e he).trans (hP f hf)

theorem weightPart_upper (P : MvPolynomial σ K) (w : σ → ℤ) (a : ℤ) :
    UpperBound (weightPart P w a) w a := by
  intro e he
  have hc := mem_support_iff.mp he
  rw [coeff_weightPart] at hc
  split_ifs at hc with h
  · exact h.le
  · exact (hc rfl).elim

end HessianTheorem11.UnconditionalOrbitWeights

namespace HessianTheorem11.UnconditionalOrbitIdeal
open MvPolynomial PolynomialRestriction UnconditionalOrbitWeights
variable {K : Type*} [Field K] {n d : ℕ}

theorem coefficientMatrix_entry_weight (B : Matrix (Fin n) (Fin n) K)
    (v w : Fin n → ℤ) (hB : ∀ i j, B i j ≠ 0 → v i ≤ w j)
    (e m : DegreeIndex n d) (h : finiteCoefficientMatrix B e m ≠ 0) :
    coefficientWeights v m ≤ coefficientWeights w e := by
  exact PolynomialWeightTransport.lowerBound_restrict_monomial B v w hB m.val 1 e.val
    (mem_support_iff.mpr h)

theorem coefficientPullback_upper (B : Matrix (Fin n) (Fin n) K)
    (v w : Fin n → ℤ) (hB : ∀ i j, B i j ≠ 0 → v i ≤ w j)
    (P : MvPolynomial (DegreeIndex n d) K) (a : ℤ)
    (hP : UpperBound P (coefficientWeights w) a) :
    UpperBound (restrict (finiteCoefficientMatrix B) P) (coefficientWeights v) a :=
  upper_restrict (finiteCoefficientMatrix B) _ _ (coefficientMatrix_entry_weight B v w hB) P a hP

end HessianTheorem11.UnconditionalOrbitIdeal
