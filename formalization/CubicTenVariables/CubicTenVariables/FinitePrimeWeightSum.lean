import CubicTenVariables.PositiveReciprocalSum
import Mathlib.Data.Nat.Factorization.Basic

/-! A finite Euler-product majorization proved directly by finite exponent
profiles. No convergence or multiplicativity statement is assumed. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace CubicTenVariables.FinitePrimeWeightSum
open scoped BigOperators

/-- Local finite-sum bounds by a summable prime majorant give a uniform
bound for arbitrary finite sets of positive integers. -/
theorem exists_uniform_bound (w : ℕ → ℕ → ℝ)
    (hw : ∀ p k, 0 ≤ w p k) (hw0 : ∀ p, w p 0 = 1)
    (ε K : ℝ) (hε : 0 < ε) (hK : 0 ≤ K)
    (hlocal : ∀ p : ℕ, p.Prime → ∀ E : Finset ℕ,
      (∑ k ∈ E, w p k) ≤ 1+K*(p : ℝ)^(-1-ε)) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ Q : Finset ℕ, (∀ r ∈ Q, 0 < r) →
      (∑ r ∈ Q, ∏ p ∈ r.primeFactors, w p (r.factorization p)) ≤ C := by
  classical
  obtain ⟨B,hB,hseries⟩ := PositiveReciprocalSum.exists_uniform_rpow_bound (-1-ε) (by linarith)
  refine ⟨Real.exp (K*B), Real.one_le_exp (by positivity), ?_⟩
  intro Q hQ
  let S : Finset ℕ := Q.biUnion Nat.primeFactors
  let f (r : ℕ) (p : S) : ℕ := r.factorization p
  have hsub (r : ℕ) (hr : r ∈ Q) : r.primeFactors ⊆ S :=
    Finset.subset_biUnion_of_mem Nat.primeFactors hr
  have hzero (r : ℕ) (hr : r ∈ Q) (p : ℕ) (hp : p ∉ S) : r.factorization p = 0 := by
    apply Finsupp.notMem_support_iff.mp
    exact fun h => hp (hsub r hr h)
  have hinj : Set.InjOn f (Q : Set ℕ) := by
    intro a ha b hb hab
    apply Nat.eq_of_factorization_eq (hQ a ha).ne' (hQ b hb).ne'
    intro p
    by_cases hp : p ∈ S
    · exact congrFun hab ⟨p,hp⟩
    · rw [hzero a ha p hp, hzero b hb p hp]
  have hprod (r : ℕ) (hr : r ∈ Q) :
      (∏ p ∈ r.primeFactors, w p (r.factorization p)) = ∏ p : S, w p (f r p) := by
    change (∏ p ∈ r.primeFactors, w p (r.factorization p)) = ∏ p : S, w (p : ℕ) (r.factorization p)
    rw [Finset.prod_coe_sort S (fun p => w p (r.factorization p))]
    apply Finset.prod_subset (hsub r hr)
    intro p hp hnot
    have hz : r.factorization p = 0 := Finsupp.notMem_support_iff.mp hnot
    simp only [hz, hw0]
  let T := Q.image f
  let A (p : S) : Finset ℕ := T.image (fun t => t p)
  have hT : T ⊆ Fintype.piFinset A := by
    intro t ht
    exact Fintype.mem_piFinset.mpr (fun p => Finset.mem_image_of_mem _ ht)
  have hprime (p : S) : (p : ℕ).Prime := by
    obtain ⟨r,hr,hp⟩ := Finset.mem_biUnion.mp p.property
    exact Nat.prime_of_mem_primeFactors hp
  calc
    _ = ∑ r ∈ Q, ∏ p : S, w p (f r p) := Finset.sum_congr rfl hprod
    _ = ∑ t ∈ T, ∏ p : S, w p (t p) := (Finset.sum_image (f := fun t : S → ℕ => ∏ p : S, w p (t p)) hinj).symm
    _ ≤ ∑ t ∈ Fintype.piFinset A, ∏ p : S, w p (t p) :=
      Finset.sum_le_sum_of_subset_of_nonneg hT (fun t _ _ => Finset.prod_nonneg (fun p _ => hw p (t p)))
    _ = ∏ p : S, ∑ k ∈ A p, w p k := (Finset.prod_univ_sum A (fun (p : S) k => w p k)).symm
    _ ≤ ∏ p : S, (1+K*(p : ℝ)^(-1-ε)) :=
      Finset.prod_le_prod (fun p _ => Finset.sum_nonneg (fun k _ => hw p k))
        (fun p _ => hlocal p (hprime p) (A p))
    _ ≤ ∏ p : S, Real.exp (K*(p : ℝ)^(-1-ε)) := by
      apply Finset.prod_le_prod
      · intro p _; positivity
      · intro p _; simpa only [add_comm] using Real.add_one_le_exp (K*(p : ℝ)^(-1-ε))
    _ = Real.exp (K*(∑ p ∈ S, (p : ℝ)^(-1-ε))) := by
      rw [← Real.exp_sum, ← Finset.mul_sum, Finset.sum_coe_sort S (fun p : ℕ => (p : ℝ)^(-1-ε))]
    _ ≤ Real.exp (K*B) := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (hseries S) hK)

end CubicTenVariables.FinitePrimeWeightSum
