import CubicTenVariables.PrimeConstantEpsilonBound
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Data.Fintype.BigOperators

/-! Multiplicity of splitting each merged squarefree depth factor into
its ordinary and square-prime parts. The literal factorization choices
are finite, with exactly two choices for each prime of the total product.
No numerical-depth periodicity or arithmetic estimate is assumed. -/

set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.ComplementMergedMultiplicity
open scoped BigOperators

/-- All actual factorization choices at every finite depth index. -/
def choices {ι : Type*} [Fintype ι] (q : ι → ℕ) : Finset (ι → ℕ × ℕ) := by
  classical
  exact Fintype.piFinset (fun j => (q j).divisorsAntidiagonal)

theorem mem_choices_iff {ι : Type*} [Fintype ι] (q : ι → ℕ)
    (hq : ∀ j, q j ≠ 0) (x : ι → ℕ × ℕ) :
    x ∈ choices q ↔ ∀ j, (x j).1*(x j).2=q j := by
  classical
  simp only [choices,Fintype.mem_piFinset,Nat.mem_divisorsAntidiagonal]
  exact ⟨fun hx j => (hx j).1,fun hx j => ⟨hx j,hq j⟩⟩

private theorem divisor_card (q : ℕ) (hq : Squarefree q) :
    q.divisors.card = 2^q.primeFactors.card := by
  rw [Nat.card_divisors hq.ne_zero]
  calc
    _ = ∏ p ∈ q.primeFactors, (2 : ℕ) := by
      apply Finset.prod_congr rfl
      intro p hp
      rw [Nat.factorization_eq_one_of_squarefree hq (Nat.prime_of_mem_primeFactors hp)
        (Nat.dvd_of_mem_primeFactors hp)]
    _ = _ := Finset.prod_const _

private theorem primeFactors_prod_card {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (q : ι → ℕ) (hq : ∀ j, q j ≠ 0)
    (hcop : Pairwise (fun i j => (q i).Coprime (q j))) :
    (∏ j ∈ s, q j).primeFactors.card = ∑ j ∈ s, (q j).primeFactors.card := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    have hs : (∏ j ∈ s, q j) ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun j _ => hq j)
    have hc : (q i).Coprime (∏ j ∈ s, q j) := Nat.coprime_prod_right_iff.mpr
      (fun j hj => hcop (by intro he; subst j; exact hi hj))
    rw [Finset.prod_insert hi,Finset.sum_insert hi,Nat.primeFactors_mul (hq i) hs,
      Finset.card_union_of_disjoint hc.disjoint_primeFactors,ih]

/-- Exact count, including the empty index type and merged factors equal
to one. Squarefreeness and pairwise coprimality are the only hypotheses. -/
theorem card_choices {ι : Type*} [Fintype ι] (q : ι → ℕ)
    (hq : ∀ j, Squarefree (q j))
    (hcop : Pairwise (fun i j => (q i).Coprime (q j))) :
    (choices q).card = 2^(∏ j, q j).primeFactors.card := by
  classical
  rw [choices,Fintype.card_piFinset]
  calc
    _ = ∏ j, (q j).divisors.card := by
      apply Finset.prod_congr rfl
      intro j _
      rw [← Nat.map_div_right_divisors,Finset.card_map]
    _ = ∏ j, 2^(q j).primeFactors.card := by
      apply Finset.prod_congr rfl
      intro j _
      exact divisor_card (q j) (hq j)
    _ = 2^(∑ j, (q j).primeFactors.card) := (Finset.prod_pow_eq_pow_sum ..)
    _ = _ := by rw [primeFactors_prod_card Finset.univ q (fun j => (hq j).ne_zero) hcop]

/-- Any finite set of actual split functions has the same multiplicity
upper bound, without an extra injectivity or uniqueness premise. -/
theorem card_families_le {ι : Type*} [Fintype ι] (q : ι → ℕ)
    (hq : ∀ j, Squarefree (q j))
    (hcop : Pairwise (fun i j => (q i).Coprime (q j)))
    (E : Finset (ι → ℕ × ℕ)) (hE : ∀ x ∈ E, ∀ j, (x j).1*(x j).2=q j) :
    E.card ≤ 2^(∏ j, q j).primeFactors.card := by
  classical
  rw [← card_choices q hq hcop]
  exact Finset.card_le_card (fun x hx => (mem_choices_iff q (fun j => (hq j).ne_zero) x).mpr (hE x hx))

/-- The two-array representation used for exact depth allocations. -/
theorem card_pair_families_le {ι : Type*} [Fintype ι] (q : ι → ℕ)
    (hq : ∀ j, Squarefree (q j))
    (hcop : Pairwise (fun i j => (q i).Coprime (q j)))
    (E : Finset ((ι → ℕ) × (ι → ℕ)))
    (hE : ∀ x ∈ E, ∀ j, x.1 j*x.2 j=q j) :
    E.card ≤ 2^(∏ j, q j).primeFactors.card := by
  classical
  let zip : ((ι → ℕ) × (ι → ℕ)) → (ι → ℕ × ℕ) := fun x j => (x.1 j,x.2 j)
  have hinj : Function.Injective zip := by
    intro x y hxy
    apply Prod.ext
    · funext j
      exact congrArg Prod.fst (congrFun hxy j)
    · funext j
      exact congrArg Prod.snd (congrFun hxy j)
  have he : (E.image zip).card = E.card := Finset.card_image_of_injective E hinj
  rw [← he]
  apply card_families_le q hq hcop
  intro x hx
  obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hx
  exact hE y hy

/-- One epsilon-absorption constant is chosen before all modulus scales,
merged factors and split families on the fixed finite index type. -/
theorem exists_uniform_bound {ι : Type*} [Fintype ι] (ε : ℝ) (hε : 0 < ε) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ D : ℝ, 1 ≤ D → ∀ q : ι → ℕ,
      (∀ j, Squarefree (q j)) →
      Pairwise (fun i j => (q i).Coprime (q j)) →
      ((∏ j, q j : ℕ) : ℝ) ≤ 2*D →
      ∀ E : Finset ((ι → ℕ) × (ι → ℕ)),
        (∀ x ∈ E, ∀ j, x.1 j*x.2 j=q j) → (E.card : ℝ) ≤ K*D^ε := by
  obtain ⟨A,hA,hbound⟩ := PrimeConstantEpsilonBound.exists_bound 2 (by norm_num) ε hε
  refine ⟨max 1 (A*(2 : ℝ)^ε),le_max_left _ _,?_⟩
  intro D hD q hq hcop hsize E hE
  have hprod : 1 ≤ ∏ j, q j := Nat.one_le_iff_ne_zero.mpr
    (Finset.prod_ne_zero_iff.mpr fun j _ => (hq j).ne_zero)
  have hcard : (E.card : ℝ) ≤ (2 : ℝ)^(∏ j, q j).primeFactors.card := by
    exact_mod_cast card_pair_families_le q hq hcop E hE
  calc
    _ ≤ (2 : ℝ)^(∏ j, q j).primeFactors.card := hcard
    _ ≤ A*((∏ j, q j : ℕ) : ℝ)^ε := hbound _ hprod
    _ ≤ A*(2*D)^ε := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (Nat.cast_nonneg _) hsize hε.le) (by linarith)
    _ = (A*(2 : ℝ)^ε)*D^ε := by
      rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (by linarith : 0 ≤ D)]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)

end CubicTenVariables.ComplementMergedMultiplicity
