import CubicTenVariables.LatticeFrequencyTail
import CubicTenVariables.PrimeSumAdapter
import CubicTenVariables.QuadraticGaussBound

/-! All-modulus trivial complete-sum bounds and convergent nonzero-frequency
tails. The real mass function may be an integral of an absolute value. No
homogeneity, point-count estimate or oscillatory literature input is used. -/
set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.CompleteSumFrequencyTail
open MvPolynomial
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

/-- Triangle inequality for the actual integer-representative complete sum,
valid for every positive modulus, including one and composite moduli. -/
theorem trivial_bound (F : MvPolynomial (Fin n) ℤ) (q : ℕ) (hq : 1 ≤ q)
    (v : Fin n → ℤ) : ‖completeCubicSum F q v‖ ≤ (q : ℝ)^(n+1) := by
  classical
  letI : NeZero q := ⟨by omega⟩
  unfold completeCubicSum
  calc
    _ ≤ ∑ a : Fin q, ‖if Nat.Coprime a.val q then
        ∑ x : Fin n → Fin q, residueExponential q (completeSumPhase F a x v) else 0‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _a : Fin q, (q : ℝ)^n := by
      apply Finset.sum_le_sum
      intro a _
      split_ifs
      · apply (norm_sum_le _ _).trans
        simp only [PrimeSumAdapter.residueExponential_eq_stdAddChar,
          QuadraticGaussBound.norm_stdAddChar,Finset.sum_const,Finset.card_univ,
          Fintype.card_fun,Fintype.card_fin,nsmul_eq_mul,mul_one,Nat.cast_pow]
        exact le_rfl
      · simp
    _ = _ := by simp [pow_succ,mul_comm]

/-- The nonzero-frequency term, using a real nonnegative mass. -/
def term (F : MvPolynomial (Fin n) ℤ) (q : ℕ)
    (f : (Fin n → ℤ) → ℝ) (v : Fin n → ℤ) : ℝ :=
  if v=0 then 0 else ‖completeCubicSum F q v‖*f v

/-- The actual complement of a finite frequency cutoff. -/
def tail (F : MvPolynomial (Fin n) ℤ) (q : ℕ)
    (f : (Fin n → ℤ) → ℝ) (T : Finset (Fin n → ℤ)) (v : Fin n → ℤ) : ℝ :=
  if v ∈ T then 0 else term F q f v

theorem term_nonneg (F : MvPolynomial (Fin n) ℤ) (q : ℕ)
    (f : (Fin n → ℤ) → ℝ) (hf : ∀ v, 0 ≤ f v) (v : Fin n → ℤ) :
    0 ≤ term F q f v := by
  unfold term
  split_ifs
  · exact le_rfl
  · exact mul_nonneg (norm_nonneg _) (hf v)

/-- A summable tail makes the complete nonzero-frequency series summable,
and the finite-cut decomposition is an exact equality. -/
theorem summable_and_split (F : MvPolynomial (Fin n) ℤ) (q : ℕ)
    (f : (Fin n → ℤ) → ℝ) (T : Finset (Fin n → ℤ))
    (htail : Summable (tail F q f T)) :
    Summable (term F q f) ∧
      (∑' v, term F q f v) = (∑ v ∈ T, term F q f v)+(∑' v, tail F q f T v) := by
  let g : (Fin n → ℤ) → ℝ := fun v => if v ∈ T then term F q f v else 0
  have hg : Summable g := summable_of_ne_finset_zero (s := T) (by
    intro v hv
    exact if_neg hv)
  have he : term F q f = fun v => g v+tail F q f T v := by
    funext v
    by_cases hv : v ∈ T <;> simp [g,tail,hv]
  have hs : Summable (term F q f) := he ▸ hg.add htail
  refine ⟨hs,?_⟩
  calc
    (∑' v, term F q f v) = (∑' v, (g v+tail F q f T v)) := congrArg (fun h => ∑' v, h v) he
    _ = (∑' v, g v)+(∑' v, tail F q f T v) := hg.tsum_add htail
    _ = _ := by
      congr 1
      calc
        (∑' v, g v) = ∑ v ∈ T, g v := tsum_eq_sum (fun v hv => if_neg hv)
        _ = _ := Finset.sum_congr rfl fun v hv => if_pos hv

/-- One constant depending only on n,N precedes the polynomial, modulus,
cutoff, mass and physical scales. Both the full series and its actual tail
are proved summable before their sums are bounded or rearranged. -/
theorem exists_bound (n N : ℕ) (hN : n < N) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ (F : MvPolynomial (Fin n) ℤ) (q : ℕ), 1 ≤ q →
      ∀ (T : Finset (Fin n → ℤ)) (f : (Fin n → ℤ) → ℝ) (C P A : ℝ),
      0 ≤ C → 0 < P → (∀ v, 0 ≤ f v) →
      (∀ v : Fin n → ℤ, v ≠ 0 → v ∉ T →
        f v ≤ C*P^(-A)*‖(fun i => (v i : ℝ))‖^(-(N : ℝ))) →
      Summable (term F q f) ∧ Summable (tail F q f T) ∧
      (∑' v, term F q f v) = (∑ v ∈ T, term F q f v)+(∑' v, tail F q f T v) ∧
      (∑' v, tail F q f T v) ≤ K*C*P^(-A)*(q : ℝ)^(n+1) := by
  obtain ⟨K,hK,hdom⟩ := LatticeFrequencyTail.exists_domination_bound N hN
  refine ⟨K,hK,?_⟩
  intro F q hq T f C P A hC hP hf hbound
  have hcoeff : 0 ≤ (q : ℝ)^(n+1)*C*P^(-A) := by positivity
  have hnonneg : ∀ v, 0 ≤ tail F q f T v := by
    intro v
    unfold tail
    split_ifs
    · exact le_rfl
    · exact term_nonneg F q f hf v
  have hmajor : ∀ v, tail F q f T v ≤
      ((q : ℝ)^(n+1)*C*P^(-A))*LatticeFrequencyTail.weight N v := by
    intro v
    by_cases hvT : v ∈ T
    · simp only [tail,if_pos hvT]
      exact mul_nonneg hcoeff (LatticeFrequencyTail.weight_nonneg N v)
    by_cases hv : v=0
    · simp only [tail,if_neg hvT,term,if_pos hv]
      exact mul_nonneg hcoeff (LatticeFrequencyTail.weight_nonneg N v)
    rw [tail,if_neg hvT,term,if_neg hv]
    calc
      _ ≤ (q : ℝ)^(n+1)*(C*P^(-A)*LatticeFrequencyTail.weight N v) :=
        mul_le_mul (trivial_bound F q hq v) (hbound v hv hvT) (hf v) (by positivity)
      _ = _ := by ring
  obtain ⟨htail,ht⟩ := hdom (tail F q f T) _ hcoeff hnonneg hmajor
  obtain ⟨hs,he⟩ := summable_and_split F q f T htail
  refine ⟨hs,htail,he,?_⟩
  calc
    _ ≤ ((q : ℝ)^(n+1)*C*P^(-A))*K := ht
    _ = _ := by ring

end CubicTenVariables.CompleteSumFrequencyTail
