import CubicTenVariables.LatticeFrequencyTail
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! Nonzero-frequency tails with an arbitrary bounded nonnegative arithmetic
coefficient. Convergence and the finite-cut identity are proved from the
stated pointwise decay, without a convergence or literature premise. -/
set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.ArithmeticFrequencyTail
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

/-- The nonzero-frequency term, using a real nonnegative mass. -/
def term (a : (Fin n → ℤ) → ℝ)
    (f : (Fin n → ℤ) → ℝ) (v : Fin n → ℤ) : ℝ :=
  if v=0 then 0 else a v*f v

/-- The actual complement of a finite frequency cutoff. -/
def tail (a : (Fin n → ℤ) → ℝ)
    (f : (Fin n → ℤ) → ℝ) (T : Finset (Fin n → ℤ)) (v : Fin n → ℤ) : ℝ :=
  if v ∈ T then 0 else term a f v

theorem term_nonneg (a : (Fin n → ℤ) → ℝ)
    (f : (Fin n → ℤ) → ℝ) (ha : ∀ v, 0 ≤ a v) (hf : ∀ v, 0 ≤ f v) (v : Fin n → ℤ) :
    0 ≤ term a f v := by
  unfold term
  split_ifs
  · exact le_rfl
  · exact mul_nonneg (ha v) (hf v)

/-- A summable tail makes the complete nonzero-frequency series summable,
and the finite-cut decomposition is an exact equality. -/
theorem summable_and_split (a : (Fin n → ℤ) → ℝ)
    (f : (Fin n → ℤ) → ℝ) (T : Finset (Fin n → ℤ))
    (htail : Summable (tail a f T)) :
    Summable (term a f) ∧
      (∑' v, term a f v) = (∑ v ∈ T, term a f v)+(∑' v, tail a f T v) := by
  let g : (Fin n → ℤ) → ℝ := fun v => if v ∈ T then term a f v else 0
  have hg : Summable g := summable_of_ne_finset_zero (s := T) (by
    intro v hv
    exact if_neg hv)
  have he : term a f = fun v => g v+tail a f T v := by
    funext v
    by_cases hv : v ∈ T <;> simp [g,tail,hv]
  have hs : Summable (term a f) := he ▸ hg.add htail
  refine ⟨hs,?_⟩
  calc
    (∑' v, term a f v) = (∑' v, (g v+tail a f T v)) := congrArg (fun h => ∑' v, h v) he
    _ = (∑' v, g v)+(∑' v, tail a f T v) := hg.tsum_add htail
    _ = _ := by
      congr 1
      calc
        (∑' v, g v) = ∑ v ∈ T, g v := tsum_eq_sum (fun v hv => if_neg hv)
        _ = _ := Finset.sum_congr rfl fun v hv => if_pos hv

/-- The constant depends only on the lattice dimension and decay exponent.
The arithmetic coefficient bound M remains explicit and independent of the
mass function, cutoff and physical scales. -/
theorem exists_bound (n N : ℕ) (hN : n < N) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ (a : (Fin n → ℤ) → ℝ) (M : ℝ),
      (∀ v, 0 ≤ a v) → (∀ v, a v ≤ M) →
      ∀ (T : Finset (Fin n → ℤ)) (f : (Fin n → ℤ) → ℝ) (C P A : ℝ),
      0 ≤ C → 0 < P → (∀ v, 0 ≤ f v) →
      (∀ v : Fin n → ℤ, v ≠ 0 → v ∉ T →
        f v ≤ C*P^(-A)*‖(fun i => (v i : ℝ))‖^(-(N : ℝ))) →
      Summable (term a f) ∧ Summable (tail a f T) ∧
      (∑' v, term a f v) = (∑ v ∈ T, term a f v)+(∑' v, tail a f T v) ∧
      (∑' v, tail a f T v) ≤ K*M*C*P^(-A) := by
  obtain ⟨K,hK,hdom⟩ := LatticeFrequencyTail.exists_domination_bound N hN
  refine ⟨K,hK,?_⟩
  intro a M ha haM T f C P A hC hP hf hbound
  have hM : 0 ≤ M := (ha 0).trans (haM 0)
  have hcoeff : 0 ≤ M*C*P^(-A) := by positivity
  have hnonneg : ∀ v, 0 ≤ tail a f T v := by
    intro v
    unfold tail
    split_ifs
    · exact le_rfl
    · exact term_nonneg a f ha hf v
  have hmajor : ∀ v, tail a f T v ≤
      (M*C*P^(-A))*LatticeFrequencyTail.weight N v := by
    intro v
    by_cases hvT : v ∈ T
    · simp only [tail,if_pos hvT]
      exact mul_nonneg hcoeff (LatticeFrequencyTail.weight_nonneg N v)
    by_cases hv : v=0
    · simp only [tail,if_neg hvT,term,if_pos hv]
      exact mul_nonneg hcoeff (LatticeFrequencyTail.weight_nonneg N v)
    rw [tail,if_neg hvT,term,if_neg hv]
    calc
      _ ≤ M*(C*P^(-A)*LatticeFrequencyTail.weight N v) :=
        mul_le_mul (haM v) (hbound v hv hvT) (hf v) hM
      _ = _ := by ring
  obtain ⟨htail,ht⟩ := hdom (tail a f T) _ hcoeff hnonneg hmajor
  obtain ⟨hs,he⟩ := summable_and_split a f T htail
  refine ⟨hs,htail,he,?_⟩
  calc
    _ ≤ (M*C*P^(-A))*K := ht
    _ = _ := by ring

end CubicTenVariables.ArithmeticFrequencyTail
