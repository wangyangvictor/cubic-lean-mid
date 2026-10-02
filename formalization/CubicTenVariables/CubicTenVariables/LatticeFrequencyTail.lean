import Mathlib.Algebra.Module.ZLattice.Summable

/-! Summable inverse powers of the literal sup norm of integer frequency
vectors, and domination bounds for actual nonnegative infinite sums. -/
set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.LatticeFrequencyTail
open scoped BigOperators
variable {n : ℕ}

/-- Actual real sup norm, rather than a chosen equivalent lattice norm. -/
def weight (N : ℕ) (v : Fin n → ℤ) : ℝ :=
  ‖(fun i => (v i : ℝ))‖^(-(N : ℝ))

theorem weight_nonneg (N : ℕ) (v : Fin n → ℤ) : 0 ≤ weight N v :=
  Real.rpow_nonneg (norm_nonneg _) _

/-- Convergence on the entire lattice; for N>n the zero vector contributes
zero, with the standard real-power convention. -/
theorem summable_weight (N : ℕ) (hN : n < N) :
    Summable (weight (n := n) N) := by
  let L := Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Fin n)))
  let e : (Fin n → ℤ) → L := fun v => ⟨fun i => (v i : ℝ), by
    apply ((Pi.basisFun ℝ (Fin n)).mem_span_iff_repr_mem ℤ _).mpr
    intro i
    exact ⟨v i,by simp⟩⟩
  have he : Function.Injective e := by
    intro v w h
    funext i
    have hi := congrArg (fun z : L => (z : Fin n → ℝ) i) h
    change (v i : ℝ)=(w i : ℝ) at hi
    exact_mod_cast hi
  have hr : Module.finrank ℤ L=n := by
    rw [ZLattice.rank ℝ L]
    simp
  have hlt : -(N : ℝ) < -(Module.finrank ℤ L : ℝ) := by
    rw [hr]
    exact neg_lt_neg (by exact_mod_cast hN)
  have hs := (ZLattice.summable_norm_rpow L (-(N : ℝ)) hlt).comp_injective he
  exact hs

/-- Literal version useful without unfolding the weight definition. -/
theorem summable_norm_rpow (N : ℕ) (hN : n < N) :
    Summable (fun v : Fin n → ℤ => ‖(fun i => (v i : ℝ))‖^(-(N : ℝ))) :=
  summable_weight N hN

/-- A single finite positive constant before all dominated functions and
scales. Summability is an explicit conclusion, not inferred from a value
of a potentially totalized tsum. -/
theorem exists_domination_bound (N : ℕ) (hN : n < N) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ (f : (Fin n → ℤ) → ℝ) (C : ℝ), 0 ≤ C →
      (∀ v, 0 ≤ f v) → (∀ v, f v ≤ C*weight N v) →
      Summable f ∧ (∑' v, f v) ≤ C*K := by
  have hs := summable_weight N hN
  let K : ℝ := 1+∑' v : Fin n → ℤ, weight N v
  have hK : 1 ≤ K := by
    have ht : 0 ≤ (∑' v : Fin n → ℤ, weight N v) :=
      tsum_nonneg (weight_nonneg (n := n) N)
    dsimp [K]
    linarith
  refine ⟨K,hK,?_⟩
  intro f C hC hf hbound
  have hmaj := hs.mul_left C
  have hsum : Summable f := Summable.of_nonneg_of_le hf hbound hmaj
  refine ⟨hsum,?_⟩
  calc
    (∑' v, f v) ≤ ∑' v, C*weight N v := hsum.tsum_le_tsum hbound hmaj
    _ = C*∑' v : Fin n → ℤ, weight N v := tsum_mul_left
    _ ≤ C*K := mul_le_mul_of_nonneg_left (by dsimp [K]; linarith) hC

end CubicTenVariables.LatticeFrequencyTail
