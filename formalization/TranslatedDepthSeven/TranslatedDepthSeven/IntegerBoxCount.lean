import TranslatedDepthSeven.Parameters
import Mathlib.Data.Fin.Tuple.Finset
import Mathlib.Data.Int.Interval

/-!
# Coefficient-independent counting in an integral box

This is the elementary bounded-height estimate used to dispose of a fixed
small-height range before invoking a logarithmic asymptotic formula.  It is a
count of the ambient box and contains no variety-dependent hypothesis.
-/

namespace TranslatedDepthSeven

noncomputable section

open Finset

/-- The literal integral sup-norm box `[-M,M]^n`. -/
def integerSupNormBox (n M : ℕ) : Finset (IntVector n) :=
  Fintype.piFinset fun _ : Fin n ↦ Finset.Icc (-(M : ℤ)) (M : ℤ)

@[simp]
theorem mem_integerSupNormBox_iff {n M : ℕ} (x : IntVector n) :
    x ∈ integerSupNormBox n M ↔ ∀ i, (x i).natAbs ≤ M := by
  simp only [integerSupNormBox, Fintype.mem_piFinset, Finset.mem_Icc]
  constructor
  · intro h i
    specialize h i
    omega
  · intro h i
    specialize h i
    omega

/-- Exact cardinality of the integral sup-norm box. -/
theorem card_integerSupNormBox (n M : ℕ) :
    (integerSupNormBox n M).card = (2 * M + 1) ^ n := by
  simp [integerSupNormBox, Int.card_Icc]
  congr 1
  omega

/-- Every finite family of integral vectors with coordinate bound `M` has at
most `(2M+1)^n` members. -/
theorem card_intVector_finset_le_box {n M : ℕ} (A : Finset (IntVector n))
    (hA : ∀ x ∈ A, ∀ i, (x i).natAbs ≤ M) :
    A.card ≤ (2 * M + 1) ^ n := by
  rw [← card_integerSupNormBox n M]
  apply Finset.card_le_card
  intro x hx
  rw [mem_integerSupNormBox_iff]
  exact hA x hx

/-- A strict real sup-norm bound `|x_i| < H` is contained in the integral box
of radius `ceil H`.  This is the form matching Pila's affine height. -/
theorem card_intVector_finset_lt_real_le_ceil_pow {n : ℕ}
    (A : Finset (IntVector n)) {H : ℝ}
    (hA : ∀ x ∈ A, ∀ i, |(x i : ℝ)| < H) :
    A.card ≤ (2 * ⌈H⌉₊ + 1) ^ n := by
  apply card_intVector_finset_le_box A
  intro x hx i
  have habs : ((x i).natAbs : ℝ) < H := by
    simpa [Nat.cast_natAbs] using hA x hx i
  exact_mod_cast (lt_of_lt_of_le habs (Nat.le_ceil H)).le

/-- Non-strict real coordinate bounds are converted to Pila's strict height
convention by enlarging the height by one. -/
theorem card_intVector_finset_le_real_le_ceil_add_one_pow {n : ℕ}
    (A : Finset (IntVector n)) {H : ℝ}
    (hA : ∀ x ∈ A, ∀ i, |(x i : ℝ)| ≤ H) :
    A.card ≤ (2 * ⌈H + 1⌉₊ + 1) ^ n := by
  apply card_intVector_finset_lt_real_le_ceil_pow A
  intro x hx i
  exact (hA x hx i).trans_lt (lt_add_one H)

end

end TranslatedDepthSeven
