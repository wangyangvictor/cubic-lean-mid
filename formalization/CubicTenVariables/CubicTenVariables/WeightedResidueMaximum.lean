import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-!
# The literal weighted residue maximum used in flexible lifting

The maximum ranges over every residue vector modulo a positive integer A.
Weights are summed over the given finite set of integer vectors in that
class. Nonnegativity is required only on that finite set, and only for the
nonnegativity theorem. The stationary-support bound is an exact residue-class
identification followed by the defining maximum bound.
-/

noncomputable section
namespace CubicTenVariables.WeightedResidueMaximum
open scoped BigOperators

attribute [local instance] Classical.propDecidable
variable (A : ℕ) [NeZero A] {n : ℕ}

/-- The weighted mass of one actual residue class. -/
def classWeight (V : Finset (Fin n → ℤ)) (w : (Fin n → ℤ) → ℝ)
    (k : Fin n → ZMod A) : ℝ :=
  ∑ v ∈ V.filter (fun v => (fun i => (v i : ZMod A)) = k), w v

/-- The actual attained finite maximum E_A(V;w). -/
def maximum (V : Finset (Fin n → ℤ)) (w : (Fin n → ℤ) → ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (classWeight A V w)

theorem maximum_attained (V : Finset (Fin n → ℤ)) (w : (Fin n → ℤ) → ℝ) :
    ∃ k : Fin n → ZMod A, maximum A V w = classWeight A V w k := by
  obtain ⟨k, _, hk⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty (classWeight A V w)
  exact ⟨k, hk⟩

theorem classWeight_le_maximum (V : Finset (Fin n → ℤ))
    (w : (Fin n → ℤ) → ℝ) (k : Fin n → ZMod A) :
    classWeight A V w k ≤ maximum A V w :=
  Finset.le_sup' (classWeight A V w) (Finset.mem_univ k)

omit [NeZero A] in
theorem classWeight_nonneg (V : Finset (Fin n → ℤ)) (w : (Fin n → ℤ) → ℝ)
    (hw : ∀ v ∈ V, 0 ≤ w v) (k : Fin n → ZMod A) : 0 ≤ classWeight A V w k := by
  apply Finset.sum_nonneg
  intro v hv
  exact hw v (Finset.mem_filter.mp hv).1

theorem maximum_nonneg (V : Finset (Fin n → ℤ)) (w : (Fin n → ℤ) → ℝ)
    (hw : ∀ v ∈ V, 0 ≤ w v) : 0 ≤ maximum A V w :=
  (classWeight_nonneg A V w hw 0).trans (classWeight_le_maximum A V w 0)

omit [NeZero A] in
/-- The literal stationary congruence is precisely the residue class -b. -/
theorem stationary_support_iff (b v : Fin n → ℤ) :
    (∀ i, (A : ℤ) ∣ b i + v i) ↔
      (fun i => (v i : ZMod A)) = fun i => -(b i : ZMod A) := by
  simp only [funext_iff, ← ZMod.intCast_zmod_eq_zero_iff_dvd, Int.cast_add]
  constructor
  · intro h i
    exact eq_neg_iff_add_eq_zero.mpr (by simpa only [add_comm] using h i)
  · intro h i
    rw [h i, add_neg_cancel]

omit [NeZero A] in
/-- Exact equality with the indicated class mass, before taking a maximum. -/
theorem sum_stationary_support_eq (V : Finset (Fin n → ℤ))
    (w : (Fin n → ℤ) → ℝ) (b : Fin n → ℤ) :
    (∑ v ∈ V.filter (fun v => ∀ i, (A : ℤ) ∣ b i + v i), w v) =
      classWeight A V w (fun i => -(b i : ZMod A)) := by
  simp only [stationary_support_iff, classWeight]

/-- Fixed-gradient support contributes at most E_A(V;w). The bound even
holds for signed weights; applications may separately assume nonnegativity. -/
theorem sum_stationary_support_le (V : Finset (Fin n → ℤ))
    (w : (Fin n → ℤ) → ℝ) (b : Fin n → ℤ) :
    (∑ v ∈ V.filter (fun v => ∀ i, (A : ℤ) ∣ b i + v i), w v) ≤ maximum A V w := by
  rw [sum_stationary_support_eq]
  exact classWeight_le_maximum A V w _

theorem sum_if_stationary_support_le (V : Finset (Fin n → ℤ))
    (w : (Fin n → ℤ) → ℝ) (b : Fin n → ℤ) :
    (∑ v ∈ V, if (∀ i, (A : ℤ) ∣ b i + v i) then w v else 0) ≤ maximum A V w := by
  simpa only [Finset.sum_filter] using sum_stationary_support_le A V w b

@[simp] theorem maximum_empty (w : (Fin n → ℤ) → ℝ) : maximum A ∅ w = 0 := by
  obtain ⟨k,hk⟩ := maximum_attained A ∅ w
  simp only [classWeight, Finset.filter_empty, Finset.sum_empty] at hk
  exact hk

end CubicTenVariables.WeightedResidueMaximum
