import CubicTenVariables.Targets
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Int.Interval
import Mathlib.Topology.Order.Real
import Mathlib.Topology.Order.OrderClosed

/-! Actual finite-box counts and the final positivity implication.
These results do not assert an asymptotic formula for cubic zeros.
They prove the elementary endpoint to which an independently established
positive main term and negligible error can be applied. -/

namespace CubicTenVariables
open MvPolynomial Filter
open scoped Topology

/-- The actual integral vectors in the closed sup-norm box of radius `B`. -/
def integerBox (n B : ℕ) : Finset (Fin n → ℤ) :=
  Fintype.piFinset fun _ => Finset.Icc (-(B : ℤ)) (B : ℤ)

@[simp] theorem mem_integerBox {n B : ℕ} {x : Fin n → ℤ} :
    x ∈ integerBox n B ↔ ∀ i, |x i| ≤ (B : ℤ) := by
  simp only [integerBox, Fintype.mem_piFinset, Finset.mem_Icc, abs_le]

/-- Actual nonzero integral zeros in a finite box; the origin is excluded. -/
def integerZerosInBox {n : ℕ} (F : MvPolynomial (Fin n) ℤ) (B : ℕ) :
    Finset (Fin n → ℤ) :=
  (integerBox n B).filter fun x => x ≠ 0 ∧ eval x F = 0

@[simp] theorem mem_integerZerosInBox {n B : ℕ}
    {F : MvPolynomial (Fin n) ℤ} {x : Fin n → ℤ} :
    x ∈ integerZerosInBox F B ↔
      (∀ i, |x i| ≤ (B : ℤ)) ∧ x ≠ 0 ∧ eval x F = 0 := by
  simp only [integerZerosInBox, Finset.mem_filter, mem_integerBox]

/-- The number of actual nonzero integral zeros in the radius-`B` box. -/
def integerZeroCount {n : ℕ} (F : MvPolynomial (Fin n) ℤ) (B : ℕ) : ℕ :=
  (integerZerosInBox F B).card

theorem exists_mem_integerBox {n : ℕ} (x : Fin n → ℤ) :
    ∃ B : ℕ, x ∈ integerBox n B := by
  refine ⟨Finset.univ.sup (fun i => (x i).natAbs), ?_⟩
  rw [mem_integerBox]
  intro i
  have hi : (x i).natAbs ≤ Finset.univ.sup (fun j => (x j).natAbs) :=
    Finset.le_sup (f := fun j => (x j).natAbs) (Finset.mem_univ i)
  simpa only [Int.natCast_natAbs] using (Nat.cast_le (α := ℤ)).mpr hi

theorem hasIntegerZero_of_count_pos {n B : ℕ} (F : MvPolynomial (Fin n) ℤ)
    (h : 0 < integerZeroCount F B) : HasIntegerZero F := by
  obtain ⟨x, hx⟩ := Finset.card_pos.mp h
  exact ⟨x, (mem_integerZerosInBox.mp hx).2⟩

theorem hasIntegerZero_iff_exists_count_pos {n : ℕ} (F : MvPolynomial (Fin n) ℤ) :
    HasIntegerZero F ↔ ∃ B : ℕ, 0 < integerZeroCount F B := by
  constructor
  · rintro ⟨x, hx, hFx⟩
    obtain ⟨B, hB⟩ := exists_mem_integerBox x
    refine ⟨B, Finset.card_pos.mpr ⟨x, ?_⟩⟩
    exact Finset.mem_filter.mpr ⟨hB, hx, hFx⟩
  · rintro ⟨B, hB⟩
    exact hasIntegerZero_of_count_pos F hB

/-- Without a nonzero integral zero, every one of these actual counts is zero. -/
theorem integerZeroCount_eq_zero_of_not_hasIntegerZero {n : ℕ}
    (F : MvPolynomial (Fin n) ℤ) (hF : ¬ HasIntegerZero F) (B : ℕ) :
    integerZeroCount F B = 0 := by
  by_contra hB
  exact hF (hasIntegerZero_of_count_pos F (Nat.pos_of_ne_zero hB))

/-- Any positive normalized limit of these actual counts forces a nonzero
integral zero. No polynomial homogeneity or analytic input is assumed. -/
theorem hasIntegerZero_of_normalized_count_tendsto {n : ℕ}
    (F : MvPolynomial (Fin n) ℤ) (k : ℕ) {c : ℝ} (hc : 0 < c)
    (hlim : Tendsto (fun B : ℕ => (integerZeroCount F B : ℝ) / (B : ℝ) ^ k)
      atTop (𝓝 c)) : HasIntegerZero F := by
  have hpos := hlim.eventually_const_lt hc
  obtain ⟨B, hB⟩ := hpos.exists
  apply hasIntegerZero_of_count_pos F
  by_contra h
  have hz : integerZeroCount F B = 0 := Nat.eq_zero_of_not_pos h
  simp only [hz, Nat.cast_zero, zero_div, lt_self_iff_false] at hB

/-- In ten variables a positive `B^7` asymptotic has the desired Diophantine
consequence. Establishing that asymptotic remains a separate theorem. -/
theorem hasIntegerZero_of_ten_variable_count_asymptotic
    (F : MvPolynomial (Fin 10) ℤ) {c : ℝ} (hc : 0 < c)
    (hlim : Tendsto (fun B : ℕ => (integerZeroCount F B : ℝ) / (B : ℝ) ^ 7)
      atTop (𝓝 c)) : HasIntegerZero F :=
  hasIntegerZero_of_normalized_count_tendsto F 7 hc hlim

end CubicTenVariables
