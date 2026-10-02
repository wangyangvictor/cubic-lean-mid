import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Max

/-!
# A static first-occurrence partition

The manuscript repeatedly fixes an order on a finite collection of geometric
objects and assigns a point to the first object containing it.  This file
records that construction as an ordinary disjoint partition of finite sets.
There is no recursive state: the cell indexed by `i` is defined by one
simultaneous formula saying that `i` is the least index whose set contains
the point.
-/

namespace TranslatedDepthSeven

noncomputable section

variable {ι α : Type*} [Fintype ι] [LinearOrder ι] [DecidableEq α]

/-- Points of `A i` for which `i` is the least index containing the point. -/
def firstOccurrenceCell (A : ι → Finset α) (i : ι) : Finset α :=
  (A i).filter fun x ↦ ∀ j, x ∈ A j → i ≤ j

@[simp]
theorem mem_firstOccurrenceCell_iff
    (A : ι → Finset α) (i : ι) (x : α) :
    x ∈ firstOccurrenceCell A i ↔
      x ∈ A i ∧ ∀ j, x ∈ A j → i ≤ j := by
  simp [firstOccurrenceCell]

/-- Distinct least-index cells are disjoint. -/
theorem firstOccurrenceCell_disjoint
    (A : ι → Finset α) {i j : ι} (hij : i ≠ j) :
    Disjoint (firstOccurrenceCell A i) (firstOccurrenceCell A j) := by
  rw [Finset.disjoint_left]
  intro x hxi hxj
  have hi := (mem_firstOccurrenceCell_iff A i x).mp hxi
  have hj := (mem_firstOccurrenceCell_iff A j x).mp hxj
  exact hij (le_antisymm (hi.2 j hj.1) (hj.2 i hi.1))

/-- The least-index cells have exactly the same union as the original finite
family. -/
theorem biUnion_firstOccurrenceCell_eq
    (A : ι → Finset α) :
    Finset.univ.biUnion (firstOccurrenceCell A) =
      Finset.univ.biUnion A := by
  ext x
  constructor
  · intro hx
    obtain ⟨i, -, hxi⟩ := Finset.mem_biUnion.mp hx
    exact Finset.mem_biUnion.mpr
      ⟨i, Finset.mem_univ i, (mem_firstOccurrenceCell_iff A i x).mp hxi |>.1⟩
  · intro hx
    obtain ⟨j, -, hxj⟩ := Finset.mem_biUnion.mp hx
    let J : Finset ι := Finset.univ.filter fun i ↦ x ∈ A i
    have hJ : J.Nonempty := ⟨j, by simp [J, hxj]⟩
    let i := J.min' hJ
    have hiJ : i ∈ J := Finset.min'_mem J hJ
    have hxi : x ∈ A i := (Finset.mem_filter.mp hiJ).2
    have hleast : ∀ l, x ∈ A l → i ≤ l := by
      intro l hxl
      exact Finset.min'_le J l (by simp [J, hxl])
    exact Finset.mem_biUnion.mpr
      ⟨i, Finset.mem_univ i,
        (mem_firstOccurrenceCell_iff A i x).mpr ⟨hxi, hleast⟩⟩

/-- Exact cardinality after replacing an ordered finite cover by its disjoint
least-index cells. -/
theorem card_biUnion_eq_sum_card_firstOccurrenceCell
    (A : ι → Finset α) :
    (Finset.univ.biUnion A).card =
      ∑ i : ι, (firstOccurrenceCell A i).card := by
  rw [← biUnion_firstOccurrenceCell_eq A,
    Finset.card_biUnion]
  intro i _ j _ hij
  exact firstOccurrenceCell_disjoint A hij

/-- The disjoint assignment never increases the sum of the individual
cardinalities. -/
theorem card_biUnion_le_sum_card
    (A : ι → Finset α) :
    (Finset.univ.biUnion A).card ≤ ∑ i : ι, (A i).card := by
  rw [card_biUnion_eq_sum_card_firstOccurrenceCell A]
  exact Finset.sum_le_sum fun i _ ↦
    Finset.card_le_card (Finset.filter_subset _ _)

end

end TranslatedDepthSeven
