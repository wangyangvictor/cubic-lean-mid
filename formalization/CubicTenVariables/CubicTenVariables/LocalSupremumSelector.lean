import CubicTenVariables.LocalSupremumWindow

/-! Exact finite selectors for actual lattice-window maxima. Centers with
empty windows are removed, including when the maximum on a nonempty window
is zero. The selector is only asserted to lie in the frequency set on the
actual finite set of active centers. -/
set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.LocalSupremumSelector
open LocalSupremumWindow
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

/-- Exactly the centers whose real-width windows are nonempty. The rounded
box is used only to construct a finite set and adds no centers. -/
def realCenters (S : Finset (Fin n → ℤ)) (L : ℝ) : Finset (Fin n → ℤ) :=
  (centers S ⌈max L 0⌉₊).filter fun v => (window S v L).Nonempty

@[simp] theorem mem_realCenters (S : Finset (Fin n → ℤ)) (L : ℝ)
    (v : Fin n → ℤ) : v ∈ realCenters S L ↔ (window S v L).Nonempty := by
  constructor
  · exact fun h => (Finset.mem_filter.mp h).2
  · intro h
    refine Finset.mem_filter.mpr ⟨?_,h⟩
    obtain ⟨a,ha⟩ := h
    obtain ⟨haS,haL⟩ := (mem_window S v a L).mp ha
    apply (mem_centers S ⌈max L 0⌉₊ v).mpr
    refine ⟨a,(mem_window S v a _).mpr ⟨haS,?_⟩⟩
    intro i
    exact (haL i).trans ((le_max_left L 0).trans (Nat.le_ceil _))

@[simp] theorem realCenters_empty (L : ℝ) : realCenters (∅ : Finset (Fin n → ℤ)) L=∅ := by
  ext v
  simp [window]

/-- A maximizing frequency on every active center, extended by zero to
the other centers. No claim about membership is made on empty windows. -/
def selector (S : Finset (Fin n → ℤ)) (g : (Fin n → ℤ) → ℝ)
    (L : ℝ) (v : Fin n → ℤ) : Fin n → ℤ :=
  if h : (window S v L).Nonempty then
    Classical.choose (maximum_attained S g v L h) else 0

theorem selector_spec (S : Finset (Fin n → ℤ)) (g : (Fin n → ℤ) → ℝ)
    (L : ℝ) (v : Fin n → ℤ) (hv : v ∈ realCenters S L) :
    selector S g L v ∈ S ∧
      (∀ i, |(selector S g L v i : ℝ)-(v i : ℝ)| ≤ L) ∧
      maximum S g v L = g (selector S g L v) := by
  have h := (mem_realCenters S L v).mp hv
  simpa only [selector,dif_pos h] using
    Classical.choose_spec (maximum_attained S g v L h)

theorem maximum_zero_of_not_mem_realCenters (S : Finset (Fin n → ℤ))
    (g : (Fin n → ℤ) → ℝ) (L : ℝ) (v : Fin n → ℤ)
    (hv : v ∉ realCenters S L) : maximum S g v L=0 := by
  have h : ¬(window S v L).Nonempty := by simpa using hv
  simp [maximum,h]

/-- Exact reduction of the unrestricted lattice sum to the selected values
on precisely the nonempty windows. No sign hypothesis on g is needed. -/
theorem tsum_eq_sum_selector (S : Finset (Fin n → ℤ))
    (g : (Fin n → ℤ) → ℝ) (L : ℝ) :
    (∑' v : Fin n → ℤ, maximum S g v L) =
      ∑ v ∈ realCenters S L, g (selector S g L v) := by
  calc
    (∑' v : Fin n → ℤ, maximum S g v L) =
        ∑ v ∈ realCenters S L, maximum S g v L :=
      tsum_eq_sum fun v hv => maximum_zero_of_not_mem_realCenters S g L v hv
    _ = _ := Finset.sum_congr rfl fun v hv => (selector_spec S g L v hv).2.2

/-- The center bound follows from the selected frequency and its actual
window inequality; it does not use an integer rounding of the real width. -/
theorem center_bound (a v : Fin n → ℤ) (B L : ℝ)
    (ha : ∀ i, |(a i : ℝ)| ≤ B)
    (hav : ∀ i, |(a i : ℝ)-(v i : ℝ)| ≤ L) :
    ∀ i, |(v i : ℝ)| ≤ B+L := by
  intro i
  calc
    |(v i : ℝ)| = |(a i : ℝ)+((v i : ℝ)-(a i : ℝ))| := by ring_nf
    _ ≤ |(a i : ℝ)|+|(v i : ℝ)-(a i : ℝ)| := abs_add_le _ _
    _ ≤ B+L := add_le_add (ha i) (by simpa only [abs_sub_comm] using hav i)

/-- Existential packaging for an arbitrary finite frequency set. -/
theorem exists_selector (S : Finset (Fin n → ℤ))
    (g : (Fin n → ℤ) → ℝ) (L : ℝ) :
    ∃ (T : Finset (Fin n → ℤ)) (a : (Fin n → ℤ) → (Fin n → ℤ)),
      (∀ v, v ∈ T ↔ (window S v L).Nonempty) ∧
      (∀ v ∈ T, a v ∈ S ∧ (∀ i, |(a v i : ℝ)-(v i : ℝ)| ≤ L) ∧
        maximum S g v L=g (a v)) ∧
      (∑' v : Fin n → ℤ, maximum S g v L) = ∑ v ∈ T, g (a v) :=
  ⟨realCenters S L,selector S g L,mem_realCenters S L,
    selector_spec S g L,tsum_eq_sum_selector S g L⟩

/-- The source's actual nonzero bounded frequencies, retaining the exact
selector and the coordinate bound needed for subsequent volume estimates. -/
theorem exists_frequency_selector (g : (Fin n → ℤ) → ℝ) (B L : ℝ) :
    ∃ (T : Finset (Fin n → ℤ)) (a : (Fin n → ℤ) → (Fin n → ℤ)),
      (∀ v, v ∈ T ↔ (window (frequencies n B) v L).Nonempty) ∧
      (∀ v ∈ T, a v ≠ 0 ∧ (∀ i, |(a v i : ℝ)| ≤ B) ∧
        (∀ i, |(a v i : ℝ)-(v i : ℝ)| ≤ L) ∧
        (∀ i, |(v i : ℝ)| ≤ B+L) ∧
        maximum (frequencies n B) g v L=g (a v)) ∧
      (∑' v : Fin n → ℤ, maximum (frequencies n B) g v L) =
        ∑ v ∈ T, g (a v) := by
  refine ⟨realCenters (frequencies n B) L,selector (frequencies n B) g L,
    mem_realCenters _ L,?_,tsum_eq_sum_selector _ g L⟩
  intro v hv
  obtain ⟨ha,hav,he⟩ := selector_spec (frequencies n B) g L v hv
  obtain ⟨hne,hab⟩ := (mem_frequencies B _).mp ha
  exact ⟨hne,hab,hav,center_bound _ v B L hab hav,he⟩

end CubicTenVariables.LocalSupremumSelector
