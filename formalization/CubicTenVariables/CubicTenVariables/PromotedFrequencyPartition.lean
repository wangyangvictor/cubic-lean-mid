import Mathlib.Data.Nat.Find
import Mathlib.Data.Set.Lattice
import Mathlib.Tactic

/-! The literal finite promotion partition used for ten rational variables.
The six levels partition the punctured space; the origin is a separate
seventh part. This corrects the manuscript's sentence calling the six
punctured levels a partition of the whole space. The actual promotion opens
are still to be supplied by the geometric construction. -/

set_option autoImplicit false
namespace CubicTenVariables.PromotedFrequencyPartition

variable {α : Type*}

/-- Original depth layer, with all terminal depths retained at level five. -/
def layer (Z : ℕ → Set α) (j : ℕ) : Set α :=
  if j < 5 then Z j \ Z (j+1) else Z 5

/-- Remove the open from its old layer and promote the next open by one level. -/
def promoted (Z U : ℕ → Set α) (j : ℕ) : Set α :=
  if j < 5 then (layer Z j \ U j) ∪ U (j+1) else Z 5

theorem layer_subset (Z : ℕ → Set α) {j : ℕ} (hj : j ≤ 5) : layer Z j ⊆ Z j := by
  by_cases h : j < 5
  · simpa only [layer,if_pos h] using (Set.diff_subset : Z j \ Z (j+1) ⊆ Z j)
  · have he : j = 5 := by omega
    subst j
    simp [layer]

theorem exists_layer (Z : ℕ → Set α) (hZ : Z 0 = Set.univ) (x : α) :
    ∃ j : Fin 6, x ∈ layer Z j.val := by
  classical
  let j := Nat.findGreatest (fun i => x ∈ Z i) 5
  have hj : j ≤ 5 := Nat.findGreatest_le _
  have hx : x ∈ Z j := Nat.findGreatest_spec (P:=fun i => x ∈ Z i) (by omega : 0 ≤ 5) (by change x ∈ Z 0; rw [hZ]; trivial)
  refine ⟨⟨j,by omega⟩,?_⟩
  change x ∈ layer Z j
  by_cases h : j < 5
  · rw [layer,if_pos h]
    exact ⟨hx,Nat.findGreatest_is_greatest (P:=fun i => x ∈ Z i) (n:=5) (k:=j+1) (by change j < j+1; omega) (by omega)⟩
  · have he : j = 5 := by omega
    rw [layer,if_neg h]
    simpa only [he] using hx

theorem promoted_subset (Z U : ℕ → Set α) (hZ : Antitone Z)
    (hU : ∀ j, j ≤ 5 → U j ⊆ layer Z j) {j : ℕ} (hj : j ≤ 5) :
    promoted Z U j ⊆ Z j := by
  by_cases h : j < 5
  · rw [promoted,if_pos h]
    rintro x (hx | hx)
    · exact layer_subset Z hj hx.1
    · exact hZ (by omega : j ≤ j+1) (layer_subset Z (by omega) (hU (j+1) (by omega) hx))
  · have he : j = 5 := by omega
    subst j
    simp [promoted]

theorem promoted_disjoint (Z U : ℕ → Set α) (hZ : Antitone Z)
    (hU : ∀ j, j ≤ 5 → U j ⊆ layer Z j) (hU5 : U 5 = ∅)
    {j k : ℕ} (hjk : j < k) (hk : k ≤ 5) :
    Disjoint (promoted Z U j) (promoted Z U k) := by
  apply Set.disjoint_left.mpr
  intro x hxj hxk
  have hj : j < 5 := by omega
  rw [promoted,if_pos hj] at hxj
  rcases hxj with hxj | hxj
  · have hnot : x ∉ Z (j+1) := by
      have hl : x ∈ Z j \ Z (j+1) := by simpa only [layer,if_pos hj] using hxj.1
      exact hl.2
    exact hnot (hZ (by omega) (promoted_subset Z U hZ hU hk hxk))
  · have hj1 : j+1 < 5 := by
      by_contra hn
      have he : j+1 = 5 := by omega
      rw [he,hU5] at hxj
      exact hxj
    have hnot : x ∉ Z (j+2) := by
      have hu := hU (j+1) (by omega) hxj
      simp only [layer,if_pos hj1,Nat.add_assoc] at hu
      exact hu.2
    by_cases he : k = j+1
    · subst k
      rw [promoted,if_pos hj1] at hxk
      rcases hxk with hxk | hxk
      · exact hxk.2 hxj
      · have hu := layer_subset Z (by omega) (hU (j+1+1) (by omega) hxk)
        exact hnot (by simpa only [Nat.add_assoc] using hu)
    · exact hnot (hZ (by omega) (promoted_subset Z U hZ hU hk hxk))

theorem exists_promoted (Z U : ℕ → Set α) (hZ0 : Z 0 = Set.univ)
    (hU0 : U 0 = ∅) (x : α) : ∃ j : Fin 6, x ∈ promoted Z U j.val := by
  obtain ⟨⟨j,hj⟩,hx⟩ := exists_layer Z hZ0 x
  by_cases h5 : j < 5
  · by_cases hu : x ∈ U j
    · have hj0 : 0 < j := by
        by_contra hn
        have he : j = 0 := by omega
        rw [he,hU0] at hu
        exact hu
      refine ⟨⟨j-1,by omega⟩,?_⟩
      rw [promoted,if_pos (by omega : j-1 < 5)]
      exact Or.inr (by simpa only [Nat.sub_add_cancel hj0] using hu)
    · refine ⟨⟨j,hj⟩,?_⟩
      rw [promoted,if_pos h5]
      exact Or.inl ⟨hx,hu⟩
  · refine ⟨⟨j,hj⟩,?_⟩
    simpa only [promoted,layer,if_neg h5] using hx

/-- Exactly one rearranged level, before removing the distinguished origin. -/
theorem existsUnique_promoted (Z U : ℕ → Set α) (hZ0 : Z 0 = Set.univ)
    (hZ : Antitone Z) (hU : ∀ j, j ≤ 5 → U j ⊆ layer Z j)
    (hU0 : U 0 = ∅) (hU5 : U 5 = ∅) (x : α) :
    ∃! j : Fin 6, x ∈ promoted Z U j.val := by
  obtain ⟨j,hj⟩ := exists_promoted Z U hZ0 hU0 x
  refine ⟨j,hj,?_⟩
  intro k hk
  by_contra hne
  have hn : k.val ≠ j.val := fun he => hne (Fin.ext he)
  rcases lt_or_gt_of_ne hn with hlt | hgt
  · exact Set.disjoint_left.mp (promoted_disjoint Z U hZ hU hU5 hlt (by omega)) hk hj
  · exact Set.disjoint_left.mp (promoted_disjoint Z U hZ hU hU5 hgt (by omega)) hj hk

variable [Zero α]

/-- The source's P_0,...,P_5, all punctured. P_6 is the separate origin. -/
def part (Z U : ℕ → Set α) (j : Fin 6) : Set α := promoted Z U j.val \ {0}

theorem mem_part (Z U : ℕ → Set α) (j : Fin 6) (x : α) :
    x ∈ part Z U j ↔ x ∈ promoted Z U j.val ∧ x ≠ 0 := Iff.rfl

theorem existsUnique_part (Z U : ℕ → Set α) (hZ0 : Z 0 = Set.univ)
    (hZ : Antitone Z) (hU : ∀ j, j ≤ 5 → U j ⊆ layer Z j)
    (hU0 : U 0 = ∅) (hU5 : U 5 = ∅) (x : α) (hx : x ≠ 0) :
    ∃! j : Fin 6, x ∈ part Z U j := by
  obtain ⟨j,hj,hunique⟩ := existsUnique_promoted Z U hZ0 hZ hU hU0 hU5 x
  exact ⟨j,⟨hj,hx⟩,fun k hk => hunique k hk.1⟩

theorem union_parts (Z U : ℕ → Set α) (hZ0 : Z 0 = Set.univ)
    (hU0 : U 0 = ∅) : (⋃ j : Fin 6, part Z U j) = {x | x ≠ 0} := by
  ext x
  constructor
  · intro hx
    obtain ⟨j,hj⟩ := Set.mem_iUnion.mp hx
    exact hj.2
  · intro hx
    obtain ⟨j,hj⟩ := exists_promoted Z U hZ0 hU0 x
    exact Set.mem_iUnion.mpr ⟨j,hj,hx⟩

theorem union_parts_with_origin (Z U : ℕ → Set α) (hZ0 : Z 0 = Set.univ)
    (hU0 : U 0 = ∅) : (⋃ j : Fin 6, part Z U j) ∪ {0} = Set.univ := by
  rw [union_parts Z U hZ0 hU0]
  ext x
  simp only [Set.mem_union,Set.mem_setOf_eq,Set.mem_singleton_iff,Set.mem_univ,iff_true]
  by_cases hx : x = 0
  · exact Or.inr hx
  · exact Or.inl hx

end CubicTenVariables.PromotedFrequencyPartition
