import TranslatedDepthSeven.StaticComparison
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# A static partition with a point-dependent connected vertex set

In the square-free reservoir argument, the admissible moduli for a point
are those coprime to its displayed integer certificates.  This is a
point-dependent induced subgraph of one fixed finite reservoir graph.  The
certificate-deletion theorem proves that this induced subgraph is connected.

This file records the exact finite-set consequence.  At every point one
restricts the component labels to its surviving vertices.  Connectedness
then gives one of three literal alternatives: an empty label at a surviving
vertex, unequal labels on a surviving edge, or one nonempty label on every
surviving vertex.  The last sum ranges only over labels which actually occur
at a surviving point--vertex pair, so the ambient label type need not be
finite.
-/

namespace TranslatedDepthSeven

noncomputable section

open SimpleGraph

universe u v w

variable {V : Type u} {A : Type v} {B : Type w}
variable {G : SimpleGraph V}

/-- The finite set of labels which occur at a surviving point--vertex pair. -/
def occurringPointwiseLabels
    [DecidableEq V] [DecidableEq A] [DecidableEq B]
    (X : Finset A) (vertices : A → Finset V)
    (label : A → V → Option B) : Finset (Option B) := by
  classical
  exact X.biUnion fun x ↦ (vertices x).image (label x)

@[simp]
theorem mem_occurringPointwiseLabels_iff
    [DecidableEq V] [DecidableEq A] [DecidableEq B]
    (X : Finset A) (vertices : A → Finset V)
    (label : A → V → Option B) (o : Option B) :
    o ∈ occurringPointwiseLabels X vertices label ↔
      ∃ x ∈ X, ∃ v ∈ vertices x, label x v = o := by
  classical
  simp [occurringPointwiseLabels]

/-- Cardinal form of the connected-label trichotomy when the connected
induced vertex set is allowed to depend on the point.

The edge sum is over ordered pairs.  This is harmless, and is the convenient
form for direct comparison with the directed-edge reservoir bound. -/
theorem card_le_sum_pointwiseConnected_vertex_edge_persistent
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    [DecidableEq A] [DecidableEq B]
    (X : Finset A) (vertices : A → Finset V)
    (label : A → V → Option B)
    (hconnected : ∀ x ∈ X,
      (G.induce (↑(vertices x) : Set V)).Connected) :
    X.card ≤
      (∑ v : V,
        (X.filter fun x ↦ v ∈ vertices x ∧ label x v = none).card) +
      (∑ v : V, ∑ w : V,
        (X.filter fun x ↦
          v ∈ vertices x ∧ w ∈ vertices x ∧
            G.Adj v w ∧ label x v ≠ label x w).card) +
      (∑ o ∈ occurringPointwiseLabels X vertices label,
        (X.filter fun x ↦
          o ≠ none ∧ ∀ v ∈ vertices x, label x v = o).card) := by
  classical
  let vertexUnion : Finset A :=
    Finset.univ.biUnion fun v ↦
      X.filter fun x ↦ v ∈ vertices x ∧ label x v = none
  let edgeUnion : Finset A :=
    Finset.univ.biUnion fun v ↦
      Finset.univ.biUnion fun w ↦
        X.filter fun x ↦
          v ∈ vertices x ∧ w ∈ vertices x ∧
            G.Adj v w ∧ label x v ≠ label x w
  let persistentUnion : Finset A :=
    (occurringPointwiseLabels X vertices label).biUnion fun o ↦
      X.filter fun x ↦
        o ≠ none ∧ ∀ v ∈ vertices x, label x v = o
  have hcover : X ⊆ vertexUnion ∪ edgeUnion ∪ persistentUnion := by
    intro x hx
    let S : Set V := ↑(vertices x)
    let restrictedLabel : S → Option B := fun v ↦ label x v.1
    rcases StaticComparison.connected_option_labels
        (hconnected x hx) restrictedLabel with
      ⟨v, hv⟩ | ⟨v, w, hvw, hne⟩ | ⟨b, hb⟩
    · apply Finset.mem_union_left
      apply Finset.mem_union_left
      exact Finset.mem_biUnion.mpr
        ⟨v.1, Finset.mem_univ v.1,
          Finset.mem_filter.mpr ⟨hx, v.2, hv⟩⟩
    · apply Finset.mem_union_left
      apply Finset.mem_union_right
      exact Finset.mem_biUnion.mpr
        ⟨v.1, Finset.mem_univ v.1,
          Finset.mem_biUnion.mpr
            ⟨w.1, Finset.mem_univ w.1,
              Finset.mem_filter.mpr
                ⟨hx, v.2, w.2, hvw, hne⟩⟩⟩
    · apply Finset.mem_union_right
      let v₀ : S := Classical.choice (hconnected x hx).nonempty
      have hoccurs : some b ∈ occurringPointwiseLabels X vertices label := by
        exact (mem_occurringPointwiseLabels_iff X vertices label (some b)).2
          ⟨x, hx, v₀.1, v₀.2, hb v₀⟩
      exact Finset.mem_biUnion.mpr
        ⟨some b, hoccurs, Finset.mem_filter.mpr
          ⟨hx, Option.some_ne_none b, by
            intro v hv
            exact hb ⟨v, hv⟩⟩⟩
  have hvertex : vertexUnion.card ≤
      ∑ v : V,
        (X.filter fun x ↦ v ∈ vertices x ∧ label x v = none).card := by
    exact Finset.card_biUnion_le
  have hedge : edgeUnion.card ≤
      ∑ v : V, ∑ w : V,
        (X.filter fun x ↦
          v ∈ vertices x ∧ w ∈ vertices x ∧
            G.Adj v w ∧ label x v ≠ label x w).card := by
    refine Finset.card_biUnion_le.trans ?_
    apply Finset.sum_le_sum
    intro v _hv
    exact Finset.card_biUnion_le
  have hpersistent : persistentUnion.card ≤
      ∑ o ∈ occurringPointwiseLabels X vertices label,
        (X.filter fun x ↦
          o ≠ none ∧ ∀ v ∈ vertices x, label x v = o).card := by
    exact Finset.card_biUnion_le
  calc
    X.card ≤ (vertexUnion ∪ edgeUnion ∪ persistentUnion).card :=
      Finset.card_le_card hcover
    _ ≤ (vertexUnion ∪ edgeUnion).card + persistentUnion.card :=
      Finset.card_union_le _ _
    _ ≤ (vertexUnion.card + edgeUnion.card) + persistentUnion.card :=
      Nat.add_le_add_right (Finset.card_union_le _ _) _
    _ ≤
        ((∑ v : V,
            (X.filter fun x ↦
              v ∈ vertices x ∧ label x v = none).card) +
          (∑ v : V, ∑ w : V,
            (X.filter fun x ↦
              v ∈ vertices x ∧ w ∈ vertices x ∧
                G.Adj v w ∧ label x v ≠ label x w).card)) +
          (∑ o ∈ occurringPointwiseLabels X vertices label,
            (X.filter fun x ↦
              o ≠ none ∧ ∀ v ∈ vertices x, label x v = o).card) :=
      Nat.add_le_add (Nat.add_le_add hvertex hedge) hpersistent
    _ = _ := by omega

end

end TranslatedDepthSeven
