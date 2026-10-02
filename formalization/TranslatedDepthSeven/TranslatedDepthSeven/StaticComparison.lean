import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

/-!
# Static comparison on a connected modulus graph

This is the finite-combinatorial core of the packet comparison.  It contains
no geometric state or counting hypothesis.  A label which does not terminate
at a vertex either differs across an edge or is one fixed label throughout a
connected graph.
-/

namespace TranslatedDepthSeven

namespace StaticComparison

open SimpleGraph

variable {V α : Type*} {G : SimpleGraph V}

/-- A function which has the same value at the endpoints of every edge has
the same value at any two reachable vertices. -/
theorem label_eq_of_reachable (label : V → α) {u v : V}
    (huv : G.Reachable u v)
    (hedge : ∀ ⦃x y⦄, G.Adj x y → label x = label y) :
    label u = label v := by
  have hrt : Relation.ReflTransGen G.Adj u v :=
    (G.reachable_iff_reflTransGen u v).mp huv
  have himage : Relation.ReflTransGen (fun x y : α ↦ x = y) (label u) (label v) :=
    hrt.lift label (fun _ _ hxy ↦ hedge hxy)
  rw [Relation.reflTransGen_eq_self (r := fun x y : α ↦ x = y)
    (fun _ ↦ rfl) (fun _ _ _ hxy hyz ↦ hxy.trans hyz)] at himage
  exact himage

/-- Static trichotomy used for packet surfaces and quotient curves.

`none` is a terminal node output.  If no vertex is terminal, either two
adjacent vertices have different labels, or one label occurs at every
vertex. -/
theorem connected_option_labels (hG : G.Connected) (label : V → Option α) :
    (∃ v, label v = none) ∨
      (∃ v w, G.Adj v w ∧ label v ≠ label w) ∨
      (∃ a, ∀ v, label v = some a) := by
  classical
  by_cases hnone : ∃ v, label v = none
  · exact Or.inl hnone
  right
  by_cases hedgeDiff : ∃ v w, G.Adj v w ∧ label v ≠ label w
  · exact Or.inl hedgeDiff
  right
  have hedge : ∀ ⦃v w⦄, G.Adj v w → label v = label w := by
    intro v w hvw
    by_contra hne
    exact hedgeDiff ⟨v, w, hvw, hne⟩
  let v₀ : V := Classical.choice hG.nonempty
  have hv₀ne : label v₀ ≠ none := by
    intro hv₀
    exact hnone ⟨v₀, hv₀⟩
  obtain ⟨a, ha⟩ := Option.ne_none_iff_exists.mp hv₀ne
  refine ⟨a, ?_⟩
  intro v
  have heq : label v₀ = label v :=
    label_eq_of_reachable label (hG v₀ v) hedge
  exact heq.symm.trans ha.symm

end StaticComparison

end TranslatedDepthSeven
