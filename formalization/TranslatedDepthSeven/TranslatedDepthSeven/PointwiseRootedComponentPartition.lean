import TranslatedDepthSeven.PointwiseConnectedComponentPartition

/-! When a common root survives every point-dependent prime deletion, all
persistent labels already occur at that root. This keeps the number of
persistent curves controlled by one initial auxiliary cut. -/

namespace TranslatedDepthSeven
noncomputable section
open scoped BigOperators

theorem card_le_sum_pointwiseConnected_vertex_edge_persistent_at_root
    {V A B : Type*} [Fintype V] [DecidableEq V]
    [DecidableEq A] [DecidableEq B]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (v₀ : V) (X : Finset A) (vertices : A → Finset V)
    (label : A → V → Option B)
    (hroot : ∀ x ∈ X, v₀ ∈ vertices x)
    (hconnected : ∀ x ∈ X,
      (G.induce (↑(vertices x) : Set V)).Connected) :
    X.card ≤
      (∑ v : V, (X.filter fun x => v ∈ vertices x ∧ label x v = none).card) +
      (∑ v : V, ∑ w : V, (X.filter fun x =>
        v ∈ vertices x ∧ w ∈ vertices x ∧ G.Adj v w ∧ label x v ≠ label x w).card) +
      (∑ o ∈ X.image (fun x => label x v₀),
        (X.filter fun x => o ≠ none ∧ ∀ v ∈ vertices x, label x v = o).card) := by
  classical
  have hsub : X.image (fun x => label x v₀) ⊆
      occurringPointwiseLabels X vertices label := by
    intro o ho
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp ho
    exact (mem_occurringPointwiseLabels_iff _ _ _ _).mpr
      ⟨x, hx, v₀, hroot x hx, rfl⟩
  have hsum :
      (∑ o ∈ X.image (fun x => label x v₀),
        (X.filter fun x => o ≠ none ∧ ∀ v ∈ vertices x, label x v = o).card) =
      (∑ o ∈ occurringPointwiseLabels X vertices label,
        (X.filter fun x => o ≠ none ∧ ∀ v ∈ vertices x, label x v = o).card) := by
    apply Finset.sum_subset hsub
    intro o _ho hnot
    apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro x hx
    obtain ⟨hxX, _hne, hlabel⟩ := Finset.mem_filter.mp hx
    exact hnot (Finset.mem_image.mpr ⟨x, hxX, hlabel v₀ (hroot x hxX)⟩)
  rw [hsum]
  exact card_le_sum_pointwiseConnected_vertex_edge_persistent X vertices label hconnected

/-- If every surviving auxiliary vanishes at the point, the empty-label
alternative disappears and only root-persistent and changed-edge points
remain. -/
theorem card_le_sum_pointwiseConnected_edge_persistent_at_root
    {V A B : Type*} [Fintype V] [DecidableEq V]
    [DecidableEq A] [DecidableEq B]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (v₀ : V) (X : Finset A) (vertices : A → Finset V)
    (label : A → V → Option B)
    (hroot : ∀ x ∈ X, v₀ ∈ vertices x)
    (hconnected : ∀ x ∈ X,
      (G.induce (↑(vertices x) : Set V)).Connected)
    (hnonempty : ∀ x ∈ X, ∀ v ∈ vertices x, label x v ≠ none) :
    X.card ≤
      (∑ v : V, ∑ w : V, (X.filter fun x =>
        v ∈ vertices x ∧ w ∈ vertices x ∧ G.Adj v w ∧ label x v ≠ label x w).card) +
      (∑ o ∈ X.image (fun x => label x v₀),
        (X.filter fun x => o ≠ none ∧ ∀ v ∈ vertices x, label x v = o).card) := by
  classical
  have h := card_le_sum_pointwiseConnected_vertex_edge_persistent_at_root
    G v₀ X vertices label hroot hconnected
  have hzero : (∑ v : V,
      (X.filter fun x => v ∈ vertices x ∧ label x v = none).card) = 0 := by
    apply Finset.sum_eq_zero
    intro v _hv
    apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro x hx
    obtain ⟨hxX, hvX, heq⟩ := Finset.mem_filter.mp hx
    exact hnonempty x hxX v hvX heq
  simpa only [hzero, zero_add] using h

end
end TranslatedDepthSeven
