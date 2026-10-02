import TranslatedDepthSeven.PrimeSubsetPrefixGraph

/-!
# The fixed-cardinality reservoir inside the rooted prefix graph

The rooted prefix graph contains every subset of the ambient prime pool of
cardinality at most `k`.  This file identifies its surviving vertices of
cardinality exactly `k` with the existing fixed-cardinality reservoir after
an arbitrary deletion of primes.  Thus the empty prefix is a common root,
the surviving induced graph is connected, and any terminal reservoir member
is literally a terminal vertex of the same graph.
-/

namespace TranslatedDepthSeven.PrimeSubsetPrefix
noncomputable section

@[simp]
theorem mem_survivingVertices_iff
    {P Q : Finset ℕ} {k : ℕ} (v : Vertex P k) :
    v ∈ survivingVertices P Q k ↔ v.1 ⊆ Q := by
  simp [survivingVertices]

@[simp]
theorem mem_survivingVertices_sdiff_iff
    {P bad : Finset ℕ} {k : ℕ} (v : Vertex P k) :
    v ∈ survivingVertices P (P \ bad) k ↔
      ∀ p ∈ v.1, p ∉ bad := by
  rw [mem_survivingVertices_iff]
  constructor
  · intro hv p hp
    exact (Finset.mem_sdiff.mp (hv hp)).2
  · intro hv p hp
    exact Finset.mem_sdiff.mpr
      ⟨(mem_vertices.mp v.2).1 hp, hv p hp⟩

/-- Include a fixed-cardinality subset of the surviving pool as a terminal
vertex of the ambient rooted prefix graph. -/
def terminalPrefixEmbedding
    {P Q : Finset ℕ} {k : ℕ} (hQ : Q ⊆ P) :
    ReservoirVertex Q k ↪ Vertex P k where
  toFun s := ⟨s.1, mem_vertices.mpr
    ⟨s.2.1.trans hQ, s.2.2.le⟩⟩
  inj' s t hst := by
    apply Subtype.ext
    exact congrArg (fun v : Vertex P k => v.1) hst

@[simp]
theorem terminalPrefixEmbedding_val
    {P Q : Finset ℕ} {k : ℕ} (hQ : Q ⊆ P)
    (s : ReservoirVertex Q k) :
    (terminalPrefixEmbedding hQ s).1 = s.1 := rfl

@[simp]
theorem terminalPrefixEmbedding_card
    {P Q : Finset ℕ} {k : ℕ} (hQ : Q ⊆ P)
    (s : ReservoirVertex Q k) :
    (terminalPrefixEmbedding hQ s).1.card = k := s.2.2

@[simp]
theorem terminalPrefixEmbedding_mem_surviving
    {P Q : Finset ℕ} {k : ℕ} (hQ : Q ⊆ P)
    (s : ReservoirVertex Q k) :
    terminalPrefixEmbedding hQ s ∈ survivingVertices P Q k := by
  exact mem_survivingVertices_iff _ |>.mpr s.2.1

@[simp]
theorem terminalPrefixEmbedding_modulus
    {P Q : Finset ℕ} {k : ℕ} (hQ : Q ⊆ P)
    (s : ReservoirVertex Q k) :
    modulus (terminalPrefixEmbedding hQ s) = primeProduct s.1 := rfl

/-- Exact equivalence between the old terminal reservoir and the terminal
layer of the surviving rooted prefix graph. -/
def terminalPrefixEquiv
    {P Q : Finset ℕ} {k : ℕ} (hQ : Q ⊆ P) :
    ReservoirVertex Q k ≃
      {v : Vertex P k //
        v ∈ survivingVertices P Q k ∧ v.1.card = k} where
  toFun s := ⟨terminalPrefixEmbedding hQ s,
    terminalPrefixEmbedding_mem_surviving hQ s,
    terminalPrefixEmbedding_card hQ s⟩
  invFun v := ⟨v.1.1,
    (mem_survivingVertices_iff v.1).mp v.2.1,
    v.2.2⟩
  left_inv s := by
    apply Subtype.ext
    rfl
  right_inv v := by
    apply Subtype.ext
    apply Subtype.ext
    rfl

/-- A terminal modulus supplied by the existing reservoir is the modulus of
a surviving terminal prefix vertex, without changing the underlying prime
set or its product. -/
theorem exists_terminalPrefix_of_mem_modulusReservoir
    {P Q : Finset ℕ} {k q : ℕ} (hQ : Q ⊆ P)
    (hq : q ∈ modulusReservoir Q k) :
    ∃ v : Vertex P k,
      v ∈ survivingVertices P Q k ∧ v.1.card = k ∧ modulus v = q := by
  obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hq
  let t : ReservoirVertex Q k :=
    ⟨s, Finset.mem_powersetCard.mp hs⟩
  exact ⟨terminalPrefixEmbedding hQ t,
    terminalPrefixEmbedding_mem_surviving hQ t,
    terminalPrefixEmbedding_card hQ t,
    terminalPrefixEmbedding_modulus hQ t⟩

/-- If at least `k` primes survive, then the rooted prefix graph has a
surviving terminal vertex. -/
theorem exists_terminalPrefix_of_card_le
    {P Q : Finset ℕ} {k : ℕ} (hQ : Q ⊆ P) (hk : k ≤ Q.card) :
    ∃ v : Vertex P k,
      v ∈ survivingVertices P Q k ∧ v.1.card = k := by
  obtain ⟨s, hs, hcard⟩ := Finset.exists_subset_card_eq hk
  let t : ReservoirVertex Q k := ⟨s, hs, hcard⟩
  exact ⟨terminalPrefixEmbedding hQ t,
    terminalPrefixEmbedding_mem_surviving hQ t,
    terminalPrefixEmbedding_card hQ t⟩

/-- A one-exchange edge in the old fixed-cardinality reservoir becomes a
two-edge path in the rooted prefix graph, through the common subset obtained
by deleting the exchanged prime.  The intermediate vertex still survives
the same prime deletion. -/
theorem terminalPrefixEmbedding_oneExchange_common_neighbor
    {P Q : Finset ℕ} {k : ℕ} (hQ : Q ⊆ P)
    {s t : ReservoirVertex Q k} (hst : OneExchange s.1 t.1) :
    ∃ u : Vertex P k,
      u ∈ survivingVertices P Q k ∧
      (graph P k).Adj u (terminalPrefixEmbedding hQ s) ∧
      (graph P k).Adj u (terminalPrefixEmbedding hQ t) := by
  obtain ⟨p, hp, q, hq, ht⟩ := hst
  have huQ : s.1.erase p ⊆ Q :=
    (Finset.erase_subset _ _).trans s.2.1
  have huCard : (s.1.erase p).card ≤ k := by
    calc
      (s.1.erase p).card ≤ s.1.card := Finset.card_erase_le
      _ = k := s.2.2
  let u : Vertex P k := ⟨s.1.erase p,
    mem_vertices.mpr ⟨huQ.trans hQ, huCard⟩⟩
  refine ⟨u, mem_survivingVertices_iff u |>.mpr huQ, ?_, ?_⟩
  · exact Or.inl ⟨p, Finset.notMem_erase p s.1,
      (Finset.insert_erase hp).symm⟩
  · exact Or.inl ⟨q, by
      intro hmem
      apply hq
      exact Finset.mem_of_mem_erase hmem, ht⟩

/-- The exact common-root package after deleting a point-dependent finite
set of bad primes.  The room hypothesis is used only for the terminal layer;
connectivity and survival of the empty root hold for every deletion. -/
theorem pointwise_deleted_root_connected_and_terminal
    {A : Type*} [DecidableEq A]
    (P : Finset ℕ) (k : ℕ) (X : Finset A)
    (bad : A → Finset ℕ)
    (hroom : ∀ x ∈ X, k ≤ (P \ bad x).card) :
    ∀ x ∈ X,
      root P k ∈ survivingVertices P (P \ bad x) k ∧
      ((graph P k).induce
        (↑(survivingVertices P (P \ bad x) k) : Set (Vertex P k))).Connected ∧
      ∃ v : Vertex P k,
        v ∈ survivingVertices P (P \ bad x) k ∧ v.1.card = k := by
  intro x hx
  exact ⟨root_mem_surviving P (P \ bad x) k,
    surviving_connected P (P \ bad x) k Finset.sdiff_subset,
    exists_terminalPrefix_of_card_le Finset.sdiff_subset (hroom x hx)⟩

end
end TranslatedDepthSeven.PrimeSubsetPrefix
