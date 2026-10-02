import TranslatedDepthSeven.BertrandReservoir
import TranslatedDepthSeven.StaticComparison

/-!
# The literal one-exchange graph

The manuscript joins two fixed-cardinality prime sets when one prime is
replaced by another.  This file makes that graph explicit.  In particular,
it proves symmetry, connectedness after passage to any surviving prime set,
and a finite directed-edge bound.  No prime-density or geometric hypothesis
occurs here.
-/

namespace TranslatedDepthSeven

noncomputable section

/-- A one-element exchange cannot return the original finite set. -/
theorem oneExchange_irrefl (s : Finset ℕ) : ¬OneExchange s s := by
  rintro ⟨p, hp, q, hq, hs⟩
  apply hq
  rw [hs]
  exact Finset.mem_insert_self q (s.erase p)

/-- On equal-cardinality finite sets, the one-exchange relation is symmetric. -/
theorem oneExchange_symm_of_card_eq {s t : Finset ℕ}
    (hcard : s.card = t.card) (hst : OneExchange s t) : OneExchange t s := by
  obtain ⟨p, hp, q, hq, rfl⟩ := hst
  have hpq : p ≠ q := fun hpq ↦ hq (hpq ▸ hp)
  refine ⟨q, Finset.mem_insert_self _ _, p, ?_, ?_⟩
  · simp [hpq, hp]
  · ext x
    simp only [Finset.mem_insert, Finset.mem_erase]
    by_cases hxs : x ∈ s <;>
      by_cases hxp : x = p <;>
      by_cases hxq : x = q <;>
      simp_all

/-- The vertices of the reservoir graph are literally the `k`-element
subsets of the surviving prime set `u`. -/
def ReservoirVertex (u : Finset ℕ) (k : ℕ) :=
  {s : Finset ℕ // s ⊆ u ∧ s.card = k}

/-- The simple graph whose edges are one-prime exchanges. -/
def reservoirGraph (u : Finset ℕ) (k : ℕ) :
    SimpleGraph (ReservoirVertex u k) where
  Adj s t := OneExchange s.1 t.1
  symm s t hst := oneExchange_symm_of_card_eq
    (s.2.2.trans t.2.2.symm) hst
  loopless s := oneExchange_irrefl s.1

/-- The one-exchange graph is preconnected, including the empty-vertex case. -/
theorem reservoirGraph_preconnected (u : Finset ℕ) (k : ℕ) :
    (reservoirGraph u k).Preconnected := by
  intro s t
  rw [SimpleGraph.reachable_iff_reflTransGen]
  induction hn : (s.1 \ t.1).card using Nat.strong_induction_on generalizing s with
  | h n ih =>
      by_cases hst : s = t
      · subst s
        exact Relation.ReflTransGen.refl
      · have hvals : s.1 ≠ t.1 := fun h ↦ hst (Subtype.ext h)
        obtain ⟨s', hs', hcard', hex, hdec⟩ :=
          exists_oneExchange_toward s.2.1 t.2.1
            (s.2.2.trans t.2.2.symm) hvals
        let v' : ReservoirVertex u k :=
          ⟨s', hs', hcard'.trans s.2.2⟩
        have hadj : (reservoirGraph u k).Adj s v' := hex
        have htail : Relation.ReflTransGen (reservoirGraph u k).Adj v' t := by
          apply ih (s' \ t.1).card
          · simpa [hn] using hdec
          · rfl
        exact (Relation.ReflTransGen.single hadj).trans htail

/-- If at least `k` primes survive, the literal reservoir graph is connected. -/
theorem reservoirGraph_connected {u : Finset ℕ} {k : ℕ}
    (hku : k ≤ u.card) : (reservoirGraph u k).Connected := by
  obtain ⟨s, hs, hcard⟩ := Finset.exists_subset_card_eq hku
  let v : ReservoirVertex u k := ⟨s, hs, hcard⟩
  exact
    { preconnected := reservoirGraph_preconnected u k
      nonempty := ⟨v⟩ }

/-- The static label trichotomy now applies directly to the finite reservoir
graph, rather than to an assumed connected relation. -/
theorem reservoir_label_trichotomy {u : Finset ℕ} {k : ℕ}
    (hku : k ≤ u.card) {α : Type*}
    (label : ReservoirVertex u k → Option α) :
    (∃ v, label v = none) ∨
      (∃ v w, (reservoirGraph u k).Adj v w ∧ label v ≠ label w) ∨
      ∃ a, ∀ v, label v = some a :=
  StaticComparison.connected_option_labels
    (reservoirGraph_connected hku) label

/-- Directed one-exchange pairs inside the fixed-cardinality family.  The
direction is irrelevant to connectivity, but makes the finite count literal. -/
def reservoirDirectedEdges (u : Finset ℕ) (k : ℕ) :
    Finset (Finset ℕ × Finset ℕ) := by
  classical
  exact ((u.powersetCard k).product (u.powersetCard k)).filter
    fun st ↦ OneExchange st.1 st.2

theorem card_reservoirDirectedEdges_le_choose_sq (u : Finset ℕ) (k : ℕ) :
    (reservoirDirectedEdges u k).card ≤ (Nat.choose u.card k) ^ 2 := by
  have hsub : reservoirDirectedEdges u k ⊆
      (u.powersetCard k).product (u.powersetCard k) :=
    by
      classical
      exact Finset.filter_subset _ _
  have hcard := Finset.card_le_card hsub
  simpa [reservoirDirectedEdges, Finset.card_product, pow_two] using hcard

/-- A crude edge bound sufficient for every subpower estimate in the
manuscript. -/
theorem card_reservoirDirectedEdges_le_four_pow (u : Finset ℕ) (k : ℕ) :
    (reservoirDirectedEdges u k).card ≤ 4 ^ u.card := by
  calc
    (reservoirDirectedEdges u k).card ≤ (Nat.choose u.card k) ^ 2 :=
      card_reservoirDirectedEdges_le_choose_sq u k
    _ ≤ (2 ^ u.card) ^ 2 := by
      exact pow_le_pow_left' (Nat.choose_le_two_pow u.card k) 2
    _ = 4 ^ u.card := by
      rw [← pow_mul, show u.card * 2 = 2 * u.card by omega, pow_mul]
      norm_num

/-- The total number of fixed-cardinality vertices and directed exchange
edges is bounded by twice `4^|u|`.  This deliberately crude form is convenient
for the subsequent subpower absorption. -/
theorem card_vertices_add_directedEdges_le_two_mul_four_pow
    (u : Finset ℕ) (k : ℕ) :
    (u.powersetCard k).card + (reservoirDirectedEdges u k).card ≤
      2 * 4 ^ u.card := by
  have hv0 : (u.powersetCard k).card = Nat.choose u.card k :=
    Finset.card_powersetCard k u
  have hv1 : (u.powersetCard k).card ≤ 2 ^ u.card := by
    rw [hv0]
    exact Nat.choose_le_two_pow u.card k
  have hv2 : 2 ^ u.card ≤ 4 ^ u.card :=
    Nat.pow_le_pow_left (by norm_num) u.card
  have he := card_reservoirDirectedEdges_le_four_pow u k
  omega

end

end TranslatedDepthSeven
