import TranslatedDepthSeven.ReservoirGraph
import TranslatedDepthSeven.PointwiseConnectedComponentPartition

/-! Prime-product prefixes of every length up to a fixed depth. Including
the empty prefix provides one common root (modulus one) after any deletion
of bad primes. This is the rooted graph needed to keep persistent curves
inside the single initial auxiliary cut. -/

namespace TranslatedDepthSeven.PrimeSubsetPrefix
noncomputable section

def vertices (P : Finset ℕ) (k : ℕ) : Finset (Finset ℕ) :=
  P.powerset.filter (fun s => s.card ≤ k)

abbrev Vertex (P : Finset ℕ) (k : ℕ) := ↑(vertices P k)

theorem mem_vertices {P s : Finset ℕ} {k : ℕ} :
    s ∈ vertices P k ↔ s ⊆ P ∧ s.card ≤ k := by
  simp [vertices]

def root (P : Finset ℕ) (k : ℕ) : Vertex P k :=
  ⟨∅, mem_vertices.mpr ⟨Finset.empty_subset _, by simp⟩⟩

def OneInsertion (s t : Finset ℕ) : Prop :=
  ∃ p, p ∉ s ∧ t = insert p s

theorem oneInsertion_irrefl (s : Finset ℕ) : ¬ OneInsertion s s := by
  rintro ⟨p, hp, heq⟩
  apply hp
  rw [heq]
  exact Finset.mem_insert_self _ _

def graph (P : Finset ℕ) (k : ℕ) : SimpleGraph (Vertex P k) where
  Adj s t := OneInsertion s.1 t.1 ∨ OneInsertion t.1 s.1
  symm _ _ := Or.symm
  loopless s := by
    rintro (h | h) <;> exact oneInsertion_irrefl s.1 h

/-- Every prefix is reachable from the empty prefix by adjoining its own
primes, never exceeding the final depth. -/
theorem root_reachable (P : Finset ℕ) (k : ℕ) (v : Vertex P k) :
    (graph P k).Reachable (root P k) v := by
  have hreach : ∀ s : Finset ℕ, ∀ hs : s ∈ vertices P k,
      (graph P k).Reachable (root P k) ⟨s, hs⟩ := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro hs
      exact SimpleGraph.Reachable.refl _
    | @insert p s hp ih =>
      intro hs
      have hspec := mem_vertices.mp hs
      have hs' : s ∈ vertices P k := mem_vertices.mpr
        ⟨Finset.Subset.trans (Finset.subset_insert _ _) hspec.1,
          (Finset.card_le_card (Finset.subset_insert p s)).trans hspec.2⟩
      have hadj : (graph P k).Adj ⟨s, hs'⟩ ⟨insert p s, hs⟩ :=
        Or.inl ⟨p, hp, rfl⟩
      exact (ih hs').trans hadj.reachable
  exact hreach v.1 v.2

theorem connected (P : Finset ℕ) (k : ℕ) : (graph P k).Connected := by
  rw [SimpleGraph.connected_iff_exists_forall_reachable]
  exact ⟨root P k, root_reachable P k⟩

/-- Deleting any primes leaves a connected induced graph with the same
empty root. No cardinal lower bound is needed for this connectivity fact. -/
theorem induced_surviving_connected (P Q : Finset ℕ) (k : ℕ) (hQ : Q ⊆ P) :
    ((graph P k).induce {v : Vertex P k | v.1 ⊆ Q}).Connected := by
  let f : graph Q k →g (graph P k).induce {v : Vertex P k | v.1 ⊆ Q} :=
    { toFun := fun v => ⟨⟨v.1, mem_vertices.mpr
        ⟨(mem_vertices.mp v.2).1.trans hQ, (mem_vertices.mp v.2).2⟩⟩,
          (mem_vertices.mp v.2).1⟩
      map_rel' := fun h => h }
  have hf : Function.Surjective f := by
    rintro ⟨v, hv⟩
    refine ⟨⟨v.1, mem_vertices.mpr ⟨hv, (mem_vertices.mp v.2).2⟩⟩, ?_⟩
    rfl
  exact (connected Q k).map f hf

def survivingVertices (P Q : Finset ℕ) (k : ℕ) : Finset (Vertex P k) :=
  Finset.univ.filter (fun v => v.1 ⊆ Q)

theorem root_mem_surviving (P Q : Finset ℕ) (k : ℕ) :
    root P k ∈ survivingVertices P Q k := by
  simp [survivingVertices, root]

theorem surviving_connected (P Q : Finset ℕ) (k : ℕ) (hQ : Q ⊆ P) :
    ((graph P k).induce (↑(survivingVertices P Q k) : Set (Vertex P k))).Connected := by
  have heq : (↑(survivingVertices P Q k) : Set (Vertex P k)) =
      {v : Vertex P k | v.1 ⊆ Q} := by
    ext v
    simp [survivingVertices]
  rw [heq]
  exact induced_surviving_connected P Q k hQ

theorem card_vertices_le_two_pow (P : Finset ℕ) (k : ℕ) :
    Fintype.card (Vertex P k) ≤ 2 ^ P.card := by
  rw [Fintype.card_coe]
  exact (Finset.card_filter_le _ _).trans_eq (Finset.card_powerset P)

def modulus {P : Finset ℕ} {k : ℕ} (v : Vertex P k) : ℕ := primeProduct v.1

@[simp] theorem modulus_root (P : Finset ℕ) (k : ℕ) :
    modulus (root P k) = 1 := by simp [modulus, root, primeProduct]

/-- A prefix edge changes the modulus by exactly one available prime;
its least common multiple is the larger of the two moduli. -/
theorem adjacent_modulus_factor {P : Finset ℕ} {k : ℕ} {v w : Vertex P k}
    (hvw : (graph P k).Adj v w) :
    ∃ p ∈ P,
      (modulus w = p * modulus v ∧ Nat.lcm (modulus v) (modulus w) = modulus w) ∨
      (modulus v = p * modulus w ∧ Nat.lcm (modulus v) (modulus w) = modulus v) := by
  have hstep {a b : Vertex P k} (hab : OneInsertion a.1 b.1) :
      ∃ p ∈ P, modulus b = p * modulus a := by
    obtain ⟨p, hp, hb⟩ := hab
    refine ⟨p, (mem_vertices.mp b.2).1 ?_, ?_⟩
    · rw [hb]
      exact Finset.mem_insert_self _ _
    · simp only [modulus, primeProduct, hb, Finset.prod_insert hp]
  rcases hvw with h | h
  · obtain ⟨p, hp, heq⟩ := hstep h
    refine ⟨p, hp, Or.inl ⟨heq, ?_⟩⟩
    apply Nat.lcm_eq_right
    rw [heq]
    exact Nat.dvd_mul_left _ _
  · obtain ⟨p, hp, heq⟩ := hstep h
    refine ⟨p, hp, Or.inr ⟨heq, ?_⟩⟩
    apply Nat.lcm_eq_left
    rw [heq]
    exact Nat.dvd_mul_left _ _

end
end TranslatedDepthSeven.PrimeSubsetPrefix
