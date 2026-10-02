import TranslatedDepthSeven.ReservoirGraph

/-!
# The reservoir graph on the moduli themselves

For a finite set `P` of primes, multiplication identifies the `k`-element
subsets of `P` with the natural numbers in `modulusReservoir P k`.  This file
makes that identification an equivalence and transports the one-exchange
graph to the literal moduli.  Thus no implicit choice of a factor set remains
in statements about adjacency.
-/

namespace TranslatedDepthSeven

noncomputable section

/-- A modulus belonging to the fixed-cardinality reservoir. -/
def ReservoirModulus (P : Finset ℕ) (k : ℕ) :=
  ↑(modulusReservoir P k)

theorem primeFactors_spec_of_mem_modulusReservoir
    {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) {k q : ℕ}
    (hq : q ∈ modulusReservoir P k) :
    q.primeFactors ⊆ P ∧ q.primeFactors.card = k ∧
      primeProduct q.primeFactors = q := by
  obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hq
  have hs' := Finset.mem_powersetCard.mp hs
  have hprime : ∀ p ∈ s, p.Prime := fun p hp ↦ hP p (hs'.1 hp)
  have hfactors : (primeProduct s).primeFactors = s :=
    primeFactors_primeProduct hprime
  rw [hfactors]
  exact ⟨hs'.1, hs'.2, rfl⟩

/-- Multiplication is a literal equivalence from the fixed-cardinality prime
subsets to the resulting integer moduli.  Its inverse sends a modulus to its
set of prime factors. -/
def reservoirVertexModulusEquiv
    (P : Finset ℕ) (k : ℕ) (hP : ∀ p ∈ P, p.Prime) :
    ReservoirVertex P k ≃ ReservoirModulus P k where
  toFun s := ⟨primeProduct s.1, Finset.mem_image.mpr
    ⟨s.1, Finset.mem_powersetCard.mpr s.2, rfl⟩⟩
  invFun q := ⟨q.1.primeFactors,
    (primeFactors_spec_of_mem_modulusReservoir hP q.2).1,
    (primeFactors_spec_of_mem_modulusReservoir hP q.2).2.1⟩
  left_inv s := by
    apply Subtype.ext
    exact primeFactors_primeProduct (fun p hp ↦ hP p (s.2.1 hp))
  right_inv q := by
    apply Subtype.ext
    exact (primeFactors_spec_of_mem_modulusReservoir hP q.2).2.2

@[simp]
theorem reservoirVertexModulusEquiv_apply_val
    {P : Finset ℕ} {k : ℕ} (hP : ∀ p ∈ P, p.Prime)
    (s : ReservoirVertex P k) :
    (reservoirVertexModulusEquiv P k hP s).1 = primeProduct s.1 := rfl

@[simp]
theorem reservoirVertexModulusEquiv_symm_apply_val
    {P : Finset ℕ} {k : ℕ} (hP : ∀ p ∈ P, p.Prime)
    (q : ReservoirModulus P k) :
    ((reservoirVertexModulusEquiv P k hP).symm q).1 = q.1.primeFactors := rfl

/-- The simple graph on the integer moduli in the reservoir: two moduli are
adjacent exactly when their (unique) prime-factor sets differ by one
exchange. -/
def modulusReservoirGraph
    (P : Finset ℕ) (k : ℕ) (hP : ∀ p ∈ P, p.Prime) :
    SimpleGraph (ReservoirModulus P k) where
  Adj q r := OneExchange q.1.primeFactors r.1.primeFactors
  symm q r hqr := oneExchange_symm_of_card_eq
    ((primeFactors_spec_of_mem_modulusReservoir hP q.2).2.1.trans
      (primeFactors_spec_of_mem_modulusReservoir hP r.2).2.1.symm) hqr
  loopless q := oneExchange_irrefl q.1.primeFactors

theorem modulusReservoirGraph_adj_iff
    {P : Finset ℕ} {k : ℕ} (hP : ∀ p ∈ P, p.Prime)
    {q r : ReservoirModulus P k} :
    (modulusReservoirGraph P k hP).Adj q r ↔
      OneExchange q.1.primeFactors r.1.primeFactors := Iff.rfl

/-- Multiplication is an isomorphism from the subset graph to the literal
modulus graph. -/
def reservoirGraphModulusIso
    (P : Finset ℕ) (k : ℕ) (hP : ∀ p ∈ P, p.Prime) :
    reservoirGraph P k ≃g modulusReservoirGraph P k hP where
  toEquiv := reservoirVertexModulusEquiv P k hP
  map_rel_iff' := by
    intro s t
    change OneExchange (primeProduct s.1).primeFactors
        (primeProduct t.1).primeFactors ↔ OneExchange s.1 t.1
    rw [primeFactors_primeProduct (fun p hp ↦ hP p (s.2.1 hp)),
      primeFactors_primeProduct (fun p hp ↦ hP p (t.2.1 hp))]

/-- If `P` contains at least `k` primes, the graph on the integer moduli is
connected. -/
theorem modulusReservoirGraph_connected
    {P : Finset ℕ} {k : ℕ} (hP : ∀ p ∈ P, p.Prime)
    (hkP : k ≤ P.card) :
    (modulusReservoirGraph P k hP).Connected := by
  exact (reservoirGraph_connected hkP).map
    (reservoirGraphModulusIso P k hP).toHom
    (reservoirGraphModulusIso P k hP).toEquiv.surjective

/-- Exact cardinality of the literal finite type of reservoir moduli. -/
theorem card_reservoirModulus
    {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) (k : ℕ) :
    Fintype.card (ReservoirModulus P k) = Nat.choose P.card k := by
  rw [Fintype.card_coe]
  exact card_modulusReservoir_of_primes hP k

/-- Directed adjacent pairs of literal integer moduli. -/
def modulusReservoirDirectedEdges
    (P : Finset ℕ) (k : ℕ) (hP : ∀ p ∈ P, p.Prime) :
    Finset (ReservoirModulus P k × ReservoirModulus P k) := by
  classical
  exact Finset.univ.filter fun qr ↦
    (modulusReservoirGraph P k hP).Adj qr.1 qr.2

theorem card_modulusReservoirDirectedEdges_le_card_sq
    (P : Finset ℕ) (k : ℕ) (hP : ∀ p ∈ P, p.Prime) :
    (modulusReservoirDirectedEdges P k hP).card ≤
      (Nat.choose P.card k) ^ 2 := by
  classical
  have hsub : modulusReservoirDirectedEdges P k hP ⊆
      (Finset.univ : Finset (ReservoirModulus P k × ReservoirModulus P k)) :=
    Finset.filter_subset _ _
  have hcard := Finset.card_le_card hsub
  simpa [modulusReservoirDirectedEdges, Fintype.card_prod,
    card_reservoirModulus hP k, pow_two] using hcard

theorem card_modulusReservoirDirectedEdges_le_four_pow
    (P : Finset ℕ) (k : ℕ) (hP : ∀ p ∈ P, p.Prime) :
    (modulusReservoirDirectedEdges P k hP).card ≤ 4 ^ P.card := by
  calc
    (modulusReservoirDirectedEdges P k hP).card ≤
        (Nat.choose P.card k) ^ 2 :=
      card_modulusReservoirDirectedEdges_le_card_sq P k hP
    _ ≤ (2 ^ P.card) ^ 2 := by
      exact pow_le_pow_left' (Nat.choose_le_two_pow P.card k) 2
    _ = 4 ^ P.card := by
      rw [← pow_mul, show P.card * 2 = 2 * P.card by omega, pow_mul]
      norm_num

/-- A subpower-ready bound for the total number of literal moduli and
directed adjacent pairs. -/
theorem card_moduli_add_directedEdges_le_two_mul_four_pow
    (P : Finset ℕ) (k : ℕ) (hP : ∀ p ∈ P, p.Prime) :
    Fintype.card (ReservoirModulus P k) +
        (modulusReservoirDirectedEdges P k hP).card ≤
      2 * 4 ^ P.card := by
  have hv : Fintype.card (ReservoirModulus P k) ≤ 2 ^ P.card := by
    rw [card_reservoirModulus hP k]
    exact Nat.choose_le_two_pow P.card k
  have hv' : 2 ^ P.card ≤ 4 ^ P.card :=
    Nat.pow_le_pow_left (by norm_num) P.card
  have he := card_modulusReservoirDirectedEdges_le_four_pow P k hP
  omega

end

end TranslatedDepthSeven
