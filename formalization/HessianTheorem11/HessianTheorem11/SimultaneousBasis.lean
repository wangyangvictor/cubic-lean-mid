import HessianTheorem11.AdaptedFlag
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas

/-!+# A simultaneous basis for two subspaces with a prescribed transverse vector

The two subspaces need not be nested.  A basis of their intersection is first
extended with the prescribed vector to the tangent subspace.  A complement of
the intersection inside the other subspace supplies an independent second
family.  Extending their union gives the ambient coordinate basis.
-/

namespace HessianTheorem11

open Module Submodule

noncomputable section

variable {K : Type*} [Field K]

theorem span_basis_vectors_mem_eq_of_spanning_set
    {V ι : Type*} [AddCommGroup V] [Module K V]
    (b : Basis ι K V) (P : Submodule K V) (S : Set V)
    (spans : span K S = P) (included : S ⊆ Set.range b) :
    span K (b '' {i | b i ∈ P}) = P := by
  apply le_antisymm
  · apply span_le.mpr
    rintro _ ⟨i, hi, rfl⟩
    exact hi
  · calc
      P = span K S := spans.symm
      _ ≤ span K (b '' {i | b i ∈ P}) := by
        apply span_mono
        intro v hv
        obtain ⟨i, rfl⟩ := included hv
        refine ⟨i, ?_, rfl⟩
        change b i ∈ P
        rw [← spans]
        exact subset_span hv

theorem exists_set_basis_simultaneous
    {V : Type*} [AddCommGroup V] [Module K V]
    (T L : Submodule K V) (x : V) (memT : x ∈ T) (notMemL : x ∉ L) :
    ∃ (S : Set V) (b : Basis S K V) (i₀ : S),
      b i₀ = x ∧ span K (b '' {i | b i ∈ T}) = T ∧
        span K (b '' {i | b i ∈ L}) = L := by
  classical
  let U : Submodule K L := T.comap L.subtype
  obtain ⟨C, complement⟩ := U.exists_isCompl
  let bU := Basis.ofVectorSpace K U
  let bC := Basis.ofVectorSpace K C
  let intoT : U →ₗ[K] T :=
    { toFun := fun u => ⟨u.1.1, u.2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have intoT_injective : Function.Injective intoT := by
    intro a b h
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : T => (z : V)) h
  have independentU : LinearIndependent K (intoT ∘ bU) :=
    bU.linearIndependent.map_injOn intoT intoT_injective.injOn
  let xT : T := ⟨x, memT⟩
  have x_outside : xT ∉ span K (Set.range (intoT ∘ bU)) := by
    intro hx
    have hs : span K (Set.range (intoT ∘ bU)) ≤ L.comap T.subtype := by
      apply span_le.mpr
      rintro _ ⟨i, rfl⟩
      exact (bU i).1.2
    exact notMemL (hs hx)
  let start : Option (Basis.ofVectorSpaceIndex K U) → T :=
    fun i => Option.casesOn' i xT (intoT ∘ bU)
  have independentStart : LinearIndependent K start := independentU.option x_outside
  obtain ⟨ST, bT, containsStart⟩ :=
    exists_basis_containing_independent_range start independentStart
  let intoE : C →ₗ[K] V := L.subtype.comp C.subtype
  have intoE_injective : Function.Injective intoE := by
    intro a b h
    apply Subtype.ext
    apply Subtype.ext
    exact h
  have independentT : LinearIndependent K (T.subtype ∘ bT) :=
    bT.linearIndependent.map_injOn T.subtype Subtype.val_injective.injOn
  have independentC : LinearIndependent K (intoE ∘ bC) :=
    bC.linearIndependent.map_injOn intoE intoE_injective.injOn
  have spanT : span K (Set.range (T.subtype ∘ bT)) = T := by
    rw [Set.range_comp, ← Submodule.map_span, bT.span_eq, Submodule.map_subtype_top]
  have spanC : span K (Set.range (intoE ∘ bC)) = C.map L.subtype := by
    rw [Set.range_comp, ← Submodule.map_span, bC.span_eq, Submodule.map_top]
    simp only [intoE, LinearMap.range_comp, Submodule.range_subtype]
  have disjointTC : Disjoint T (C.map L.subtype) := by
    apply Submodule.disjoint_def.mpr
    intro v hvT hvC
    obtain ⟨y, hyC, rfl⟩ := hvC
    have hyU : y ∈ U := hvT
    have hy0 := Submodule.disjoint_def.mp complement.disjoint y hyU hyC
    exact congrArg Subtype.val hy0
  have independentTotal : LinearIndependent K
      (Sum.elim (T.subtype ∘ bT) (intoE ∘ bC)) :=
    independentT.sum_type independentC (by rwa [spanT, spanC])
  obtain ⟨SE, bE, containsTotal⟩ := exists_basis_containing_independent_range
    (Sum.elim (T.subtype ∘ bT) (intoE ∘ bC)) independentTotal
  have containsT : Set.range (T.subtype ∘ bT) ⊆ Set.range bE := by
    rintro _ ⟨i, rfl⟩
    exact containsTotal ⟨Sum.inl i, rfl⟩
  have containsC : Set.range (intoE ∘ bC) ⊆ Set.range bE := by
    rintro _ ⟨i, rfl⟩
    exact containsTotal ⟨Sum.inr i, rfl⟩
  let uE : U →ₗ[K] V := L.subtype.comp U.subtype
  have containsU : Set.range (uE ∘ bU) ⊆ Set.range bE := by
    rintro _ ⟨i, rfl⟩
    obtain ⟨j, hj⟩ := containsStart ⟨some i, rfl⟩
    have ht := containsT ⟨j, rfl⟩
    simpa only [Function.comp_apply, hj] using ht
  have spanU : span K (Set.range (uE ∘ bU)) = U.map L.subtype := by
    rw [Set.range_comp, ← Submodule.map_span, bU.span_eq, Submodule.map_top]
    simp only [uE, LinearMap.range_comp, Submodule.range_subtype]
  have spansL : span K (Set.range (uE ∘ bU) ∪ Set.range (intoE ∘ bC)) = L := by
    rw [Submodule.span_union, spanU, spanC, ← Submodule.map_sup,
      complement.sup_eq_top, Submodule.map_subtype_top]
  obtain ⟨iT, hiT⟩ := containsStart ⟨none, rfl⟩
  obtain ⟨iE, hiE⟩ := containsT ⟨iT, rfl⟩
  refine ⟨SE, bE, iE, ?_, ?_, ?_⟩
  · simpa only [Function.comp_apply, hiT] using hiE
  · exact span_basis_vectors_mem_eq_of_contains_subspace_basis bE T bT containsT
  · exact span_basis_vectors_mem_eq_of_spanning_set bE L _ spansL
      (Set.union_subset containsU containsC)

theorem exists_fin_basis_simultaneous {n : ℕ}
    (T L : Submodule K (Fin n → K)) (x : Fin n → K)
    (memT : x ∈ T) (notMemL : x ∉ L) :
    ∃ (b : Basis (Fin n) K (Fin n → K)) (i₀ : Fin n),
      b i₀ = x ∧ span K (b '' {i | b i ∈ T}) = T ∧
        span K (b '' {i | b i ∈ L}) = L := by
  obtain ⟨S, b, i₀, radial, tangent, kernel⟩ :=
    exists_set_basis_simultaneous T L x memT notMemL
  letI : Finite S := Module.Finite.finite_basis b
  letI : Fintype S := Fintype.ofFinite S
  have cardinality : Fintype.card S = n := by
    rw [← finrank_eq_card_basis b]
    simp
  let e : S ≃ Fin n := (Fintype.equivFin S).trans (finCongr cardinality)
  refine ⟨b.reindex e, e i₀, ?_, ?_, ?_⟩
  · simpa using radial
  · rwa [basis_reindex_mem_image]
  · rwa [basis_reindex_mem_image]

/-- The coordinate data needed for four-block smooth radial weights. -/
structure SimultaneousSubspaceBasis {n : ℕ}
    (T L : Submodule K (Fin n → K)) (x : Fin n → K) where
  basis : Basis (Fin n) K (Fin n → K)
  radial : Fin n
  tangentIndices : Finset (Fin n)
  kernelIndices : Finset (Fin n)
  radial_eq : basis radial = x
  radial_mem_tangent : radial ∈ tangentIndices
  radial_notMem_kernel : radial ∉ kernelIndices
  mem_tangent_iff : ∀ i, basis i ∈ T ↔ i ∈ tangentIndices
  mem_kernel_iff : ∀ i, basis i ∈ L ↔ i ∈ kernelIndices
  tangent_card : tangentIndices.card = finrank K T
  kernel_card : kernelIndices.card = finrank K L
  tangent_span : span K (basis '' (tangentIndices : Set (Fin n))) = T
  kernel_span : span K (basis '' (kernelIndices : Set (Fin n))) = L

theorem nonempty_simultaneousSubspaceBasis {n : ℕ}
    (T L : Submodule K (Fin n → K)) (x : Fin n → K)
    (memT : x ∈ T) (notMemL : x ∉ L) :
    Nonempty (SimultaneousSubspaceBasis T L x) := by
  classical
  obtain ⟨b, i₀, radial, tangent, kernel⟩ :=
    exists_fin_basis_simultaneous T L x memT notMemL
  refine ⟨{
    basis := b
    radial := i₀
    tangentIndices := Finset.univ.filter (fun i => b i ∈ T)
    kernelIndices := Finset.univ.filter (fun i => b i ∈ L)
    radial_eq := radial
    radial_mem_tangent := ?_
    radial_notMem_kernel := ?_
    mem_tangent_iff := ?_
    mem_kernel_iff := ?_
    tangent_card := card_basis_indices_mem_submodule b T tangent
    kernel_card := card_basis_indices_mem_submodule b L kernel
    tangent_span := ?_
    kernel_span := ?_
  }⟩
  · simp [radial, memT]
  · simp [radial, notMemL]
  · intro i; simp
  · intro i; simp
  · simpa using tangent
  · simpa using kernel

def simultaneousSubspaceBasis {n : ℕ}
    (T L : Submodule K (Fin n → K)) (x : Fin n → K)
    (memT : x ∈ T) (notMemL : x ∉ L) :
    SimultaneousSubspaceBasis T L x :=
  Classical.choice (nonempty_simultaneousSubspaceBasis T L x memT notMemL)

end

end HessianTheorem11
