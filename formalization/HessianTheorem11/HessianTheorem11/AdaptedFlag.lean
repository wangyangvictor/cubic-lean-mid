import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic

/-!+# A basis adapted to a pointed two-step flag

For `x ∈ T ≤ L ≤ E` with `x ≠ 0`, extend the singleton `x` successively to
bases of `T`, `L`, and `E`.  After reindexing to `Fin n`, the basis vectors
lying in either subspace span precisely that subspace.
-/

namespace HessianTheorem11

open Module Submodule

noncomputable section

variable {K : Type*} [Field K]

theorem exists_basis_containing_independent_range
    {V ι : Type*} [AddCommGroup V] [Module K V]
    (v : ι → V) (independent : LinearIndependent K v) :
    ∃ (S : Set V) (b : Basis S K V), Set.range v ⊆ Set.range b := by
  refine ⟨_, Basis.extend independent.linearIndepOn_id, ?_⟩
  rw [Basis.range_extend]
  exact independent.linearIndepOn_id.subset_extend _

theorem span_basis_vectors_mem_eq_of_contains_subspace_basis
    {V ι κ : Type*} [AddCommGroup V] [Module K V]
    (b : Basis ι K V) (P : Submodule K V) (c : Basis κ K P)
    (included : Set.range (P.subtype ∘ c) ⊆ Set.range b) :
    span K (b '' {i | b i ∈ P}) = P := by
  apply le_antisymm
  · apply span_le.mpr
    rintro _ ⟨i, hi, rfl⟩
    exact hi
  · have hc : span K (Set.range (P.subtype ∘ c)) = P := by
      rw [Set.range_comp, ← Submodule.map_span, c.span_eq, Submodule.map_subtype_top]
    calc
      P = span K (Set.range (P.subtype ∘ c)) := hc.symm
      _ ≤ span K (b '' {i | b i ∈ P}) := by
        apply span_mono
        rintro _ ⟨i, rfl⟩
        obtain ⟨j, hj⟩ := included ⟨i, rfl⟩
        refine ⟨j, ?_, hj⟩
        change b j ∈ P
        rw [hj]
        exact (c i).property

theorem exists_set_basis_adapted_flag
    {V : Type*} [AddCommGroup V] [Module K V]
    (T L : Submodule K V) (nested : T ≤ L)
    (x : V) (nonzero : x ≠ 0) (memT : x ∈ T) :
    ∃ (S : Set V) (b : Basis S K V) (i₀ : S),
      b i₀ = x ∧ span K (b '' {i | b i ∈ T}) = T ∧
        span K (b '' {i | b i ∈ L}) = L := by
  let xT : T := ⟨x, memT⟩
  have hxT : xT ≠ 0 := by
    intro h
    exact nonzero (congrArg Subtype.val h)
  have independent : LinearIndependent K (fun _ : Unit => xT) :=
    LinearIndependent.of_subsingleton () hxT
  obtain ⟨ST, bT, containsX⟩ :=
    exists_basis_containing_independent_range (fun _ : Unit => xT) independent
  let inclusion : T →ₗ[K] L := Submodule.inclusion nested
  have inclusion_injective : Function.Injective inclusion := Submodule.inclusion_injective _
  have independentT : LinearIndependent K (inclusion ∘ bT) :=
    bT.linearIndependent.map_injOn inclusion inclusion_injective.injOn
  obtain ⟨SL, bL, containsT⟩ :=
    exists_basis_containing_independent_range (inclusion ∘ bT) independentT
  have independentL : LinearIndependent K (L.subtype ∘ bL) :=
    bL.linearIndependent.map_injOn L.subtype Subtype.val_injective.injOn
  obtain ⟨SE, bE, containsL⟩ :=
    exists_basis_containing_independent_range (L.subtype ∘ bL) independentL
  have containsT_in_E : Set.range (T.subtype ∘ bT) ⊆ Set.range bE := by
    rintro _ ⟨i, rfl⟩
    obtain ⟨j, hj⟩ := containsT ⟨i, rfl⟩
    have he := containsL ⟨j, rfl⟩
    simpa only [Function.comp_apply, hj] using he
  obtain ⟨iT, hiT⟩ := containsX ⟨(), rfl⟩
  obtain ⟨iE, hiE⟩ := containsT_in_E ⟨iT, rfl⟩
  refine ⟨SE, bE, iE, ?_, ?_, ?_⟩
  · simpa only [Function.comp_apply, hiT] using hiE
  · exact span_basis_vectors_mem_eq_of_contains_subspace_basis bE T bT containsT_in_E
  · exact span_basis_vectors_mem_eq_of_contains_subspace_basis bE L bL containsL

theorem basis_reindex_mem_image
    {V ι κ : Type*} [AddCommGroup V] [Module K V]
    (b : Basis ι K V) (e : ι ≃ κ) (P : Submodule K V) :
    b.reindex e '' {i | b.reindex e i ∈ P} = b '' {i | b i ∈ P} := by
  ext v
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact ⟨e.symm i, by simpa using hi, by simp⟩
  · rintro ⟨i, hi, rfl⟩
    exact ⟨e i, by simpa using hi, by simp⟩

theorem exists_fin_basis_adapted_flag {n : ℕ}
    (T L : Submodule K (Fin n → K)) (nested : T ≤ L)
    (x : Fin n → K) (nonzero : x ≠ 0) (memT : x ∈ T) :
    ∃ (b : Basis (Fin n) K (Fin n → K)) (i₀ : Fin n),
      b i₀ = x ∧ span K (b '' {i | b i ∈ T}) = T ∧
        span K (b '' {i | b i ∈ L}) = L := by
  obtain ⟨S, b, i₀, radial, tangent, kernel⟩ :=
    exists_set_basis_adapted_flag T L nested x nonzero memT
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

theorem card_basis_indices_mem_submodule
    {V ι : Type*} [AddCommGroup V] [Module K V] [Fintype ι]
    (b : Basis ι K V) (P : Submodule K V)
    [DecidablePred (fun i => b i ∈ P)]
    (spans : span K (b '' {i | b i ∈ P}) = P) :
    (Finset.univ.filter (fun i => b i ∈ P)).card = finrank K P := by
  classical
  have independent : LinearIndependent K (fun i : {i // b i ∈ P} => b i.1) :=
    b.linearIndependent.comp Subtype.val Subtype.val_injective
  have range_eq : Set.range (fun i : {i // b i ∈ P} => b i.1) =
      b '' {i | b i ∈ P} := by
    ext v
    simp
  have dim := finrank_span_eq_card independent
  rw [range_eq, spans] at dim
  simpa only [Fintype.card_subtype] using dim.symm

/-- A finite coordinate basis together with the two blocks of an adapted
flag.  The radial singleton lies in the tangent block, which lies in the
kernel block. -/
structure AdaptedFlagBasis {n : ℕ}
    (T L : Submodule K (Fin n → K)) (x : Fin n → K) where
  basis : Basis (Fin n) K (Fin n → K)
  radial : Fin n
  tangentIndices : Finset (Fin n)
  kernelIndices : Finset (Fin n)
  radial_eq : basis radial = x
  radial_mem : radial ∈ tangentIndices
  indices_nested : tangentIndices ⊆ kernelIndices
  mem_tangent_iff : ∀ i, basis i ∈ T ↔ i ∈ tangentIndices
  mem_kernel_iff : ∀ i, basis i ∈ L ↔ i ∈ kernelIndices
  tangent_card : tangentIndices.card = finrank K T
  kernel_card : kernelIndices.card = finrank K L
  tangent_span : span K (basis '' (tangentIndices : Set (Fin n))) = T
  kernel_span : span K (basis '' (kernelIndices : Set (Fin n))) = L

theorem nonempty_adaptedFlagBasis {n : ℕ}
    (T L : Submodule K (Fin n → K)) (nested : T ≤ L)
    (x : Fin n → K) (nonzero : x ≠ 0) (memT : x ∈ T) :
    Nonempty (AdaptedFlagBasis T L x) := by
  classical
  obtain ⟨b, i₀, radial, tangent, kernel⟩ :=
    exists_fin_basis_adapted_flag T L nested x nonzero memT
  refine ⟨{
    basis := b
    radial := i₀
    tangentIndices := Finset.univ.filter (fun i => b i ∈ T)
    kernelIndices := Finset.univ.filter (fun i => b i ∈ L)
    radial_eq := radial
    radial_mem := ?_
    indices_nested := ?_
    mem_tangent_iff := ?_
    mem_kernel_iff := ?_
    tangent_card := card_basis_indices_mem_submodule b T tangent
    kernel_card := card_basis_indices_mem_submodule b L kernel
    tangent_span := ?_
    kernel_span := ?_
  }⟩
  · simp [radial, memT]
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    exact nested hi
  · intro i
    simp
  · intro i
    simp
  · simpa using tangent
  · simpa using kernel

/-- The chosen adapted basis; all structural properties are exposed as fields. -/
def adaptedFlagBasis {n : ℕ}
    (T L : Submodule K (Fin n → K)) (nested : T ≤ L)
    (x : Fin n → K) (nonzero : x ≠ 0) (memT : x ∈ T) :
    AdaptedFlagBasis T L x :=
  Classical.choice (nonempty_adaptedFlagBasis T L nested x nonzero memT)

end

end HessianTheorem11
