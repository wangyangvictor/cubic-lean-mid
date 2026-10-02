import TranslatedDepthSeven.FiniteAlgebraPointCount
import Mathlib.LinearAlgebra.TensorProduct.Basis

/-!
# Points in a fibre of an explicit finite module

Let `B → A` be a commutative algebra with an explicit `B`-basis indexed by
`Fin D`, and fix a map `B → K` to a finite field.  Base change transports
that basis to a `K`-basis of `K ⊗[B] A`, so the scalar fibre has dimension
exactly `D`.  Dedekind independence then bounds the `B`-algebra maps
`A →ₐ[B] K`, i.e. the points above the fixed base point, by `D`.

The basis form gives an equality.  The finite-spanning-family form below is
the one used directly after module-finite Noether normalization; it removes
any need for generic freeness in residue-fibre counting.  No geometric or
effectivity hypothesis occurs in this file.
-/

namespace TranslatedDepthSeven

noncomputable section

open scoped TensorProduct

universe u v w

/-- An explicit rank-`D` basis remains a rank-`D` basis after arbitrary
specialization of the base ring to a field. -/
theorem finrank_scalarFibre_eq_of_basis_fin
    (B : Type u) (K : Type v) (A : Type w) (D : ℕ)
    [CommRing B] [Field K] [CommRing A]
    [Algebra B K] [Algebra B A]
    (b : Module.Basis (Fin D) B A) :
    Module.finrank K (K ⊗[B] A) = D := by
  rw [Module.finrank_eq_card_basis (b.baseChange K)]
  exact Fintype.card_fin D

/-- More generally, a basis indexed by a finite type gives the corresponding
cardinality as the dimension of every scalar fibre. -/
theorem finrank_scalarFibre_eq_card_of_basis
    (B : Type u) (K : Type v) (A : Type w) (ι : Type*)
    [CommRing B] [Field K] [CommRing A]
    [Algebra B K] [Algebra B A] [Fintype ι]
    (b : Module.Basis ι B A) :
    Module.finrank K (K ⊗[B] A) = Fintype.card ι := by
  rw [Module.finrank_eq_card_basis (b.baseChange K)]

/-- The points of `Spec A` above one fixed `K`-valued point of `Spec B` are
at most the rank of an explicit finite free presentation `B → A`.

The chosen algebra structure `[Algebra B K]` is the fixed base point, and
`A →ₐ[B] K` is exactly its fibre under restriction of points. -/
theorem natCard_algHom_over_base_le_of_basis_fin
    (B : Type u) (K : Type v) (A : Type w) (D : ℕ)
    [CommRing B] [Field K] [Finite K] [CommRing A]
    [Algebra B K] [Algebra B A]
    (b : Module.Basis (Fin D) B A) :
    Nat.card (A →ₐ[B] K) ≤ D := by
  letI : Module.Finite B A := Module.Finite.of_basis b
  calc
    Nat.card (A →ₐ[B] K) ≤ Module.finrank K (K ⊗[B] A) :=
      natCard_algHom_over_base_le_baseChange_finrank B K A
    _ = D := finrank_scalarFibre_eq_of_basis_fin B K A D b

/-- Finite-index version of
`natCard_algHom_over_base_le_of_basis_fin`. -/
theorem natCard_algHom_over_base_le_card_of_basis
    (B : Type u) (K : Type v) (A : Type w) (ι : Type*)
    [CommRing B] [Field K] [Finite K] [CommRing A]
    [Algebra B K] [Algebra B A] [Fintype ι]
    (b : Module.Basis ι B A) :
    Nat.card (A →ₐ[B] K) ≤ Fintype.card ι := by
  letI : Module.Finite B A := Module.Finite.of_basis b
  calc
    Nat.card (A →ₐ[B] K) ≤ Module.finrank K (K ⊗[B] A) :=
      natCard_algHom_over_base_le_baseChange_finrank B K A
    _ = Fintype.card ι := finrank_scalarFibre_eq_card_of_basis B K A ι b

/-- A displayed finite spanning family remains spanning after arbitrary
field specialization.  Consequently the scalar fibre has dimension at most
the size of that family.  Unlike the basis theorem, no freeness hypothesis
is used. -/
theorem finrank_scalarFibre_le_of_span_fin
    (B : Type u) (K : Type v) (A : Type w) (D : ℕ)
    [CommRing B] [Field K] [CommRing A]
    [Algebra B K] [Algebra B A]
    (s : Fin D → A)
    (hs : Submodule.span B (Set.range s) = ⊤) :
    Module.finrank K (K ⊗[B] A) ≤ D := by
  have hbase :
      (Submodule.span B (Set.range s)).baseChange K =
        (⊤ : Submodule B A).baseChange K :=
    congrArg (fun p : Submodule B A ↦ p.baseChange K) hs
  have hsK :
      Submodule.span K
        (Set.range (fun i : Fin D ↦ (1 : K) ⊗ₜ[B] s i)) = ⊤ := by
    rw [Submodule.baseChange_span, Submodule.baseChange_top] at hbase
    have himage :
        (TensorProduct.mk B K A 1) '' Set.range s =
          Set.range (fun i : Fin D ↦ (1 : K) ⊗ₜ[B] s i) := by
      ext x
      constructor
      · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
        exact ⟨i, rfl⟩
      · rintro ⟨i, rfl⟩
        exact ⟨s i, ⟨i, rfl⟩, rfl⟩
    rw [himage] at hbase
    exact hbase
  simpa using finrank_le_of_span_eq_top hsK

/-- A finite spanning family of size `D` bounds the number of points above
one fixed finite-field point of the normalization base by `D`. -/
theorem natCard_algHom_over_base_le_of_span_fin
    (B : Type u) (K : Type v) (A : Type w) (D : ℕ)
    [CommRing B] [Field K] [Finite K] [CommRing A]
    [Algebra B K] [Algebra B A]
    (s : Fin D → A)
    (hs : Submodule.span B (Set.range s) = ⊤) :
    Nat.card (A →ₐ[B] K) ≤ D := by
  letI : Module.Finite B A := Module.finite_def.mpr <|
    Submodule.fg_iff_exists_fin_generating_family.mpr ⟨D, s, hs⟩
  exact (natCard_algHom_over_base_le_baseChange_finrank B K A).trans
    (finrank_scalarFibre_le_of_span_fin B K A D s hs)

/-- Module-finiteness supplies one integer `D`, chosen before the residue
field, which bounds every finite-field fibre of restriction of points. -/
theorem exists_uniform_natCard_algHom_over_base_le_of_moduleFinite
    (B : Type u) (A : Type w)
    [CommRing B] [CommRing A] [Algebra B A] [Module.Finite B A] :
    ∃ D : ℕ, ∀ (K : Type v), ∀ [Field K] [Finite K] [Algebra B K],
      Nat.card (A →ₐ[B] K) ≤ D := by
  obtain ⟨D, s, hs⟩ := Module.Finite.exists_fin (R := B) (M := A)
  exact ⟨D, fun K _ _ _ ↦ natCard_algHom_over_base_le_of_span_fin B K A D s hs⟩

end

end TranslatedDepthSeven
