import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Dual.Defs

/-!
# A complementary basis and its dual functionals

An independent finite family extends to a basis. The remaining coordinate
functionals vanish on that family and pair as the identity matrix with the
complementary vectors. The number of complementary vectors is exactly the
ambient dimension minus the original family's size, including the empty
and full-basis cases.
-/

namespace TranslatedDepthSeven

noncomputable section
open Module

universe u v

variable {K : Type u} [Field K] {V : Type v} [AddCommGroup V] [Module K V]

theorem basis_sumExtend_apply_inl {ι : Type*} {a : ι → V}
    (ha : LinearIndependent K a) (i : ι) :
    Basis.sumExtend ha (Sum.inl i) = a i := by
  classical
  simp only [Basis.sumExtend, Basis.reindex_apply, Basis.extend_apply_self]
  rfl

/-- The complementary index has the exact finite dimension difference. -/
theorem exists_basis_finSum_extending_independent_family
    [FiniteDimensional K V] {r : ℕ} (a : Fin r → V)
    (ha : LinearIndependent K a) :
    ∃ b : Basis (Fin r ⊕ Fin (Module.finrank K V - r)) K V,
      ∀ i : Fin r, b (Sum.inl i) = a i := by
  classical
  let J := Basis.sumExtendIndex ha
  let b := Basis.sumExtend ha
  letI : Finite (Fin r ⊕ J) := b.linearIndependent.finite
  letI : Finite J := Finite.of_injective
    (Sum.inr : J → Fin r ⊕ J) Sum.inr_injective
  letI : Fintype J := Fintype.ofFinite J
  have hcount : r + Fintype.card J = Module.finrank K V := by
    simpa using (Module.finrank_eq_card_basis b).symm
  have hJ : Fintype.card J = Module.finrank K V - r := by omega
  let e := Fintype.equivFinOfCardEq hJ
  refine ⟨b.reindex (Equiv.sumCongr (Equiv.refl (Fin r)) e), ?_⟩
  intro i
  simpa [Basis.reindex_apply, b] using basis_sumExtend_apply_inl ha i

/-- The exact complementary vectors and dual linear functionals. No
choice of coordinates on the original vector space is required. -/
theorem exists_complementary_basis_and_dual_functionals
    [FiniteDimensional K V] {r : ℕ} (a : Fin r → V)
    (ha : LinearIndependent K a) :
    ∃ (b : Basis (Fin r ⊕ Fin (Module.finrank K V - r)) K V)
      (ell : Fin (Module.finrank K V - r) → Module.Dual K V),
      (∀ i : Fin r, b (Sum.inl i) = a i) ∧
      (∀ j i, ell j (a i) = 0) ∧
      (∀ i j, ell i (b (Sum.inr j)) = if i = j then 1 else 0) := by
  classical
  obtain ⟨b, hb⟩ := exists_basis_finSum_extending_independent_family a ha
  refine ⟨b, fun j ↦ b.coord (Sum.inr j), hb, ?_, ?_⟩
  · intro j i
    rw [← hb i]
    simp [Basis.coord_apply]
  · intro i j
    simp [Basis.coord_apply, Finsupp.single_apply, eq_comm]

end
end TranslatedDepthSeven
