import HessianTheorem11.GradedCubic

/-! Explicit bijective coordinates for a tangent hyperplane partitioned
into a radial singleton and its remaining tangent coordinates. -/
noncomputable section
namespace HessianTheorem11
open MvPolynomial GradedCubic
variable {K : Type*} [Field K] {n r s : ℕ}

structure GradedIndexCoordinates (T : Finset (Fin n)) (c : Fin n) (r s : ℕ) where
  normal : Fin r ≃ (↑Tᶜ : Type)
  tangent : Fin s ≃ (↑(T.erase c) : Type)
  equiv : GradedCubic.Index r s ≃ Fin n
  normal_apply : ∀ i, equiv (Sum.inl i) = (normal i : Fin n)
  tangent_apply : ∀ i, equiv (GradedCubic.tangent i) = (tangent i : Fin n)
  radial_apply : equiv GradedCubic.radial = c

namespace GradedIndexCoordinates

/-- Assemble the three disjoint coordinate blocks; bijectivity is proved
from the actual finset partition. -/
theorem exists_coordinates (T : Finset (Fin n)) (c : Fin n) (hc : c ∈ T)
    (hN : Tᶜ.card = r) (hA : (T.erase c).card = s) :
    Nonempty (GradedIndexCoordinates T c r s) := by
  classical
  let D : Fin r ≃ (↑Tᶜ : Type) := Fintype.equivOfCardEq (by rw [Fintype.card_fin, Fintype.card_coe]; exact hN.symm)
  let A : Fin s ≃ (↑(T.erase c) : Type) := Fintype.equivOfCardEq (by rw [Fintype.card_fin, Fintype.card_coe]; exact hA.symm)
  let f : GradedCubic.Index r s → Fin n :=
    Sum.elim (fun i => (D i : Fin n)) (Sum.elim (fun i => (A i : Fin n)) (fun _ => c))
  have hD (i : Fin r) : (D i : Fin n) ∉ T := Finset.mem_compl.mp (D i).property
  have hA₁ (i : Fin s) : (A i : Fin n) ∈ T := Finset.mem_of_mem_erase (A i).property
  have hA₂ (i : Fin s) : (A i : Fin n) ≠ c := Finset.ne_of_mem_erase (A i).property
  have hinj : Function.Injective f := by
    intro i j hij
    cases i with
    | inl i =>
      cases j with
      | inl j =>
        congr 1
        apply D.injective
        exact Subtype.ext hij
      | inr j =>
        cases j with
        | inl j => exact False.elim (hD i (by change f (Sum.inl i) ∈ T; rw [hij]; exact hA₁ j))
        | inr j => exact False.elim (hD i (by change f (Sum.inl i) ∈ T; rw [hij]; exact hc))
    | inr i =>
      cases i with
      | inl i =>
        cases j with
        | inl j => exact False.elim (hD j (by change f (Sum.inl j) ∈ T; rw [← hij]; exact hA₁ i))
        | inr j =>
          cases j with
          | inl j =>
            congr 2
            apply A.injective
            exact Subtype.ext hij
          | inr j => exact False.elim (hA₂ i hij)
      | inr i =>
        cases j with
        | inl j => exact False.elim (hD j (by change f (Sum.inl j) ∈ T; rw [← hij]; exact hc))
        | inr j =>
          cases j with
          | inl j => exact False.elim (hA₂ j hij.symm)
          | inr j => congr 2
  have hsurj : Function.Surjective f := by
    intro j
    by_cases hj : j ∈ T
    · by_cases hjc : j = c
      · subst j
        exact ⟨Sum.inr (Sum.inr ()), rfl⟩
      · let a : (↑(T.erase c) : Type) := ⟨j, Finset.mem_erase.mpr ⟨hjc,hj⟩⟩
        refine ⟨Sum.inr (Sum.inl (A.symm a)), ?_⟩
        change (A (A.symm a) : Fin n) = j
        simp [a]
    · let d : (↑Tᶜ : Type) := ⟨j, Finset.mem_compl.mpr hj⟩
      refine ⟨Sum.inl (D.symm d), ?_⟩
      change (D (D.symm d) : Fin n) = j
      simp [d]
  exact ⟨⟨D, A, Equiv.ofBijective f ⟨hinj,hsurj⟩, fun _ => rfl, fun _ => rfl, rfl⟩⟩

variable {T : Finset (Fin n)} {c : Fin n}

def normalPolynomial (D : GradedIndexCoordinates T c r s)
    (q : MvPolynomial (↑Tᶜ : Type) K) : MvPolynomial (Fin r) K := rename D.normal.symm q

def normalTuple (D : GradedIndexCoordinates T c r s)
    (p : (↑Tᶜ : Type) → MvPolynomial (↑(T.erase c) : Type) K) :
    Fin r → MvPolynomial (Fin s) K := fun i => rename D.tangent.symm (p (D.normal i))

theorem rename_normal (D : GradedIndexCoordinates T c r s)
    (q : MvPolynomial (↑Tᶜ : Type) K) :
    rename D.equiv (rename Sum.inl (D.normalPolynomial q)) =
      rename (fun i : (↑Tᶜ : Type) => (i : Fin n)) q := by
  rw [normalPolynomial, rename_rename, rename_rename]
  congr 2
  funext i
  simp only [Function.comp_apply, D.normal_apply, Equiv.apply_symm_apply]

theorem rename_component (D : GradedIndexCoordinates T c r s)
    (p : (↑Tᶜ : Type) → MvPolynomial (↑(T.erase c) : Type) K) (i : Fin r) :
    rename D.equiv (GradedCubic.embed (D.normalTuple p i)) =
      rename (fun j : (↑(T.erase c) : Type) => (j : Fin n)) (p (D.normal i)) := by
  rw [normalTuple, GradedCubic.embed, rename_rename, rename_rename]
  congr 2
  funext j
  simp only [Function.comp_apply, D.tangent_apply, Equiv.apply_symm_apply]

/-- The renamed polynomial is exactly the radial-normal expression in
the original indexed coordinates. -/
theorem rename_cubic (D : GradedIndexCoordinates T c r s)
    (q : MvPolynomial (↑Tᶜ : Type) K)
    (p : (↑Tᶜ : Type) → MvPolynomial (↑(T.erase c) : Type) K) :
    rename D.equiv (GradedCubic.cubic (D.normalPolynomial q) (D.normalTuple p)) =
      X c * rename (fun i : (↑Tᶜ : Type) => (i : Fin n)) q +
      ∑ i : (↑Tᶜ : Type), X (i : Fin n) *
        rename (fun j : (↑(T.erase c) : Type) => (j : Fin n)) (p i) := by
  rw [GradedCubic.cubic, map_add, map_mul, rename_X, D.radial_apply, D.rename_normal]
  rw [map_sum]
  simp only [map_mul, rename_X, D.normal_apply, D.rename_component]
  congr 1
  exact D.normal.sum_comp (fun i : (↑Tᶜ : Type) => (X (i : Fin n) : MvPolynomial (Fin n) K) *
    rename (fun j : (↑(T.erase c) : Type) => (j : Fin n)) (p i))

theorem normalPolynomial_homogeneous (D : GradedIndexCoordinates T c r s)
    (q : MvPolynomial (↑Tᶜ : Type) K) (hq : q.IsHomogeneous 2) :
    (D.normalPolynomial q).IsHomogeneous 2 := hq.rename_isHomogeneous

theorem normalTuple_homogeneous (D : GradedIndexCoordinates T c r s)
    (p : (↑Tᶜ : Type) → MvPolynomial (↑(T.erase c) : Type) K)
    (hp : ∀ i, (p i).IsHomogeneous 2) :
    ∀ i, (D.normalTuple p i).IsHomogeneous 2 := fun i => (hp (D.normal i)).rename_isHomogeneous

end GradedIndexCoordinates
end HessianTheorem11
