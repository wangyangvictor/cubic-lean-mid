import HessianTheorem11.FourQuadricsRadical

/-! A basis in which a quadratic tuple with differential radical of
codimension at most two uses at most two tangent coordinates. -/
noncomputable section
namespace HessianTheorem11
open Module Submodule MvPolynomial
variable {K : Type*} [Field K] [CharZero K] {n m : ℕ}

theorem exists_basis_outside_radical
    (S : Submodule K (Fin n → K)) (d : ℕ) (hd : n ≤ finrank K S + d) :
    ∃ b : Basis (Fin n) K (Fin n → K), ∃ active : Finset (Fin n), active.card ≤ d ∧
      ∀ i ∉ active, b i ∈ S := by
  classical
  obtain ⟨C,hC⟩ := Submodule.exists_isCompl S
  let bc := Module.finBasis K C
  let bs := Module.finBasis K S
  let b := (bc.prod bs).map (C.prodEquivOfIsCompl S hC.symm)
  have hcard : Fintype.card (Fin (finrank K C) ⊕ Fin (finrank K S)) = n := by
    simpa using (finrank_eq_card_basis b).symm
  let e := Fintype.equivFinOfCardEq hcard
  let bf := b.reindex e
  let active : Finset (Fin n) := Finset.univ.image (fun i : Fin (finrank K C) => e (Sum.inl i))
  have hCa : active.card = finrank K C := by
    change (Finset.univ.image (e ∘ Sum.inl)).card = _
    rw [Finset.card_image_of_injective _ (e.injective.comp Sum.inl_injective)]
    simp
  have hdim := Submodule.finrank_add_eq_of_isCompl hC
  simp only [Module.finrank_pi, Fintype.card_fin] at hdim
  refine ⟨bf,active,by omega,?_⟩
  intro i hi
  obtain ⟨j,rfl⟩ := e.surjective i
  cases j with
  | inl j => exact (hi (Finset.mem_image.mpr ⟨j,Finset.mem_univ _,rfl⟩)).elim
  | inr j =>
    simp only [bf, Basis.reindex_apply, e.symm_apply_apply]
    simp only [b,Basis.map_apply,Basis.prod_apply,Sum.elim_inr]
    change (0 : Fin n → K) + (bs j : Fin n → K) ∈ S
    simpa only [zero_add] using (bs j).property

theorem three_quadrics_active_basis [IsAlgClosed K]
    (P : Fin 3 → MvPolynomial (Fin n) K)
    (hP : ∀ i, (P i).IsHomogeneous 2) (hli : LinearIndependent K P)
    (A : Matrix (Fin 3) (Fin 3) K) (hA : A.IsSymm) (hdet : A.det ≠ 0)
    (hrel : TangentHessianRank.quadraticRelation A P = 0) :
    ∃ b : Basis (Fin n) K (Fin n → K), ∃ active : Finset (Fin n), active.card ≤ 2 ∧
      ∀ i ∉ active, ∀ x j, polynomialDifferential (P j) x (b i) = 0 := by
  obtain ⟨b,active,hcard,hb⟩ := exists_basis_outside_radical
    (polynomialTupleDifferentialRadical P) 2
    (three_quadrics_common_radical_large P hP hli A hA hdet hrel)
  refine ⟨b,active,hcard,?_⟩
  intro i hi
  exact (mem_polynomialTupleDifferentialRadical P (b i)).mp (hb i hi)

end HessianTheorem11
