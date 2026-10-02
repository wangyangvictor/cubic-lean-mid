import TranslatedDepthSeven.FiniteFreeFibrePointCount

/-!
# A restriction fibre as algebra homomorphisms over the base point

Let `g : B →ₐ[k] A` and let `phi : B →ₐ[k] K` be a `K`-valued
point of `B`.  Giving a `k`-algebra homomorphism `psi : A →ₐ[k] K`
whose restriction along `g` is `phi` is exactly the same as giving a
`B`-algebra homomorphism from `A` to `K`, after the `B`-algebra structures
on `A` and `K` have been defined by `g` and `phi` themselves.

The statements below record this literal equivalence and its elementary
finite-fibre consequence.  No auxiliary geometric notion of a fibre is
introduced.
-/

namespace TranslatedDepthSeven

noncomputable section

open scoped TensorProduct

universe u v w z

/-- The fibre over `phi` of restriction along `g` is the type of
`B`-algebra homomorphisms for the algebra structures defined by `g` and
`phi`. -/
def restrictionFibreAlgHomEquiv
    (k : Type u) (B : Type v) (A : Type w) (K : Type z)
    [CommSemiring k] [CommSemiring B] [CommSemiring A] [CommSemiring K]
    [Algebra k B] [Algebra k A] [Algebra k K]
    (g : B →ₐ[k] A) (phi : B →ₐ[k] K) :
    {psi : A →ₐ[k] K // psi.comp g = phi} ≃
      @AlgHom B A K _ _ _ g.toRingHom.toAlgebra
        phi.toRingHom.toAlgebra := by
  letI : Algebra B A := g.toRingHom.toAlgebra
  letI : Algebra B K := phi.toRingHom.toAlgebra
  exact
    { toFun := fun psi ↦
        { __ := psi.1.toRingHom
          commutes' := fun b ↦ by
            change psi.1 (g b) = phi b
            exact DFunLike.congr_fun psi.2 b }
      invFun := fun theta ↦
        ⟨{ __ := theta.toRingHom
           commutes' := fun r ↦ by
             rw [← g.commutes r]
             change theta (algebraMap B A (algebraMap k B r)) =
               algebraMap k K r
             rw [theta.commutes]
             change phi (algebraMap k B r) = algebraMap k K r
             exact phi.commutes r },
          by
            ext b
            exact theta.commutes b⟩
      left_inv := fun psi ↦ by
        apply Subtype.ext
        ext a
        rfl
      right_inv := fun theta ↦ by
        ext a
        rfl }

/-- If `A` is module-finite over `B` for the structure map `g`, then the
literal restriction fibre over `phi` has cardinality at most the dimension
of the scalar fibre `K ⊗[B] A`. -/
theorem natCard_restrictionFibre_le_baseChange_finrank
    (k : Type u) (B : Type v) (A : Type w) (K : Type z)
    [CommSemiring k] [CommRing B] [CommRing A] [Field K] [Finite K]
    [Algebra k B] [Algebra k A] [Algebra k K]
    (g : B →ₐ[k] A) (phi : B →ₐ[k] K)
    (hfinite :
      letI : Algebra B A := g.toRingHom.toAlgebra
      Module.Finite B A) :
    Nat.card {psi : A →ₐ[k] K // psi.comp g = phi} ≤
      letI : Algebra B A := g.toRingHom.toAlgebra
      letI : Algebra B K := phi.toRingHom.toAlgebra
      Module.finrank K (K ⊗[B] A) := by
  letI : Algebra B A := g.toRingHom.toAlgebra
  letI : Algebra B K := phi.toRingHom.toAlgebra
  letI : Module.Finite B A := hfinite
  rw [Nat.card_congr (restrictionFibreAlgHomEquiv k B A K g phi)]
  exact natCard_algHom_over_base_le_baseChange_finrank B K A

/-- A displayed `B`-spanning family of size `D` bounds the literal
restriction fibre by `D`.  This does not require `A` to be free over `B`. -/
theorem natCard_restrictionFibre_le_of_span_fin
    (k : Type u) (B : Type v) (A : Type w) (K : Type z) (D : ℕ)
    [CommSemiring k] [CommRing B] [CommRing A] [Field K] [Finite K]
    [Algebra k B] [Algebra k A] [Algebra k K]
    (g : B →ₐ[k] A) (phi : B →ₐ[k] K) (s : Fin D → A)
    (hs :
      letI : Algebra B A := g.toRingHom.toAlgebra
      Submodule.span B (Set.range s) = ⊤) :
    Nat.card {psi : A →ₐ[k] K // psi.comp g = phi} ≤ D := by
  letI : Algebra B A := g.toRingHom.toAlgebra
  letI : Algebra B K := phi.toRingHom.toAlgebra
  rw [Nat.card_congr (restrictionFibreAlgHomEquiv k B A K g phi)]
  exact natCard_algHom_over_base_le_of_span_fin B K A D s hs

/-- If the structure map `g` makes `A` finite free of displayed rank `D`,
then every restriction fibre over a finite-field point `phi` has at most
`D` elements.  The basis is base-changed along `phi`, so this is a direct
specialization of `natCard_restrictionFibre_le_baseChange_finrank`. -/
theorem natCard_restrictionFibre_le_of_basis_fin
    (k : Type u) (B : Type v) (A : Type w) (K : Type z) (D : ℕ)
    [CommSemiring k] [CommRing B] [CommRing A] [Field K] [Finite K]
    [Algebra k B] [Algebra k A] [Algebra k K]
    (g : B →ₐ[k] A) (phi : B →ₐ[k] K)
    (b :
      letI : Algebra B A := g.toRingHom.toAlgebra
      Module.Basis (Fin D) B A) :
    Nat.card {psi : A →ₐ[k] K // psi.comp g = phi} ≤ D := by
  letI : Algebra B A := g.toRingHom.toAlgebra
  letI : Algebra B K := phi.toRingHom.toAlgebra
  rw [Nat.card_congr (restrictionFibreAlgHomEquiv k B A K g phi)]
  exact natCard_algHom_over_base_le_of_basis_fin B K A D b

/-- Module-finiteness for the structure map `g` gives one integer `D`,
chosen before both the finite field `K` and the point `phi`, which bounds
every literal restriction fibre. -/
theorem exists_uniform_natCard_restrictionFibre_le_of_moduleFinite
    (k : Type u) (B : Type v) (A : Type w)
    [CommSemiring k] [CommRing B] [CommRing A]
    [Algebra k B] [Algebra k A] (g : B →ₐ[k] A)
    (hfinite :
      letI : Algebra B A := g.toRingHom.toAlgebra
      Module.Finite B A) :
    ∃ D : ℕ, ∀ (K : Type z), ∀ [Field K] [Finite K] [Algebra k K],
      ∀ phi : B →ₐ[k] K,
        Nat.card {psi : A →ₐ[k] K // psi.comp g = phi} ≤ D := by
  letI : Algebra B A := g.toRingHom.toAlgebra
  letI : Module.Finite B A := hfinite
  obtain ⟨D, hD⟩ :=
    exists_uniform_natCard_algHom_over_base_le_of_moduleFinite
      (B := B) (A := A)
  refine ⟨D, ?_⟩
  intro K _ _ _ phi
  letI : Algebra B K := phi.toRingHom.toAlgebra
  rw [Nat.card_congr (restrictionFibreAlgHomEquiv k B A K g phi)]
  exact hD K

end

end TranslatedDepthSeven
