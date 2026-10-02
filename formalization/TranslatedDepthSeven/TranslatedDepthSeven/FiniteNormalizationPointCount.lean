import TranslatedDepthSeven.PrimeAffineNoetherNormalization
import TranslatedDepthSeven.RestrictionFibreAlgHom

/-!
# Finite-field point count from one finite normalization

Let `k` be finite and let a `k`-algebra `A` be module-finite over
`k[T₁,…,T_d]`.  Choose one finite module-generating family of size `D`.
For every point of affine `d`-space, scalar extension of that family spans
the corresponding fibre algebra, so the fibre has vector-space dimension at
most `D`.  Linear independence of distinct algebra homomorphisms bounds the
number of points in that fibre by `D`; summing over the exactly `(#k)^d`
base points gives `#A(k) ≤ D (#k)^d`.

This is the complete local residue-count consequence of Noether
normalization.  It uses module-finiteness itself, not generic freeness, and
therefore creates no exceptional locus on the normalization base.
-/

namespace TranslatedDepthSeven

noncomputable section

open scoped TensorProduct

universe u v

/-- Uniform form with the finite module-generating family displayed.  The
same integer `D` is therefore available after any specialization for which
the displayed algebra map and spanning identity are obtained by base change. -/
theorem natCard_algHom_le_mul_pow_of_normalization_span
    (k : Type u) (A : Type v) (d D : ℕ)
    [Field k] [Finite k] [CommRing A] [Algebra k A]
    (g : MvPolynomial (Fin d) k →ₐ[k] A)
    (s : Fin D → A)
    (hs :
      letI : Algebra (MvPolynomial (Fin d) k) A :=
        g.toRingHom.toAlgebra
      Submodule.span (MvPolynomial (Fin d) k) (Set.range s) = ⊤) :
    Nat.card (A →ₐ[k] k) ≤ D * Nat.card k ^ d := by
  let B := MvPolynomial (Fin d) k
  letI : Algebra B A := g.toRingHom.toAlgebra
  letI : Module.Finite B A := Module.finite_def.mpr <|
    Submodule.fg_iff_exists_fin_generating_family.mpr ⟨D, s, hs⟩
  let restriction : (A →ₐ[k] k) → (B →ₐ[k] k) :=
    fun psi ↦ psi.comp g
  letI : Finite (B →ₐ[k] k) :=
    Finite.of_equiv (Fin d → k) (mvPolynomialAlgHomEquiv k d).symm
  have hfiniteTotal : (Set.univ : Set (A →ₐ[k] k)).Finite := by
    apply Set.Finite.of_finite_fibers restriction (Set.toFinite _)
    intro phi _hphi
    letI : Algebra B k := phi.toRingHom.toAlgebra
    letI : Module.Finite k (k ⊗[B] A) :=
      Module.Finite.base_change B k A
    letI : Finite ((k ⊗[B] A) →ₐ[k] k) := by infer_instance
    letI : Finite (A →ₐ[B] k) :=
      Finite.of_injective (baseChangeLiftAlgHom B k A)
        (baseChangeLiftAlgHom_injective B k A)
    letI : Finite {psi : A →ₐ[k] k // psi.comp g = phi} :=
      Finite.of_equiv (A →ₐ[B] k)
        (restrictionFibreAlgHomEquiv k B A k g phi).symm
    simpa [restriction, Set.finite_coe_iff] using
      (Set.finite_coe_iff.mp
        (inferInstance : Finite {psi : A →ₐ[k] k // psi.comp g = phi}))
  letI : Finite (A →ₐ[k] k) :=
    Finite.of_finite_univ hfiniteTotal
  apply natCard_le_mul_pow_of_mvPolynomial_fibers k d D
    (A →ₐ[k] k) restriction
  intro phi
  have hfibre := natCard_restrictionFibre_le_baseChange_finrank
    k B A k g phi (inferInstance : Module.Finite B A)
  letI : Algebra B k := phi.toRingHom.toAlgebra
  exact hfibre.trans
    (finrank_scalarFibre_le_of_span_fin B k A D s hs)

/-- A displayed finite normalization over affine `d`-space gives the
expected finite-field point bound, with one constant depending only on the
finite module. -/
theorem exists_natCard_algHom_le_mul_pow_of_finite_normalization
    (k : Type u) (A : Type v) (d : ℕ)
    [Field k] [Finite k] [CommRing A] [Algebra k A]
    (g : MvPolynomial (Fin d) k →ₐ[k] A)
    (hfinite : g.Finite) :
    ∃ D : ℕ, Nat.card (A →ₐ[k] k) ≤ D * Nat.card k ^ d := by
  let B := MvPolynomial (Fin d) k
  letI : Algebra B A := g.toRingHom.toAlgebra
  letI : Module.Finite B A := hfinite
  obtain ⟨D, s, hs⟩ := Module.Finite.exists_fin (R := B) (M := A)
  exact ⟨D, natCard_algHom_le_mul_pow_of_normalization_span
    k A d D g s hs⟩

/-- Prime-affine form.  A displayed transcendence degree `d` first gives a
finite normalization by exactly `d` variables, and hence the point bound
`O((#k)^d)` with a constant fixed before counting the finite-field points. -/
theorem exists_natCard_primeAffine_algHom_le_mul_pow_of_trdeg_eq
    (k : Type u) [Field k] [Finite k] {n d : ℕ}
    (P : Ideal (MvPolynomial (Fin n) k)) [P.IsPrime]
    (htrdeg : Algebra.trdeg k (MvPolynomial (Fin n) k ⧸ P) =
      (d : Cardinal)) :
    ∃ D : ℕ,
      Nat.card ((MvPolynomial (Fin n) k ⧸ P) →ₐ[k] k) ≤
        D * Nat.card k ^ d := by
  obtain ⟨g, _hinjective, hfinite⟩ :=
    exists_finite_injective_normalization_of_primeAffine_of_trdeg_eq
      P htrdeg
  exact exists_natCard_algHom_le_mul_pow_of_finite_normalization
    k (MvPolynomial (Fin n) k ⧸ P) d g hfinite

end

end TranslatedDepthSeven
