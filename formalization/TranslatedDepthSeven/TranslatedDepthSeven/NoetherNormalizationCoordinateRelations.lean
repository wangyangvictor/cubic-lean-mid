import Mathlib.RingTheory.NoetherNormalization

/-!
# Coordinate relations from Noether normalization

For a finite-type algebra over a field, Noether normalization gives an
injective finite map from a polynomial algebra.  The finite map is integral,
so every member of any displayed finite coordinate family satisfies a
literal monic polynomial over the normalization algebra.  This is the
generic-field algebraic input used by the triangular fibre count.
-/

namespace TranslatedDepthSeven

noncomputable section

open Polynomial

universe u v

/-- Noether normalization together with monic equations for a designated
finite family of elements.  The polynomials and their vanishing equations
are part of the conclusion, rather than hidden in an integrality predicate.
-/
theorem exists_finite_normalization_with_monic_relations
    {k : Type u} {R : Type v} [Field k] [CommRing R] [Nontrivial R]
    [Algebra k R] [Algebra.FiniteType k R]
    {n : ℕ} (x : Fin n → R) :
    ∃ s : ℕ, ∃ g : MvPolynomial (Fin s) k →ₐ[k] R,
      Function.Injective g ∧ g.toRingHom.Finite ∧
      ∃ p : Fin n → (MvPolynomial (Fin s) k)[X],
        ∀ i, (p i).Monic ∧ (p i).eval₂ g.toRingHom (x i) = 0 := by
  obtain ⟨s, g, hg, hfinite⟩ :=
    exists_finite_inj_algHom_of_fg k R
  have hintegral : g.toRingHom.IsIntegral := hfinite.to_isIntegral
  choose p hpmonic hpzero using fun i ↦ hintegral (x i)
  exact ⟨s, g, hg, hfinite, p, fun i ↦ ⟨hpmonic i, hpzero i⟩⟩

/-- Concrete quotient form: the images of all original polynomial
coordinates satisfy monic equations over one finite Noether normalization.
-/
theorem exists_finite_normalization_with_quotient_coordinate_relations
    {k : Type u} [Field k] {n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) k)) (hI : I ≠ ⊤) :
    ∃ s : ℕ,
      ∃ g : MvPolynomial (Fin s) k →ₐ[k]
          (MvPolynomial (Fin n) k ⧸ I),
        Function.Injective g ∧ g.toRingHom.Finite ∧
        ∃ p : Fin n → (MvPolynomial (Fin s) k)[X],
          ∀ i, (p i).Monic ∧
            (p i).eval₂ g.toRingHom
              (Ideal.Quotient.mk I (MvPolynomial.X i)) = 0 := by
  letI : Nontrivial (MvPolynomial (Fin n) k ⧸ I) :=
    Ideal.Quotient.nontrivial_iff.mpr hI
  exact exists_finite_normalization_with_monic_relations
    (fun i ↦ Ideal.Quotient.mk I (MvPolynomial.X i))

/-- A normalization relation remains monic after specialization, and its
specialized coordinate remains a root.  Thus the relations above give the
literal monic polynomials required by `PolynomialFibreCount` and
`IteratedTriangularFibreCount` on every fibre where the two coefficient maps
agree. -/
theorem monic_relation_specializes
    {B : Type u} {R K : Type v} [CommRing B] [CommRing R] [CommRing K]
    (g : B →+* R) (phi : R →+* K) (psi : B →+* K)
    (hcomp : phi.comp g = psi) (x : R) (p : B[X])
    (hmonic : p.Monic) (hzero : p.eval₂ g x = 0) :
    (p.map psi).Monic ∧ (p.map psi).eval (phi x) = 0 := by
  refine ⟨hmonic.map psi, ?_⟩
  rw [eval_map, ← hcomp]
  apply (p.hom_eval₂ g phi x).symm.trans
  rw [hzero, map_zero]

end

end TranslatedDepthSeven
