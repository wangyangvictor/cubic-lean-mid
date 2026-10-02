import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Mathlib.RingTheory.FiniteType

/-!
# Module-finiteness from displayed monic coordinate equations

Let `A` be generated as an algebra over `B` by finitely many elements
`x i`.  If every `x i` satisfies a displayed monic polynomial over `B`,
then `A` is integral and of finite type over `B`, hence module-finite.

This is the static algebraic step used after spreading a generic Noether
normalization.  It does not require the specialized algebra to remain a
domain, reduced, equidimensional, or injective over the normalization base.
-/

namespace TranslatedDepthSeven

noncomputable section

open Polynomial

universe u v

/-- Enlarging the coefficient ring in a scalar tower does not destroy a
displayed finite set of algebra generators. -/
theorem adjoin_eq_top_of_adjoin_eq_top_of_tower
    {R : Type*} {B : Type u} {A : Type v}
    [CommRing R] [CommRing B] [CommRing A]
    [Algebra R B] [Algebra R A] [Algebra B A] [IsScalarTower R B A]
    {n : ℕ} (x : Fin n → A)
    (hgenerate : Algebra.adjoin R (Set.range x) = ⊤) :
    Algebra.adjoin B (Set.range x) = ⊤ := by
  apply Subalgebra.restrictScalars_injective R
  rw [Algebra.Subalgebra.restrictScalars_adjoin, hgenerate]
  simp

/-- The images of the polynomial coordinates generate every affine
quotient algebra. -/
theorem adjoin_affineQuotient_coordinates_eq_top
    (R : Type u) [CommRing R] {n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) R)) :
    Algebra.adjoin R
        (Set.range fun i ↦
          Ideal.Quotient.mk I (MvPolynomial.X i)) = ⊤ := by
  rw [Algebra.adjoin_range_eq_range_aeval]
  have heval :
      MvPolynomial.aeval
          (fun i ↦ Ideal.Quotient.mk I (MvPolynomial.X i)) =
        Ideal.Quotient.mkₐ R I := by
    apply MvPolynomial.algHom_ext
    intro i
    simp
  rw [heval]
  exact (AlgHom.range_eq_top _).mpr
    (Ideal.Quotient.mkₐ_surjective R I)

/-- Finite algebra generators which are individually integral make the
whole algebra module-finite.  Both the generating family and the
integrality hypotheses are displayed explicitly. -/
theorem moduleFinite_of_finite_integral_generators
    {B : Type u} {A : Type v} [CommRing B] [CommRing A] [Algebra B A]
    {n : ℕ} (x : Fin n → A)
    (hgenerate : Algebra.adjoin B (Set.range x) = ⊤)
    (hintegral : ∀ i, IsIntegral B (x i)) :
    Module.Finite B A := by
  classical
  letI : Algebra.FiniteType B A := by
    refine ⟨⟨Finset.univ.image x, ?_⟩⟩
    simpa only [Finset.coe_image, Finset.coe_univ, Set.image_univ] using
      hgenerate
  letI : Algebra.IsIntegral B A := by
    apply integralClosure_eq_top_iff.mp
    apply top_unique
    rw [← hgenerate]
    apply Algebra.adjoin_le
    rintro y ⟨i, rfl⟩
    exact hintegral i
  exact Algebra.IsIntegral.finite

/-- Displayed monic equations are a convenient concrete certificate for
the preceding theorem. -/
theorem moduleFinite_of_monic_coordinate_relations
    {B : Type u} {A : Type v} [CommRing B] [CommRing A] [Algebra B A]
    {n : ℕ} (x : Fin n → A)
    (hgenerate : Algebra.adjoin B (Set.range x) = ⊤)
    (p : Fin n → B[X])
    (hrelation : ∀ i,
      (p i).Monic ∧ (p i).eval₂ (algebraMap B A) (x i) = 0) :
    Module.Finite B A := by
  apply moduleFinite_of_finite_integral_generators x hgenerate
  intro i
  exact ⟨p i, (hrelation i).1, (hrelation i).2⟩

/-- Quotient form suited to a spread affine component.  An `R`-algebra map
from `B` into the quotient supplies its `B`-algebra structure.  Monic
equations for the original affine coordinates then make that map finite.
No injectivity or primeness assumption is needed. -/
theorem finite_affineQuotient_map_of_monic_coordinate_relations
    {R : Type*} {B : Type u} [CommRing R] [CommRing B] [Algebra R B]
    {n : ℕ} (I : Ideal (MvPolynomial (Fin n) R))
    (g : B →ₐ[R] (MvPolynomial (Fin n) R ⧸ I))
    (p : Fin n → B[X])
    (hrelation : ∀ i,
      (p i).Monic ∧
        (p i).eval₂ g.toRingHom
            (Ideal.Quotient.mk I (MvPolynomial.X i)) = 0) :
    g.Finite := by
  let A := MvPolynomial (Fin n) R ⧸ I
  letI : Algebra B A := g.toRingHom.toAlgebra
  letI : IsScalarTower R B A :=
    IsScalarTower.of_algebraMap_eq fun r ↦ (g.commutes r).symm
  have hgenerateR :
      Algebra.adjoin R
          (Set.range fun i ↦
            Ideal.Quotient.mk I (MvPolynomial.X i)) = ⊤ :=
    adjoin_affineQuotient_coordinates_eq_top R I
  have hgenerateB :
      Algebra.adjoin B
          (Set.range fun i ↦
            Ideal.Quotient.mk I (MvPolynomial.X i)) = ⊤ :=
    adjoin_eq_top_of_adjoin_eq_top_of_tower
      (fun i ↦ Ideal.Quotient.mk I (MvPolynomial.X i)) hgenerateR
  exact moduleFinite_of_monic_coordinate_relations
    (fun i ↦ Ideal.Quotient.mk I (MvPolynomial.X i))
    hgenerateB p hrelation

end

end TranslatedDepthSeven
