import TranslatedDepthSeven.ProjectiveBertiniIncidenceAlgebra
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Algebra.Polynomial.AlgebraMap

/-!
# Coordinate forms of the prime incidence equation

The ring isomorphism splitting off two variables transports the checked
regular-pair argument to a literal multivariate-polynomial ideal.
-/

namespace TranslatedDepthSeven

noncomputable section

open MvPolynomial
variable {R : Type*} [CommRing R] [IsDomain R]

omit [IsDomain R] in
theorem bertini_optionEquivLeft_rename_some (σ : Type*) (p : MvPolynomial σ R) :
    optionEquivLeft R σ (rename some p) = Polynomial.C p := by
  induction p using MvPolynomial.induction_on with
  | C r => simp [optionEquivLeft_C]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p i hp => simp only [map_mul, rename_X, hp, optionEquivLeft_X_some]

/-- Literal multivariate incidence primeness, with the two distinguished
variables represented by `none` and `some none`. -/
theorem bertini_mvPolynomial_incidence_span_isPrime
    (σ : Type*) (a b : R) (c : MvPolynomial σ R) (ha : a ≠ 0)
    (hb : IsRegular (Ideal.Quotient.mk (Ideal.span ({a} : Set R)) b)) :
    (Ideal.span ({C a * X (none : Option (Option σ)) +
      rename some (C b * X (none : Option σ) + rename some c)} :
        Set (MvPolynomial (Option (Option σ)) R))).IsPrime := by
  let e : MvPolynomial (Option (Option σ)) R ≃ₐ[R]
      Polynomial (Polynomial (MvPolynomial σ R)) :=
    (optionEquivLeft R (Option σ)).trans
      (Polynomial.mapAlgEquiv (optionEquivLeft R σ))
  let L : MvPolynomial (Option (Option σ)) R :=
    C a * X none + rename some (C b * X none + rename some c)
  have he : e L = Polynomial.C (Polynomial.C (C a)) * Polynomial.X +
      Polynomial.C (Polynomial.C (C b) * Polynomial.X + Polynomial.C c) := by
    simp only [e, L, AlgEquiv.trans_apply, map_add, map_mul, optionEquivLeft_C,
      optionEquivLeft_X_none, bertini_optionEquivLeft_rename_some,
      Polynomial.coe_mapAlgEquiv, Polynomial.map_C, Polynomial.map_X]
    change Polynomial.C (optionEquivLeft R σ (C a)) * Polynomial.X +
      (Polynomial.C (optionEquivLeft R σ (C b)) *
        Polynomial.C (optionEquivLeft R σ (X none)) +
        Polynomial.C (optionEquivLeft R σ (rename some c))) = _
    rw [optionEquivLeft_C, optionEquivLeft_C, optionEquivLeft_X_none,
      bertini_optionEquivLeft_rename_some]
  have hmap : (Ideal.span ({L} : Set _)).map e.toRingHom =
      Ideal.span ({Polynomial.C (Polynomial.C (C a)) * Polynomial.X +
        Polynomial.C (Polynomial.C (C b) * Polynomial.X + Polynomial.C c)} : Set _) := by
    rw [Ideal.map_span, Set.image_singleton]
    exact congrArg (fun p ↦ Ideal.span ({p} : Set _)) he
  have hp : ((Ideal.span ({L} : Set _)).map e.toRingHom).IsPrime := by
    rw [hmap]
    exact bertini_polynomial_incidence_span_isPrime σ a b c ha hb
  have h := hp.comap e.toRingHom
  rw [Ideal.comap_map_of_bijective e.toRingHom e.bijective] at h
  exact h

end
end TranslatedDepthSeven
