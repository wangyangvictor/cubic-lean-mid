import TranslatedDepthSeven.ProjectiveConeHilbertShift
import TranslatedDepthSeven.PrimeAffineDimensionTranscendence

/-!
# Dimension of the cone over a prime affine quotient

The coordinate ring of the projective cone is a one-variable polynomial
ring over the original coordinate ring.  For prime finite-type algebras in
characteristic zero, transcendence degree and Krull dimension agree; hence
adjoining the cone coordinate raises Krull dimension by exactly one.
-/

namespace TranslatedDepthSeven

noncomputable section

set_option synthInstance.maxHeartbeats 200000

open MvPolynomial

universe u

/-- The usual quotient-ring description of a projective cone, retaining its
ground-field algebra structure. -/
noncomputable def projectiveConeQuotientAlgEquiv
    (K : Type u) [Field K] {N : ℕ}
    (I : Ideal (MvPolynomial (Fin N) K)) :
    (MvPolynomial (Option (Fin N)) K ⧸ projectiveConeIdealExtension I) ≃ₐ[K]
      Polynomial (MvPolynomial (Fin N) K ⧸ I) := by
  let e₁ := Ideal.quotientEquivAlg
      (projectiveConeIdealExtension I) (I.map Polynomial.C)
      (MvPolynomial.optionEquivLeft K (Fin N))
      (map_projectiveConeIdealExtension_optionEquivLeft I).symm
  let e₂ring := (I.polynomialQuotientEquivQuotientPolynomial).symm
  let e₂ :
      (Polynomial (MvPolynomial (Fin N) K) ⧸ I.map Polynomial.C) ≃ₐ[K]
        Polynomial (MvPolynomial (Fin N) K ⧸ I) :=
    AlgEquiv.ofRingEquiv (f := e₂ring) (by
    intro a
    change e₂ring (Ideal.Quotient.mk _
        (Polynomial.C (MvPolynomial.C a))) =
      Polynomial.C (Ideal.Quotient.mk I (MvPolynomial.C a))
    simp [e₂ring])
  exact e₁.trans e₂

/-- A prime affine cone quotient has dimension one larger than its prime
base quotient.  This is the finite-type-domain case of
`dim A[T] = dim A + 1`, proved here from Noether normalization and the
transcendence-degree tower formula. -/
theorem ringKrullDim_projectiveConeIdealExtension_eq_succ
    (K : Type u) [Field K] [CharZero K] {N r : ℕ}
    (I : Ideal (MvPolynomial (Fin N) K)) (hI : I.IsPrime)
    (hdim : ringKrullDim (MvPolynomial (Fin N) K ⧸ I) =
      (r : WithBot ℕ∞)) :
    ringKrullDim
        (MvPolynomial (Option (Fin N)) K ⧸ projectiveConeIdealExtension I) =
      ((r + 1 : ℕ) : WithBot ℕ∞) := by
  letI : I.IsPrime := hI
  let A := MvPolynomial (Fin N) K ⧸ I
  let C := MvPolynomial (Option (Fin N)) K ⧸ projectiveConeIdealExtension I
  letI : IsDomain A := (Ideal.Quotient.isDomain_iff_prime I).2 hI
  letI : IsDomain C := projectiveConeQuotient_isDomain I hI
  let e : C ≃ₐ[K] Polynomial A := projectiveConeQuotientAlgEquiv K I
  have htrdegA : Algebra.trdeg K A = (r : Cardinal) :=
    trdeg_eq_nat_of_primeAffine_ringKrullDim_eq K I hI hdim
  have htrdegPolyOverA : Algebra.trdeg A (Polynomial A) = 1 :=
    Polynomial.trdeg_of_isDomain
  have htrdegPoly : Algebra.trdeg K (Polynomial A) = (r + 1 : ℕ) := by
    have htower := trdeg_add_eq K A (A := Polynomial A)
    rw [htrdegA, htrdegPolyOverA] at htower
    simpa using htower.symm
  have htrdegC : Algebra.trdeg K C = (r + 1 : ℕ) := by
    rw [e.trdeg_eq]
    exact htrdegPoly
  have hconePrime : (projectiveConeIdealExtension I).IsPrime :=
    projectiveConeIdealExtension_isPrime I hI
  let variableEquiv : Option (Fin N) ≃ Fin (N + 1) :=
    (_root_.finSuccEquiv N).symm
  let J : Ideal (MvPolynomial (Fin (N + 1)) K) :=
    (projectiveConeIdealExtension I).map
      (MvPolynomial.renameEquiv K variableEquiv)
  let erename : C ≃ₐ[K] (MvPolynomial (Fin (N + 1)) K ⧸ J) :=
    renameQuotientAlgEquiv K variableEquiv (projectiveConeIdealExtension I)
  have hJprime : J.IsPrime := by
    letI : (projectiveConeIdealExtension I).IsPrime := hconePrime
    exact Ideal.map_isPrime_of_equiv
      (MvPolynomial.renameEquiv K variableEquiv)
  have htrdegJ :
      Algebra.trdeg K (MvPolynomial (Fin (N + 1)) K ⧸ J) =
        (r + 1 : ℕ) := by
    rw [← erename.trdeg_eq]
    exact htrdegC
  have hdimJ := ringKrullDim_eq_nat_of_primeAffine_trdeg_eq
    K J hJprime htrdegJ
  exact (ringKrullDim_eq_of_ringEquiv erename.toRingEquiv).trans hdimJ

end

end TranslatedDepthSeven
