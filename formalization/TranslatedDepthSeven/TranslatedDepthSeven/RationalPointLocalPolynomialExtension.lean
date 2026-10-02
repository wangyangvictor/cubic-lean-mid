import TranslatedDepthSeven.RationalPointSmoothConormalGeneration
import TranslatedDepthSeven.RationalPointLocalizedIdealEquality
import Mathlib.RingTheory.RingHom.Surjective
import Mathlib.RingTheory.Localization.Algebra

/-!
# The local polynomial presentation of an affine quotient at a rational point

For an ideal `J \subset k[x_1,\ldots,x_N]` vanishing at `z`, this file
constructs the literal surjection from the polynomial local ring at `z` to
the local ring of the quotient at the induced rational point.  Its kernel is
exactly the extension of `J` to the polynomial local ring.
-/

namespace TranslatedDepthSeven

noncomputable section

open MvPolynomial

universe u

/-- The prime ideal of an affine point, written using ordinary polynomial
evaluation. -/
def affineEvaluationPrime
    {k : Type u} {N : ℕ} [Field k] (z : Fin N → k) :
    Ideal (MvPolynomial (Fin N) k) :=
  RingHom.ker (MvPolynomial.eval z)

instance affineEvaluationPrime_isPrime
    {k : Type u} {N : ℕ} [Field k] (z : Fin N → k) :
    (affineEvaluationPrime z).IsPrime :=
  RingHom.ker_isPrime (MvPolynomial.eval z)

/-- The quotient point prime pulls back to the ordinary evaluation prime. -/
theorem affineEvaluationPrime_eq_comap_affineQuotientPoint
    {k : Type u} {N : ℕ} [Field k]
    (J : Ideal (MvPolynomial (Fin N) k)) (z : Fin N → k)
    (hJ : J ≤ RingHom.ker (MvPolynomial.aeval z).toRingHom) :
    affineEvaluationPrime z =
      Ideal.comap (Ideal.Quotient.mk J)
        (RingHom.ker (affineQuotientRationalPoint J z hJ).toRingHom) := by
  ext f
  change MvPolynomial.eval z f = 0 ↔
    affineQuotientRationalPoint J z hJ (Ideal.Quotient.mk J f) = 0
  rfl

/-- The local ring homomorphism from affine space to the displayed affine
quotient, localized at the corresponding rational points. -/
noncomputable def affineQuotientLocalRingAlgHom
    {k : Type u} {N : ℕ} [Field k]
    (J : Ideal (MvPolynomial (Fin N) k)) (z : Fin N → k)
    (hJ : J ≤ RingHom.ker (MvPolynomial.aeval z).toRingHom) :
    Localization.AtPrime (affineEvaluationPrime z) →ₐ[k]
      AffineQuotientRationalPointLocalRing J z hJ := by
  let q : MvPolynomial (Fin N) k →+*
      (MvPolynomial (Fin N) k ⧸ J) := Ideal.Quotient.mk J
  let x := affineQuotientRationalPoint J z hJ
  let Q : Ideal (MvPolynomial (Fin N) k ⧸ J) :=
    RingHom.ker x.toRingHom
  let f : Localization.AtPrime (affineEvaluationPrime z) →+*
      Localization.AtPrime Q :=
    Localization.localRingHom (affineEvaluationPrime z) Q q
      (affineEvaluationPrime_eq_comap_affineQuotientPoint J z hJ)
  exact
    { toRingHom := f
      commutes' := by
        intro a
        change f (algebraMap (MvPolynomial (Fin N) k)
          (Localization.AtPrime (affineEvaluationPrime z))
            (MvPolynomial.C a)) =
          algebraMap (MvPolynomial (Fin N) k ⧸ J)
            (Localization.AtPrime Q)
              (Ideal.Quotient.mk J (MvPolynomial.C a))
        simpa only [f] using
          Localization.localRingHom_to_map
            (affineEvaluationPrime z) Q q
              (affineEvaluationPrime_eq_comap_affineQuotientPoint J z hJ)
                (MvPolynomial.C a) }

/-- The preceding local quotient map is surjective. -/
theorem affineQuotientLocalRingAlgHom_surjective
    {k : Type u} {N : ℕ} [Field k]
    (J : Ideal (MvPolynomial (Fin N) k)) (z : Fin N → k)
    (hJ : J ≤ RingHom.ker (MvPolynomial.aeval z).toRingHom) :
    Function.Surjective (affineQuotientLocalRingAlgHom J z hJ) := by
  let q : MvPolynomial (Fin N) k →+*
      (MvPolynomial (Fin N) k ⧸ J) := Ideal.Quotient.mk J
  let x := affineQuotientRationalPoint J z hJ
  let Q : Ideal (MvPolynomial (Fin N) k ⧸ J) :=
    RingHom.ker x.toRingHom
  exact RingHom.surjective_localRingHom_of_surjective q
    Ideal.Quotient.mk_surjective Q

/-- The local polynomial presentation, regarded as an algebra extension. -/
noncomputable def affineQuotientLocalExtension
    {k : Type u} {N : ℕ} [Field k]
    (J : Ideal (MvPolynomial (Fin N) k)) (z : Fin N → k)
    (hJ : J ≤ RingHom.ker (MvPolynomial.aeval z).toRingHom) :
    Algebra.Extension k (AffineQuotientRationalPointLocalRing J z hJ) :=
  Algebra.Extension.ofSurjective
    (affineQuotientLocalRingAlgHom J z hJ)
    (affineQuotientLocalRingAlgHom_surjective J z hJ)

/-- The kernel of the literal local polynomial presentation is exactly the
extension of the affine quotient ideal to the polynomial local ring. -/
theorem affineQuotientLocalExtension_ker
    {k : Type u} {N : ℕ} [Field k]
    (J : Ideal (MvPolynomial (Fin N) k)) (z : Fin N → k)
    (hJ : J ≤ RingHom.ker (MvPolynomial.aeval z).toRingHom) :
    (affineQuotientLocalExtension J z hJ).ker =
      Ideal.map
        (algebraMap (MvPolynomial (Fin N) k)
          (Localization.AtPrime (affineEvaluationPrime z))) J := by
  let q : MvPolynomial (Fin N) k →+*
      (MvPolynomial (Fin N) k ⧸ J) := Ideal.Quotient.mk J
  let Q : Ideal (MvPolynomial (Fin N) k ⧸ J) :=
    RingHom.ker (affineQuotientRationalPoint J z hJ).toRingHom
  have hp : affineEvaluationPrime z = Ideal.comap q Q :=
    affineEvaluationPrime_eq_comap_affineQuotientPoint J z hJ
  have hprimeQ : Q.IsPrime := inferInstance
  have hprimeComap : (Ideal.comap q Q).IsPrime := Ideal.comap_isPrime q Q
  have hcompl : (affineEvaluationPrime z).primeCompl =
      (Ideal.comap q Q).primeCompl := by
    ext f
    change f ∉ affineEvaluationPrime z ↔ f ∉ Ideal.comap q Q
    rw [hp]
  have hT : Submonoid.map q (affineEvaluationPrime z).primeCompl =
      Q.primeCompl := by
    rw [hcompl]
    exact Submonoid.map_comap_eq_of_surjective
      Ideal.Quotient.mk_surjective Q.primeCompl
  change RingHom.ker
      (Localization.localRingHom (affineEvaluationPrime z) Q q hp) = _
  simpa only [Ideal.mk_ker, q] using
    (IsLocalization.ker_map
      (S := Localization.AtPrime (affineEvaluationPrime z))
      (Q := Localization.AtPrime Q) q hT)

/-- A finite generating family of the affine quotient ideal gives the
corresponding literal finite generating family of the local presentation
kernel. -/
theorem affineQuotientLocalExtension_ker_eq_span_of_span_eq
    {k : Type u} {N n : ℕ} [Field k]
    (J : Ideal (MvPolynomial (Fin N) k)) (z : Fin N → k)
    (hJ : J ≤ RingHom.ker (MvPolynomial.aeval z).toRingHom)
    (F : Fin n → MvPolynomial (Fin N) k)
    (hF : Ideal.span (Set.range F) = J) :
    Ideal.span (Set.range fun i ↦
      algebraMap (MvPolynomial (Fin N) k)
        (Localization.AtPrime (affineEvaluationPrime z)) (F i)) =
      (affineQuotientLocalExtension J z hJ).ker := by
  rw [affineQuotientLocalExtension_ker, ← hF, Ideal.map_span]
  congr 1
  rw [← Set.range_comp]
  rfl

end

end TranslatedDepthSeven
