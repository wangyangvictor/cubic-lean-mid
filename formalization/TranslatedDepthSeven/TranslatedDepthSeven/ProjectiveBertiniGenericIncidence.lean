import TranslatedDepthSeven.ProjectiveBertiniIncidenceLinearSum
import TranslatedDepthSeven.RationalPointResidueField
import Mathlib.RingTheory.Localization.FractionRing

/-!
The marked point gives a retraction from the universal linear-incidence
ring to the parameter polynomial ring. Consequently all nonzero parameter
polynomials survive, and an integral incidence ring has an integral generic
fiber. The generic fiber here is the literal localization at those images;
no assertion of geometric integrality is made.
-/

namespace TranslatedDepthSeven
noncomputable section
open MvPolynomial

variable {K R σ : Type*} [Field K] [CommRing R] [Algebra K R] [Fintype σ]

abbrev BertiniIncidenceRing (d : σ → R) :=
  MvPolynomial σ R ⧸ Ideal.span ({bertiniLinear d} : Set _)

def bertiniParameterMap (d : σ → R) :
    MvPolynomial σ K →+* BertiniIncidenceRing d :=
  (Ideal.Quotient.mk _).comp (MvPolynomial.map (algebraMap K R))

def bertiniParameterRetraction (d : σ → R) (x : R →ₐ[K] K)
    (hx : ∀ i, x (d i) = 0) :
    BertiniIncidenceRing d →+* MvPolynomial σ K :=
  Ideal.Quotient.lift _ (MvPolynomial.map x.toRingHom) (by
    change Ideal.span ({bertiniLinear d} : Set _) ≤
      RingHom.ker (MvPolynomial.map x.toRingHom)
    rw [Ideal.span_le, Set.singleton_subset_iff]
    change MvPolynomial.map x.toRingHom (bertiniLinear d) = 0
    simp [bertiniLinear, hx])

theorem bertiniParameterRetraction_leftInverse (d : σ → R)
    (x : R →ₐ[K] K) (hx : ∀ i, x (d i) = 0) :
    Function.LeftInverse (bertiniParameterRetraction d x hx)
      (bertiniParameterMap (K := K) d) := by
  intro p
  change MvPolynomial.map x.toRingHom
    (MvPolynomial.map (algebraMap K R) p) = p
  rw [MvPolynomial.map_map]
  have he : x.toRingHom.comp (algebraMap K R) = RingHom.id K := by
    ext a
    exact x.commutes a
  rw [he, MvPolynomial.map_id]

theorem bertiniParameterMap_injective (d : σ → R)
    (x : R →ₐ[K] K) (hx : ∀ i, x (d i) = 0) :
    Function.Injective (bertiniParameterMap (K := K) d) :=
  (bertiniParameterRetraction_leftInverse d x hx).injective

/-- The parameter-generic fiber is obtained by inverting precisely the
images of all nonzero parameter polynomials. -/
abbrev BertiniGenericIncidenceRing (d : σ → R) :=
  Localization ((nonZeroDivisors (MvPolynomial σ K)).map
    (bertiniParameterMap (K := K) d).toMonoidHom)

theorem bertiniGenericIncidence_isDomain (d : σ → R)
    (x : R →ₐ[K] K) (hx : ∀ i, x (d i) = 0)
    [IsDomain (BertiniIncidenceRing d)] :
    IsDomain (BertiniGenericIncidenceRing (K := K) d) := by
  apply IsLocalization.isDomain_localization
  exact map_le_nonZeroDivisors_of_injective
    (bertiniParameterMap (K := K) d) (bertiniParameterMap_injective d x hx) le_rfl

theorem bertini_marked_parameterMap_injective {N : ℕ}
    (J : Ideal (MvPolynomial (Fin N) K)) (z : Fin N → K)
    (hz : J ≤ RingHom.ker (aeval z).toRingHom) :
    Function.Injective (bertiniParameterMap (K := K)
      (fun i : Fin N ↦ Ideal.Quotient.mk J (X i - C (z i)))) := by
  apply bertiniParameterMap_injective _ (affineQuotientRationalPoint J z hz)
  intro i
  simp

end
end TranslatedDepthSeven
