import TranslatedDepthSeven.ProjectiveBertiniGenericIncidence
import TranslatedDepthSeven.ProjectiveBertiniSmoothGenericHyperplane
import Mathlib.RingTheory.MvPolynomial.Localization
import Mathlib.RingTheory.Polynomial.Quotient
import Mathlib.RingTheory.Localization.Ideal

/-!
The generic incidence equation as a literal coordinate-ring quotient.
Coordinate and parameter indices may differ. Incidence integrality remains
an explicit hypothesis; geometric integrality is not asserted.
-/

namespace TranslatedDepthSeven
noncomputable section
open MvPolynomial
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 500000

variable {K σ τ : Type*} [Field K] [Fintype τ]

def bertiniCoefficientHyperplane (E : τ → MvPolynomial σ K) :
    MvPolynomial σ (MvPolynomial τ K) :=
  ∑ i, C (X i) * MvPolynomial.map C (E i)

abbrev bertiniUniversalCoefficientIdeal (J : Ideal (MvPolynomial σ K))
    (E : τ → MvPolynomial σ K) :=
  J.map (MvPolynomial.map (C : K →+* MvPolynomial τ K)) ⊔
    Ideal.span {bertiniCoefficientHyperplane E}

def bertiniUniversalCoordinateMap (J : Ideal (MvPolynomial σ K)) :
    MvPolynomial σ (MvPolynomial τ K) →+* MvPolynomial τ (MvPolynomial σ K ⧸ J) :=
  (MvPolynomial.map (Ideal.Quotient.mk J)).comp
    (commAlgEquiv K σ τ).toRingEquiv.toRingHom

omit [Fintype τ] in
theorem bertiniUniversalCoordinateMap_surjective (J : Ideal (MvPolynomial σ K)) :
    Function.Surjective (bertiniUniversalCoordinateMap (τ := τ) J) :=
  (MvPolynomial.map_surjective _ Ideal.Quotient.mk_surjective).comp
    (commAlgEquiv K σ τ).surjective

omit [Fintype τ] in
theorem bertiniUniversalCoordinateMap_ker (J : Ideal (MvPolynomial σ K)) :
    RingHom.ker (bertiniUniversalCoordinateMap (τ := τ) J) =
      J.map (MvPolynomial.map (C : K →+* MvPolynomial τ K)) := by
  have hk : RingHom.ker (MvPolynomial.map (σ := τ) (Ideal.Quotient.mk J)) =
      J.map (C : MvPolynomial σ K →+* _) := by
    ext f
    simp only [RingHom.mem_ker, MvPolynomial.ext_iff, coeff_map, coeff_zero,
      Ideal.Quotient.eq_zero_iff_mem, MvPolynomial.mem_map_C_iff]
  let e := (commAlgEquiv K σ τ).toRingEquiv
  have he : e.toRingHom.comp (MvPolynomial.map (C : K →+* MvPolynomial τ K)) =
      (C : MvPolynomial σ K →+* _) := by
    ext a i <;> simp [e]
  have hm : (J.map (MvPolynomial.map (C : K →+* MvPolynomial τ K))).map
      e.toRingHom = J.map C := by
    rw [Ideal.map_map, he]
  change (RingHom.ker (MvPolynomial.map (Ideal.Quotient.mk J))).comap e.toRingHom = _
  rw [hk, ← hm, Ideal.comap_map_of_surjective e.toRingHom e.surjective,
    Ideal.comap_bot_of_injective e.toRingHom e.injective, sup_bot_eq]

theorem bertiniUniversalCoordinateMap_hyperplane
    (J : Ideal (MvPolynomial σ K)) (E : τ → MvPolynomial σ K) :
    bertiniUniversalCoordinateMap J (bertiniCoefficientHyperplane E) =
      bertiniLinear (fun i ↦ Ideal.Quotient.mk J (E i)) := by
  have he : (commAlgEquiv K σ τ).toRingEquiv.toRingHom.comp
      (MvPolynomial.map (C : K →+* MvPolynomial τ K)) =
      (C : MvPolynomial σ K →+* _) := by
    ext a i <;> simp
  simp only [bertiniUniversalCoordinateMap, RingHom.comp_apply,
    bertiniCoefficientHyperplane, map_sum, map_mul, bertiniLinear]
  apply Finset.sum_congr rfl
  intro i hi
  change MvPolynomial.map (Ideal.Quotient.mk J) (commAlgEquiv K σ τ (C (X i))) *
    MvPolynomial.map (Ideal.Quotient.mk J)
      (commAlgEquiv K σ τ (MvPolynomial.map C (E i))) = _
  rw [show commAlgEquiv K σ τ (MvPolynomial.map C (E i)) = C (E i) from
    DFunLike.congr_fun he (E i)]
  simp [mul_comm]

def bertiniUniversalIncidenceMap (J : Ideal (MvPolynomial σ K))
    (E : τ → MvPolynomial σ K) :
    MvPolynomial σ (MvPolynomial τ K) →+*
      BertiniIncidenceRing (fun i ↦ Ideal.Quotient.mk J (E i)) :=
  (Ideal.Quotient.mk _).comp (bertiniUniversalCoordinateMap J)

theorem bertiniUniversalIncidenceMap_ker
    (J : Ideal (MvPolynomial σ K)) (E : τ → MvPolynomial σ K) :
    RingHom.ker (bertiniUniversalIncidenceMap J E) = bertiniUniversalCoefficientIdeal J E := by
  have hm : (Ideal.span {bertiniCoefficientHyperplane E}).map
      (bertiniUniversalCoordinateMap J) =
      Ideal.span {bertiniLinear (fun i ↦ Ideal.Quotient.mk J (E i))} := by
    rw [Ideal.map_span, Set.image_singleton, bertiniUniversalCoordinateMap_hyperplane]
  change (RingHom.ker (Ideal.Quotient.mk _)).comap (bertiniUniversalCoordinateMap J) = _
  rw [Ideal.mk_ker, ← hm, Ideal.comap_map_of_surjective _
    (bertiniUniversalCoordinateMap_surjective J), ← RingHom.ker_eq_comap_bot,
    bertiniUniversalCoordinateMap_ker, sup_comm]

/-- Swapping variables identifies the literal universal equation with incidence. -/
def bertiniUniversalQuotientEquiv (J : Ideal (MvPolynomial σ K))
    (E : τ → MvPolynomial σ K) :
    (MvPolynomial σ (MvPolynomial τ K) ⧸ bertiniUniversalCoefficientIdeal J E) ≃+*
      BertiniIncidenceRing (fun i ↦ Ideal.Quotient.mk J (E i)) :=
  (Ideal.quotEquivOfEq (bertiniUniversalIncidenceMap_ker J E).symm).trans
    (RingHom.quotientKerEquivOfSurjective
      (Ideal.Quotient.mk_surjective.comp (bertiniUniversalCoordinateMap_surjective J)))

theorem bertiniUniversalQuotientEquiv_mk
    (J : Ideal (MvPolynomial σ K)) (E : τ → MvPolynomial σ K)
    (f : MvPolynomial σ (MvPolynomial τ K)) :
    bertiniUniversalQuotientEquiv J E (Ideal.Quotient.mk _ f) =
      bertiniUniversalIncidenceMap J E f := by
  simp [bertiniUniversalQuotientEquiv, RingHom.quotientKerEquivOfSurjective_apply_mk]

theorem bertiniUniversalQuotientEquiv_parameter
    (J : Ideal (MvPolynomial σ K)) (E : τ → MvPolynomial σ K)
    (f : MvPolynomial τ K) :
    bertiniUniversalQuotientEquiv J E (Ideal.Quotient.mk _ (C f)) =
      bertiniParameterMap (K := K) (fun i ↦ Ideal.Quotient.mk J (E i)) f := by
  rw [bertiniUniversalQuotientEquiv_mk]
  change Ideal.Quotient.mk _ (MvPolynomial.map (Ideal.Quotient.mk J)
    (commAlgEquiv K σ τ (C f))) = _
  rw [commAlgEquiv_C, MvPolynomial.map_map]
  rfl

attribute [local instance] MvPolynomial.algebraMvPolynomial

/-- A quotient commutes with localization for its actual coefficient map. -/
theorem bertini_parameterQuotient_isLocalization
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    (M : Submonoid A) [IsLocalization M B] (I : Ideal A) :
    letI := (Ideal.quotientMap (I.map (algebraMap A B)) (algebraMap A B)
      Ideal.le_comap_map).toAlgebra
    IsLocalization (M.map (Ideal.Quotient.mk I)) (B ⧸ I.map (algebraMap A B)) := by
  letI := (Ideal.quotientMap (I.map (algebraMap A B)) (algebraMap A B)
      Ideal.le_comap_map).toAlgebra
  apply IsLocalization.of_surjective M B
    (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
    (Ideal.Quotient.mk (I.map (algebraMap A B))) Ideal.Quotient.mk_surjective
  · ext x
    rfl
  · simp only [Ideal.mk_ker, le_refl]

theorem bertiniUniversalCoefficientIdeal_map
    {L : Type*} [CommRing L] (φ : MvPolynomial τ K →+* L)
    (J : Ideal (MvPolynomial σ K)) (E : τ → MvPolynomial σ K) :
    (bertiniUniversalCoefficientIdeal J E).map (MvPolynomial.map φ) =
      J.map (MvPolynomial.map (φ.comp C)) ⊔
        Ideal.span {MvPolynomial.map φ (bertiniCoefficientHyperplane E)} := by
  rw [Ideal.map_sup, Ideal.map_map, Ideal.map_span, Set.image_singleton]
  congr 2
  ext a i <;> simp

/-- Literal generic coordinate quotient equals localized universal incidence. -/
def bertiniGenericCoefficientQuotientEquiv
    (L : Type*) [CommRing L] [Algebra (MvPolynomial τ K) L]
    [IsFractionRing (MvPolynomial τ K) L]
    (J : Ideal (MvPolynomial σ K)) (E : τ → MvPolynomial σ K) :
    (MvPolynomial σ L ⧸
      (J.map (MvPolynomial.map ((algebraMap (MvPolynomial τ K) L).comp C)) ⊔
        Ideal.span {MvPolynomial.map (algebraMap (MvPolynomial τ K) L)
          (bertiniCoefficientHyperplane E)})) ≃+*
      BertiniGenericIncidenceRing (K := K) (fun i ↦ Ideal.Quotient.mk J (E i)) := by
  let P := MvPolynomial τ K
  let A := MvPolynomial σ P
  let B := MvPolynomial σ L
  let I : Ideal A := bertiniUniversalCoefficientIdeal J E
  let M : Submonoid A := (nonZeroDivisors P).map (C : P →+* A)
  let IQ := I.map (algebraMap A B)
  letI : Algebra (A ⧸ I) (B ⧸ IQ) :=
    (Ideal.quotientMap IQ (algebraMap A B) Ideal.le_comap_map).toAlgebra
  letI : IsLocalization (M.map (Ideal.Quotient.mk I)) (B ⧸ IQ) :=
    bertini_parameterQuotient_isLocalization M I
  let e := bertiniUniversalQuotientEquiv J E
  have hm : (M.map (Ideal.Quotient.mk I)).map e.toMonoidHom =
      (nonZeroDivisors P).map (bertiniParameterMap (K := K)
        (fun i ↦ Ideal.Quotient.mk J (E i))).toMonoidHom := by
    change (((nonZeroDivisors P).map (C : P →+* A).toMonoidHom).map
      (Ideal.Quotient.mk I).toMonoidHom).map e.toMonoidHom = _
    rw [Submonoid.map_map, Submonoid.map_map]
    congr 1
    ext p
    exact bertiniUniversalQuotientEquiv_parameter J E p
  have he := IsLocalization.ringEquivOfRingEquiv
    (M := M.map (Ideal.Quotient.mk I))
    (T := (nonZeroDivisors P).map (bertiniParameterMap (K := K)
      (fun i ↦ Ideal.Quotient.mk J (E i))).toMonoidHom)
    (B ⧸ IQ) (BertiniGenericIncidenceRing (K := K)
      (fun i ↦ Ideal.Quotient.mk J (E i))) e hm
  refine (Ideal.quotEquivOfEq ?_).trans he
  exact (bertiniUniversalCoefficientIdeal_map (algebraMap P L) J E).symm

theorem bertiniGenericCoefficientQuotientEquiv_mk_map
    (L : Type*) [CommRing L] [Algebra (MvPolynomial τ K) L]
    [IsFractionRing (MvPolynomial τ K) L]
    (J : Ideal (MvPolynomial σ K)) (E : τ → MvPolynomial σ K)
    (p : MvPolynomial σ (MvPolynomial τ K)) :
    bertiniGenericCoefficientQuotientEquiv L J E
      (Ideal.Quotient.mk _ (MvPolynomial.map (algebraMap (MvPolynomial τ K) L) p)) =
      algebraMap (BertiniIncidenceRing (fun i ↦ Ideal.Quotient.mk J (E i)))
        (BertiniGenericIncidenceRing (K := K) (fun i ↦ Ideal.Quotient.mk J (E i)))
        (bertiniUniversalIncidenceMap J E p) := by
  let A := MvPolynomial σ (MvPolynomial τ K)
  let B := MvPolynomial σ L
  let I : Ideal A := bertiniUniversalCoefficientIdeal J E
  let IQ := I.map (algebraMap A B)
  letI : Algebra (A ⧸ I) (B ⧸ IQ) :=
    (Ideal.quotientMap IQ (algebraMap A B) Ideal.le_comap_map).toAlgebra
  letI : IsLocalization
      (((nonZeroDivisors (MvPolynomial τ K)).map (C : MvPolynomial τ K →+* A)).map
        (Ideal.Quotient.mk I)) (B ⧸ IQ) :=
    bertini_parameterQuotient_isLocalization _ I
  unfold bertiniGenericCoefficientQuotientEquiv
  simp only [RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk]
  have hp : Ideal.Quotient.mk IQ (MvPolynomial.map (algebraMap (MvPolynomial τ K) L) p) =
      algebraMap (A ⧸ I) (B ⧸ IQ) (Ideal.Quotient.mk I p) := rfl
  rw [hp, IsLocalization.ringEquivOfRingEquiv_eq, bertiniUniversalQuotientEquiv_mk]

/-- In particular, the comparison carries every coordinate polynomial
to its same incidence class followed by parameter localization. -/
theorem bertiniGenericCoefficientQuotientEquiv_coordinate
    (L : Type*) [CommRing L] [Algebra (MvPolynomial τ K) L]
    [IsFractionRing (MvPolynomial τ K) L]
    (J : Ideal (MvPolynomial σ K)) (E : τ → MvPolynomial σ K)
    (f : MvPolynomial σ K) :
    bertiniGenericCoefficientQuotientEquiv L J E
      (Ideal.Quotient.mk _
        (MvPolynomial.map ((algebraMap (MvPolynomial τ K) L).comp C) f)) =
      algebraMap (BertiniIncidenceRing (fun i ↦ Ideal.Quotient.mk J (E i)))
        (BertiniGenericIncidenceRing (K := K) (fun i ↦ Ideal.Quotient.mk J (E i)))
        (Ideal.Quotient.mk _ (C (Ideal.Quotient.mk J f))) := by
  have h := bertiniGenericCoefficientQuotientEquiv_mk_map L J E (MvPolynomial.map C f)
  rw [MvPolynomial.map_map] at h
  rw [h]
  congr 1
  change Ideal.Quotient.mk _ (MvPolynomial.map (Ideal.Quotient.mk J)
    (commAlgEquiv K σ τ (MvPolynomial.map C f))) = _
  have he : (commAlgEquiv K σ τ).toRingEquiv.toRingHom.comp
      (MvPolynomial.map (C : K →+* MvPolynomial τ K)) =
      (C : MvPolynomial σ K →+* _) := by
    ext a i <;> simp
  rw [show commAlgEquiv K σ τ (MvPolynomial.map C f) = C f from
    DFunLike.congr_fun he f, MvPolynomial.map_C]

theorem bertiniCoefficientHyperplane_marked {N : ℕ} (z : Fin N → K) :
    bertiniCoefficientHyperplane (fun i ↦ X i - C (z i)) =
      bertiniGenericMarkedHyperplane z := by
  simp [bertiniCoefficientHyperplane, bertiniGenericMarkedHyperplane]

/-- The marked specialization matches the generic standard-smooth-chart ideal. -/
def bertiniGenericQuotientEquiv {N : ℕ}
    (L : Type*) [CommRing L] [Algebra (MvPolynomial (Fin N) K) L]
    [IsFractionRing (MvPolynomial (Fin N) K) L]
    (J : Ideal (MvPolynomial (Fin N) K)) (z : Fin N → K) :
    (MvPolynomial (Fin N) L ⧸
      (J.map (MvPolynomial.map ((algebraMap (MvPolynomial (Fin N) K) L).comp C)) ⊔
        Ideal.span {MvPolynomial.map (algebraMap (MvPolynomial (Fin N) K) L)
          (bertiniGenericMarkedHyperplane z)})) ≃+*
      BertiniGenericIncidenceRing (K := K)
        (fun i : Fin N ↦ Ideal.Quotient.mk J (X i - C (z i))) := by
  refine (Ideal.quotEquivOfEq ?_).trans
    (bertiniGenericCoefficientQuotientEquiv L J (fun i ↦ X i - C (z i)))
  rw [bertiniCoefficientHyperplane_marked]

/-- Incidence integrality and the marked point give generic-fiber integrality. -/
theorem bertiniGenericMarkedQuotient_isDomain {N : ℕ}
    (L : Type*) [CommRing L] [Algebra (MvPolynomial (Fin N) K) L]
    [IsFractionRing (MvPolynomial (Fin N) K) L]
    (J : Ideal (MvPolynomial (Fin N) K)) (z : Fin N → K)
    (hz : J ≤ RingHom.ker (aeval z).toRingHom)
    [IsDomain (BertiniIncidenceRing
      (fun i : Fin N ↦ Ideal.Quotient.mk J (X i - C (z i))))] :
    IsDomain (MvPolynomial (Fin N) L ⧸
      (J.map (MvPolynomial.map ((algebraMap (MvPolynomial (Fin N) K) L).comp C)) ⊔
        Ideal.span {MvPolynomial.map (algebraMap (MvPolynomial (Fin N) K) L)
          (bertiniGenericMarkedHyperplane z)})) := by
  letI := bertiniGenericIncidence_isDomain
    (fun i : Fin N ↦ Ideal.Quotient.mk J (X i - C (z i)))
    (affineQuotientRationalPoint J z hz) (by intro i; simp)
  exact (bertiniGenericQuotientEquiv L J z).toMulEquiv.isDomain _

end
end TranslatedDepthSeven
