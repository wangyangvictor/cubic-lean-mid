import TranslatedDepthSeven.ProjectiveBertiniGenericQuotient
import TranslatedDepthSeven.ProjectiveBertiniIncidenceElementaryCharts
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.Flat.Localization
import Mathlib.RingTheory.TensorProduct.Quotient

/-!
Regularity of the distinguished coordinate on elementary generic charts,
and its preservation under field extension. No Bertini existence hypothesis
is used in these algebraic compatibility statements.
-/

namespace TranslatedDepthSeven
noncomputable section
open MvPolynomial
open scoped TensorProduct
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 400000

theorem bertini_isRegular_of_injective
    {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (hf : Function.Injective f) (a : R) (ha : IsRegular (f a)) :
    IsRegular a := by
  have hleft : IsLeftRegular a := by
    intro x y hxy
    apply hf
    apply ha.left
    simpa only [← map_mul] using congrArg f hxy
  exact ⟨hleft, hleft.right_of_commute (fun _ ↦ Commute.all _ _)⟩

theorem bertini_isRegular_away_of_ringEquiv
    {R S : Type*} [CommRing R] [CommRing S]
    (e : R ≃+* S) (a b : R)
    (ha : IsRegular (algebraMap S (Localization.Away (e b)) (e a))) :
    IsRegular (algebraMap R (Localization.Away b) a) := by
  let e' : Localization.Away b ≃+* Localization.Away (e b) :=
    IsLocalization.ringEquivOfRingEquiv (M := Submonoid.powers b)
      (T := Submonoid.powers (e b)) _ _ e (Submonoid.map_powers e.toMonoidHom b)
  apply bertini_isRegular_of_injective e'.toRingHom e'.injective
  change IsRegular (e' (algebraMap R (Localization.Away b) a))
  rwa [IsLocalization.ringEquivOfRingEquiv_eq]

/-- On every chart where one incidence coefficient is invertible, each
nonzero original coordinate-ring element remains regular after taking
the actual generic hyperplane quotient. The chart may be empty. -/
theorem bertini_generic_coefficient_away_regular
    {K σ τ : Type*} [Field K] [Fintype τ]
    (L : Type*) [CommRing L] [Algebra (MvPolynomial τ K) L]
    [IsFractionRing (MvPolynomial τ K) L]
    (J : Ideal (MvPolynomial σ K)) [J.IsPrime]
    (E : τ → MvPolynomial σ K) (i : τ) (hi : E i ∉ J)
    (f : MvPolynomial σ K) (hf : f ∉ J) :
    let ψ := (algebraMap (MvPolynomial τ K) L).comp C
    let T := J.map (MvPolynomial.map ψ) ⊔
      Ideal.span {MvPolynomial.map (algebraMap (MvPolynomial τ K) L)
        (bertiniCoefficientHyperplane E)}
    let c := fun g : MvPolynomial σ K ↦ Ideal.Quotient.mk T (MvPolynomial.map ψ g)
    IsRegular (algebraMap (MvPolynomial σ L ⧸ T) (Localization.Away (c (E i))) (c f)) := by
  let ψ := (algebraMap (MvPolynomial τ K) L).comp C
  let T := J.map (MvPolynomial.map ψ) ⊔
    Ideal.span {MvPolynomial.map (algebraMap (MvPolynomial τ K) L)
      (bertiniCoefficientHyperplane E)}
  let c := fun g : MvPolynomial σ K ↦ Ideal.Quotient.mk T (MvPolynomial.map ψ g)
  let d := fun j ↦ Ideal.Quotient.mk J (E j)
  let S := BertiniGenericIncidenceRing (K := K) d
  let e := bertiniGenericCoefficientQuotientEquiv L J E
  have he (g : MvPolynomial σ K) : e (c g) =
      algebraMap (BertiniIncidenceRing d) S
        (bertiniIncidenceCoefficientMap d (Ideal.Quotient.mk J g)) :=
    bertiniGenericCoefficientQuotientEquiv_coordinate L J E g
  apply bertini_isRegular_away_of_ringEquiv e (c f) (c (E i))
  rw [he f, he (E i)]
  exact bertini_incidence_elementaryChart_regular_after_localization d
    ((nonZeroDivisors (MvPolynomial τ K)).map (bertiniParameterMap (K := K) d).toMonoidHom)
    i (fun h ↦ hi (Ideal.Quotient.eq_zero_iff_mem.mp h)) (Ideal.Quotient.mk J f)
    (fun h ↦ hf (Ideal.Quotient.eq_zero_iff_mem.mp h))

theorem bertini_isRegular_map_flat
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] [Module.Flat R S]
    (a : R) (ha : IsRegular a) : IsRegular (algebraMap R S a) := by
  have hleft : IsLeftRegular (algebraMap R S a) := by
    simpa only [IsSMulRegular, Algebra.smul_def] using
      (Module.Flat.isSMulRegular_of_isRegular (M := S) ha)
  exact ⟨hleft, hleft.right_of_commute (fun _ ↦ Commute.all _ _)⟩

/-- A regular element on a principal chart stays regular after any flat
base change, including every field extension. -/
theorem bertini_isRegular_away_after_flat
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] [Module.Flat R S]
    (a b : R) (ha : IsRegular (algebraMap R (Localization.Away b) a)) :
    IsRegular (algebraMap S (Localization.Away (algebraMap R S b)) (algebraMap R S a)) := by
  let Rb := Localization.Away b
  let T := Localization.Away (algebraMap R S b)
  let f : Rb →+* T := IsLocalization.Away.map Rb T (algebraMap R S) b
  have hf (r : R) : f (algebraMap R Rb r) =
      algebraMap S T (algebraMap R S r) := by
    simp only [f, IsLocalization.Away.map, IsLocalization.map_eq]
  letI : Algebra Rb T := f.toAlgebra
  haveI : IsScalarTower R Rb T := IsScalarTower.of_algebraMap_eq' (by
    ext r
    exact (hf r).symm)
  letI : Module.Flat R T := Module.Flat.trans R S T
  letI : Module.Flat Rb T :=
    (Module.flat_iff_of_isLocalization Rb (Submonoid.powers b) T).mpr inferInstance
  have h := bertini_isRegular_map_flat (S := T) (algebraMap R Rb a) ha
  change IsRegular (f (algebraMap R Rb a)) at h
  rwa [hf] at h

/-- The actual quotient map of a flat ring map is flat. -/
theorem bertini_quotient_flat
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] [Module.Flat R S]
    (I : Ideal R) :
    letI := (Ideal.quotientMap (I.map (algebraMap R S)) (algebraMap R S)
      Ideal.le_comap_map).toAlgebra
    Module.Flat (R ⧸ I) (S ⧸ I.map (algebraMap R S)) := by
  letI := (Ideal.quotientMap (I.map (algebraMap R S)) (algebraMap R S)
      Ideal.le_comap_map).toAlgebra
  let Q := (R ⧸ I) ⊗[R] S
  let e : (S ⧸ I.map (algebraMap R S)) ≃+* Q :=
    (Algebra.TensorProduct.quotIdealMapEquivTensorQuot S I).toRingEquiv.trans
      (Algebra.TensorProduct.comm R S (R ⧸ I)).toRingEquiv
  have he (a : R ⧸ I) :
      e (algebraMap (R ⧸ I) (S ⧸ I.map (algebraMap R S)) a) =
        algebraMap (R ⧸ I) Q a := by
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective a
    change e (Ideal.Quotient.mk _ (algebraMap R S r)) = _
    simp only [e, RingEquiv.trans_apply, AlgEquiv.toRingEquiv_eq_coe,
      AlgEquiv.coe_ringEquiv, Algebra.TensorProduct.quotIdealMapEquivTensorQuot_mk]
    change (1 : R ⧸ I) ⊗ₜ[R] algebraMap R S r = (Ideal.Quotient.mk I r) ⊗ₜ[R] (1 : S)
    rw [show algebraMap R S r = r • (1 : S) by simp [Algebra.smul_def],
      ← TensorProduct.smul_tmul]
    rw [show r • (1 : R ⧸ I) = Ideal.Quotient.mk I r from by
      simpa only [mul_one] using (Algebra.smul_def r (1 : R ⧸ I))]
  let eL : (S ⧸ I.map (algebraMap R S)) ≃ₗ[R ⧸ I] Q :=
    { e.toAddEquiv with
      map_smul' := by
        intro a b
        change e (a • b) = a • e b
        rw [Algebra.smul_def, map_mul, he]
        exact (Algebra.smul_def a (e b)).symm }
  exact Module.Flat.of_linearEquiv eL

attribute [local instance] MvPolynomial.algebraMvPolynomial

/-- Regularity on an actual polynomial-quotient chart survives arbitrary
extension of the coefficient field. Neither ideal is required to be prime. -/
theorem bertini_coefficientExtension_away_regular
    {K L σ : Type*} [Field K] [Field L] [Algebra K L]
    (I : Ideal (MvPolynomial σ K)) (a b : MvPolynomial σ K)
    (ha : IsRegular (algebraMap (MvPolynomial σ K ⧸ I)
      (Localization.Away (Ideal.Quotient.mk I b)) (Ideal.Quotient.mk I a))) :
    let IL := I.map (MvPolynomial.map (algebraMap K L))
    IsRegular (algebraMap (MvPolynomial σ L ⧸ IL)
      (Localization.Away (Ideal.Quotient.mk IL (MvPolynomial.map (algebraMap K L) b)))
      (Ideal.Quotient.mk IL (MvPolynomial.map (algebraMap K L) a))) := by
  letI : Module.Flat (MvPolynomial σ K) (MvPolynomial σ L) :=
    Module.Flat.isBaseChange (R := K) (M := L) (S := MvPolynomial σ K)
      (MvPolynomial σ L) Algebra.IsPushout.out
  let IL := I.map (algebraMap (MvPolynomial σ K) (MvPolynomial σ L))
  letI : Algebra (MvPolynomial σ K ⧸ I) (MvPolynomial σ L ⧸ IL) :=
    (Ideal.quotientMap IL (algebraMap (MvPolynomial σ K) (MvPolynomial σ L))
      Ideal.le_comap_map).toAlgebra
  letI : Module.Flat (MvPolynomial σ K ⧸ I) (MvPolynomial σ L ⧸ IL) :=
    bertini_quotient_flat I
  exact bertini_isRegular_away_after_flat (S := MvPolynomial σ L ⧸ IL)
    (Ideal.Quotient.mk I a) (Ideal.Quotient.mk I b) ha

theorem bertini_coefficientHyperplaneIdeal_map
    {K L M σ τ : Type*} [Field K] [CommRing L] [CommRing M] [Fintype τ]
    (φ : MvPolynomial τ K →+* L) (χ : L →+* M)
    (J : Ideal (MvPolynomial σ K)) (E : τ → MvPolynomial σ K) :
    (J.map (MvPolynomial.map (φ.comp C)) ⊔
      Ideal.span {MvPolynomial.map φ (bertiniCoefficientHyperplane E)}).map
        (MvPolynomial.map χ) =
      J.map (MvPolynomial.map ((χ.comp φ).comp C)) ⊔
        Ideal.span {MvPolynomial.map (χ.comp φ) (bertiniCoefficientHyperplane E)} := by
  rw [← bertiniUniversalCoefficientIdeal_map φ J E,
    ← bertiniUniversalCoefficientIdeal_map (χ.comp φ) J E, Ideal.map_map]
  congr 1
  ext a i <;> simp

/-- The elementary overlap regularity holds on the literal generic
hyperplane equation after any further field extension, in particular
after algebraic closure of the parameter function field. -/
theorem bertini_generic_coefficient_away_regular_after_fieldExtension
    {K σ τ : Type*} [Field K] [Fintype τ]
    (L : Type*) [Field L] [Algebra (MvPolynomial τ K) L]
    [IsFractionRing (MvPolynomial τ K) L]
    (M : Type*) [Field M] [Algebra L M]
    (J : Ideal (MvPolynomial σ K)) [J.IsPrime]
    (E : τ → MvPolynomial σ K) (i : τ) (hi : E i ∉ J)
    (f : MvPolynomial σ K) (hf : f ∉ J) :
    let φ := (algebraMap L M).comp (algebraMap (MvPolynomial τ K) L)
    let T := J.map (MvPolynomial.map (φ.comp C)) ⊔
      Ideal.span {MvPolynomial.map φ (bertiniCoefficientHyperplane E)}
    let c := fun g : MvPolynomial σ K ↦ Ideal.Quotient.mk T (MvPolynomial.map (φ.comp C) g)
    IsRegular (algebraMap (MvPolynomial σ M ⧸ T) (Localization.Away (c (E i))) (c f)) := by
  let φ := algebraMap (MvPolynomial τ K) L
  let T := J.map (MvPolynomial.map (φ.comp C)) ⊔
    Ideal.span {MvPolynomial.map φ (bertiniCoefficientHyperplane E)}
  have hL := bertini_generic_coefficient_away_regular L J E i hi f hf
  have hM := bertini_coefficientExtension_away_regular (K := L) (L := M) T
    (MvPolynomial.map (φ.comp C) f) (MvPolynomial.map (φ.comp C) (E i)) hL
  dsimp only at hM
  rw [show T.map (MvPolynomial.map (algebraMap L M)) = _ from
    bertini_coefficientHyperplaneIdeal_map φ (algebraMap L M) J E] at hM
  have hEi : MvPolynomial.map (algebraMap L M) (MvPolynomial.map (φ.comp C) (E i)) =
      MvPolynomial.map (((algebraMap L M).comp φ).comp C) (E i) := by
    rw [MvPolynomial.map_map]
    rfl
  rw [hEi, MvPolynomial.map_map] at hM
  exact hM

/-- The complete overlap condition needed for projective saturation:
each coefficient vanishes, or the distinguished nonzero element is
regular on that coefficient's principal chart. -/
theorem bertini_generic_coefficient_regular_overlaps_after_fieldExtension
    {K σ τ : Type*} [Field K] [Fintype τ]
    (L : Type*) [Field L] [Algebra (MvPolynomial τ K) L]
    [IsFractionRing (MvPolynomial τ K) L]
    (M : Type*) [Field M] [Algebra L M]
    (J : Ideal (MvPolynomial σ K)) [J.IsPrime]
    (E : τ → MvPolynomial σ K) (f : MvPolynomial σ K) (hf : f ∉ J) :
    let φ := (algebraMap L M).comp (algebraMap (MvPolynomial τ K) L)
    let T := J.map (MvPolynomial.map (φ.comp C)) ⊔
      Ideal.span {MvPolynomial.map φ (bertiniCoefficientHyperplane E)}
    let c := fun g : MvPolynomial σ K ↦ Ideal.Quotient.mk T (MvPolynomial.map (φ.comp C) g)
    ∀ i, c (E i) = 0 ∨
      IsRegular (algebraMap (MvPolynomial σ M ⧸ T) (Localization.Away (c (E i))) (c f)) := by
  classical
  intro φ T c i
  by_cases hi : E i ∈ J
  · left
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    exact (show J.map (MvPolynomial.map (φ.comp C)) ≤ T from le_sup_left)
      (Ideal.mem_map_of_mem _ hi)
  · right
    exact bertini_generic_coefficient_away_regular_after_fieldExtension L M J E i hi f hf

end
end TranslatedDepthSeven
