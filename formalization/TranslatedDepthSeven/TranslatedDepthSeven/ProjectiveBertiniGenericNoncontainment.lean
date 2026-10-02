import TranslatedDepthSeven.ProjectiveBertiniGenericQuotient
import TranslatedDepthSeven.PolynomialCoefficientFaithfulFlat

/-!
The generic linear combination of coordinate polynomials cannot belong to
the extended source ideal if one of those polynomials did not belong to it.
The assertion is preserved by every further coefficient-field extension.
All polynomials, maps, and ideals in the conclusion are the literal ones.
-/

namespace TranslatedDepthSeven
noncomputable section
open MvPolynomial
attribute [local instance] MvPolynomial.algebraMvPolynomial
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 400000

variable {K σ τ : Type*} [Field K] [Fintype τ]

theorem bertiniLinear_ne_zero_of_coefficient
    {R : Type*} [CommRing R] (d : τ → R) (i : τ) (hi : d i ≠ 0) :
    bertiniLinear d ≠ 0 := by
  classical
  intro h
  have he := congrArg (MvPolynomial.eval (fun j ↦ if j = i then 1 else 0)) h
  exact hi (by simpa [bertiniLinear] using he)

/-- A proper generic hyperplane remains proper after localization in all
nonzero parameter polynomials. -/
theorem bertiniGenericCoefficientHyperplane_not_mem
    (L : Type*) [Field L] [Algebra (MvPolynomial τ K) L]
    [IsFractionRing (MvPolynomial τ K) L]
    (I : Ideal (MvPolynomial σ K)) [I.IsPrime]
    (E : τ → MvPolynomial σ K) (i : τ) (hi : E i ∉ I) :
    MvPolynomial.map (algebraMap (MvPolynomial τ K) L)
        (bertiniCoefficientHyperplane E) ∉
      I.map (MvPolynomial.map ((algebraMap (MvPolynomial τ K) L).comp C)) := by
  let P := MvPolynomial τ K
  let A := MvPolynomial σ P
  let B := MvPolynomial σ L
  let Iu := I.map (MvPolynomial.map (C : K →+* P))
  let M : Submonoid A := (nonZeroDivisors P).map (C : P →+* A)
  have hmap : Iu.map (algebraMap A B) =
      I.map (MvPolynomial.map ((algebraMap P L).comp C)) := by
    change (I.map (MvPolynomial.map (C : K →+* P))).map
      (MvPolynomial.map (algebraMap P L)) = _
    rw [Ideal.map_map]
    congr 1
    apply RingHom.ext
    intro p
    exact MvPolynomial.map_map C (algebraMap P L) p
  intro h
  rw [← hmap] at h
  change algebraMap A B (bertiniCoefficientHyperplane E) ∈
    Iu.map (algebraMap A B) at h
  obtain ⟨s, hs, hmem⟩ :=
    (IsLocalization.algebraMap_mem_map_algebraMap_iff M B Iu
      (bertiniCoefficientHyperplane E)).mp h
  obtain ⟨p, hp, rfl⟩ := hs
  have hz : bertiniUniversalCoordinateMap I (C p * bertiniCoefficientHyperplane E) = 0 := by
    apply RingHom.mem_ker.mp
    rw [bertiniUniversalCoordinateMap_ker]
    exact hmem
  rw [map_mul, bertiniUniversalCoordinateMap_hyperplane] at hz
  have hE : bertiniLinear (fun j ↦ Ideal.Quotient.mk I (E j)) ≠ 0 :=
    bertiniLinear_ne_zero_of_coefficient _ i
      (fun he ↦ hi (Ideal.Quotient.eq_zero_iff_mem.mp he))
  have he : bertiniUniversalCoordinateMap I (C p) =
      MvPolynomial.map (algebraMap K (MvPolynomial σ K ⧸ I)) p := by
    change MvPolynomial.map (Ideal.Quotient.mk I)
      (commAlgEquiv K σ τ (C p)) = _
    rw [commAlgEquiv_C, MvPolynomial.map_map]
    rfl
  rw [he] at hz
  have hp0 : p ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hp
  have hpmap : MvPolynomial.map (algebraMap K (MvPolynomial σ K ⧸ I)) p ≠ 0 := by
    exact fun hh ↦ hp0 ((MvPolynomial.map_injective _
      (algebraMap K (MvPolynomial σ K ⧸ I)).injective)
      (hh.trans (map_zero _).symm))
  exact (mul_ne_zero hpmap hE) hz

/-- The same noncontainment holds after every further field extension;
there is no geometric-integrality assumption on the extended source. -/
theorem bertiniGenericCoefficientHyperplane_not_mem_after_fieldExtension
    (L : Type*) [Field L] [Algebra (MvPolynomial τ K) L]
    [IsFractionRing (MvPolynomial τ K) L]
    (M : Type*) [Field M] [Algebra L M]
    (I : Ideal (MvPolynomial σ K)) [I.IsPrime]
    (E : τ → MvPolynomial σ K) (i : τ) (hi : E i ∉ I) :
    let φ := (algebraMap L M).comp (algebraMap (MvPolynomial τ K) L)
    MvPolynomial.map φ (bertiniCoefficientHyperplane E) ∉
      I.map (MvPolynomial.map (φ.comp C)) := by
  let ψ := (algebraMap (MvPolynomial τ K) L).comp C
  let IL := I.map (MvPolynomial.map ψ)
  have hmap : IL.map (MvPolynomial.map (algebraMap L M)) =
      I.map (MvPolynomial.map
        (((algebraMap L M).comp (algebraMap (MvPolynomial τ K) L)).comp C)) := by
    rw [Ideal.map_map]
    congr 1
    ext a j <;> simp [ψ]
  dsimp only
  intro h
  rw [← hmap] at h
  have h' : MvPolynomial.map (algebraMap (MvPolynomial τ K) L)
      (bertiniCoefficientHyperplane E) ∈
      (IL.map (MvPolynomial.map (algebraMap L M))).comap
        (MvPolynomial.map (algebraMap L M)) := by
    simpa only [Ideal.mem_comap, MvPolynomial.map_map] using h
  rw [polynomialCoefficient_comap_map_eq] at h'
  exact bertiniGenericCoefficientHyperplane_not_mem L I E i hi h'

end
end TranslatedDepthSeven
