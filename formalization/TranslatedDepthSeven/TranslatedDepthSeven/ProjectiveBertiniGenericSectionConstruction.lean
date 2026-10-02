import TranslatedDepthSeven.ProjectiveBertiniGenericProjectiveSection
import TranslatedDepthSeven.ProjectiveBertiniAffineChartDimension
import TranslatedDepthSeven.ProjectiveBertiniGenericNoncontainment
import TranslatedDepthSeven.ProjectiveDegreeSpanGenericReduction
import Mathlib.RingTheory.KrullDimension.Field

/-! Assembly tools for the actual generic-section construction used by
the varying-field degree--span induction. -/

namespace TranslatedDepthSeven
universe u
noncomputable section
open MvPolynomial
attribute [local instance] MvPolynomial.gradedAlgebra
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 500000

/-- Positive-dimensional polynomial quotients have a coordinate surviving
in the quotient. If every variable vanished, constants would surject onto
the quotient, forcing its Krull dimension to be at most zero. -/
theorem bertini_exists_coordinate_not_mem_of_positive_dimension
    {K σ : Type*} [Field K] (I : Ideal (MvPolynomial σ K))
    (hdim : 0 < ringKrullDim (MvPolynomial σ K ⧸ I)) :
    ∃ i : σ, X i ∉ I := by
  classical
  by_contra h
  push_neg at h
  let f : K →+* MvPolynomial σ K ⧸ I := (Ideal.Quotient.mk I).comp C
  have hpoly (p : MvPolynomial σ K) : ∃ c, f c = Ideal.Quotient.mk I p := by
    induction p using MvPolynomial.induction_on with
    | C c => exact ⟨c, rfl⟩
    | add p q hp hq =>
      obtain ⟨a, ha⟩ := hp
      obtain ⟨b, hb⟩ := hq
      exact ⟨a + b, by rw [map_add, ha, hb, map_add]⟩
    | mul_X p i hp =>
      refine ⟨0, ?_⟩
      rw [map_zero, map_mul, Ideal.Quotient.eq_zero_iff_mem.mpr (h i), mul_zero]
  have hf : Function.Surjective f := by
    intro a
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective a
    exact hpoly p
  have hle := ringKrullDim_le_of_surjective f hf
  rw [ringKrullDim_eq_zero_of_field] at hle
  exact not_lt_of_ge hle hdim

/-- A marked affine coordinate surviving in the chart comes from a
surviving homogeneous marked coordinate. -/
theorem bertiniProjectiveMarkedCoefficients_not_mem_of_chart
    {K : Type*} [Field K] {N : ℕ}
    (I : Ideal (MvPolynomial (Option (Fin N)) K)) (z : Fin N → K)
    (i : Fin N) (hi : X i - C (z i) ∉ I.map multivariateDehomogenization.toRingHom) :
    bertiniProjectiveMarkedCoefficients z i ∉ I := by
  intro h
  apply hi
  simpa [bertiniProjectiveMarkedCoefficients, multivariateDehomogenization] using
    Ideal.mem_map_of_mem multivariateDehomogenization.toRingHom h

/-- Coefficient extension and bijective renaming commute on the literal ideal. -/
theorem bertini_coefficientExtension_map_renameEquiv
    {K L σ τ : Type*} [Field K] [Field L]
    (φ : K →+* L) (e : σ ≃ τ) (I : Ideal (MvPolynomial σ K)) :
    (I.map (renameEquiv K e)).map (MvPolynomial.map φ) =
      (I.map (MvPolynomial.map φ)).map (renameEquiv L e) := by
  change (I.map (renameEquiv K e).toRingHom).map (MvPolynomial.map φ) =
    (I.map (MvPolynomial.map φ)).map (renameEquiv L e).toRingHom
  rw [Ideal.map_map, Ideal.map_map]
  congr 1
  ext a i <;> simp [renameEquiv_apply]

/-- Bijective renaming transports saturation at every projective coordinate. -/
theorem bertini_coordinate_saturation_map_renameEquiv
    {K σ τ : Type*} [Field K] (e : σ ≃ τ)
    (T J : Ideal (MvPolynomial σ K))
    (hsat : ∀ f ∈ J, ∀ i : σ, ∃ a : ℕ, X i ^ a * f ∈ T) :
    ∀ f ∈ J.map (renameEquiv K e), ∀ i : τ,
      ∃ a : ℕ, X i ^ a * f ∈ T.map (renameEquiv K e) := by
  intro f hf i
  obtain ⟨g, hg, rfl⟩ :=
    (Ideal.mem_map_iff_of_surjective (renameEquiv K e) (renameEquiv K e).surjective).mp hf
  obtain ⟨a, ha⟩ := hsat g hg (e.symm i)
  refine ⟨a, ?_⟩
  simpa only [map_mul, map_pow, renameEquiv_apply, rename_X, e.apply_symm_apply] using
    Ideal.mem_map_of_mem (renameEquiv K e) ha

/-- A surviving coordinate still survives after a bijective renaming. -/
theorem bertini_X_not_mem_map_renameEquiv
    {K σ τ : Type*} [Field K] (e : σ ≃ τ)
    (J : Ideal (MvPolynomial σ K)) (i : σ) (hi : X i ∉ J) :
    X (e i) ∉ J.map (renameEquiv K e) := by
  intro h
  obtain ⟨g, hg, hgeq⟩ :=
    (Ideal.mem_map_iff_of_surjective (renameEquiv K e) (renameEquiv K e).surjective).mp h
  have heq : g = X i := (renameEquiv K e).injective (by
    simpa only [renameEquiv_apply, rename_X] using hgeq)
  exact hi (heq ▸ hg)

/-- Renaming and then inversely renaming returns the original ideal. -/
theorem bertini_map_renameEquiv_symm
    {K σ τ : Type*} [Field K] (e : σ ≃ τ) (I : Ideal (MvPolynomial σ K)) :
    (I.map (renameEquiv K e)).map (renameEquiv K e.symm) = I := by
  change (I.map (renameEquiv K e).toRingHom).map
    (renameEquiv K e.symm).toRingHom = I
  rw [Ideal.map_map]
  have he : (renameEquiv K e.symm).toRingHom.comp (renameEquiv K e).toRingHom =
      RingHom.id _ := by
    ext a i <;> simp [renameEquiv_apply]
  rw [he, Ideal.map_id]

/-- A proper geometrically integral generic section, with the actual
homogeneous equation and all-coordinate saturation, over the algebraic
closure of the field of rational functions in the hyperplane parameters. -/
theorem bertini_exists_generic_projectiveSection_option
    {K : Type u} [Field K] [CharZero K] [IsAlgClosed K] {N r : ℕ}
    (I : Ideal (MvPolynomial (Option (Fin N)) K)) (hr : 2 ≤ r)
    (hprime : I.IsPrime)
    (hhom : I.IsHomogeneous (homogeneousSubmodule (Option (Fin N)) K))
    (hX : X (none : Option (Fin N)) ∉ I)
    (hdim : ringKrullDim (MvPolynomial (Option (Fin N)) K ⧸ I) = r + 1) :
    ∃ (M : Type u) (hMfield : Field M),
      letI : Field M := hMfield
      ∃ hMalgebra : Algebra K M,
        letI : Algebra K M := hMalgebra
        IsAlgClosed M ∧
        (I.map (MvPolynomial.map (algebraMap K M))).IsPrime ∧
        ∃ (ℓ : MvPolynomial (Option (Fin N)) M)
          (J : Ideal (MvPolynomial (Option (Fin N)) M)),
          ℓ.IsHomogeneous 1 ∧
          ℓ ∉ I.map (MvPolynomial.map (algebraMap K M)) ∧
          J.IsPrime ∧ J.IsHomogeneous (homogeneousSubmodule (Option (Fin N)) M) ∧
          X (none : Option (Fin N)) ∉ J ∧
          I.map (MvPolynomial.map (algebraMap K M)) ⊔ Ideal.span {ℓ} ≤ J ∧
          ∀ (f : MvPolynomial (Option (Fin N)) M), f ∈ J →
            ∀ i : Option (Fin N), ∃ a : ℕ,
            (X i : MvPolynomial (Option (Fin N)) M) ^ a * f ∈
              I.map (MvPolynomial.map (algebraMap K M)) ⊔ Ideal.span {ℓ} := by
  letI : I.IsPrime := hprime
  let Ia := I.map multivariateDehomogenization.toRingHom
  have hIa : Ia.IsPrime := map_multivariateDehomogenization_isPrime I hhom hprime hX
  have hdimIa : ringKrullDim (MvPolynomial (Fin N) K ⧸ Ia) = (r : WithBot ℕ∞) :=
    optionAffineChart_ringKrullDim_eq_of_cone I hhom hprime hX
      (by simpa only [Nat.cast_add, Nat.cast_one] using hdim)
  obtain ⟨z, _hz, ⟨i, hi⟩, hdomain⟩ :=
    exists_bertiniGenericMarkedQuotient_geometricDomain_nonconstant_of_primeAffine_dimension
      Ia hIa hdimIa hr
  have hEi : bertiniProjectiveMarkedCoefficients z i ∉ I :=
    bertiniProjectiveMarkedCoefficients_not_mem_of_chart I z i hi
  let L : Type u := FractionRing (MvPolynomial (Fin N) K)
  let M : Type u := AlgebraicClosure L
  let φ : MvPolynomial (Fin N) K →+* M :=
    (algebraMap L M).comp (algebraMap (MvPolynomial (Fin N) K) L)
  have hchart : (Ia.map (MvPolynomial.map (φ.comp C)) ⊔
      Ideal.span {MvPolynomial.map φ (bertiniGenericMarkedHyperplane z)}).IsPrime := by
    apply (Ideal.Quotient.isDomain_iff_prime _).mp
    exact hdomain L M
  obtain ⟨J, hJprime, hJhom, hTJ, hJX, hsat⟩ :=
    bertiniGenericProjectiveMarkedIdeal_exists_prime_saturation
      L M I hprime hhom hX z hchart
  letI : Algebra K M := (φ.comp C).toAlgebra
  have hℓ : MvPolynomial.map φ (bertiniGenericProjectiveMarkedHyperplane z) ∉
      I.map (MvPolynomial.map (algebraMap K M)) :=
    bertiniGenericCoefficientHyperplane_not_mem_after_fieldExtension
      L M I (bertiniProjectiveMarkedCoefficients z) i hEi
  refine ⟨M, inferInstance, inferInstance, inferInstance,
    coefficientExtension_isPrime_of_isAlgClosed I hprime,
    MvPolynomial.map φ (bertiniGenericProjectiveMarkedHyperplane z), J,
    (bertiniGenericProjectiveMarkedHyperplane_isHomogeneous z).map φ,
    hℓ, hJprime, hJhom, hJX, hTJ, hsat⟩

/-- The generic integral hyperplane section needed by the changing-field
induction, constructed internally from the literal marked incidence ring.
There is no Bertini or section-existence hypothesis. -/
theorem projectiveGenericIntegralHyperplaneSectionExists :
    ProjectiveGenericIntegralHyperplaneSectionExists.{u} := by
  classical
  intro K _ _ _ N r I hr hprime hhom hdim
  have hpos : 0 < ringKrullDim (MvPolynomial (Fin (N + 1)) K ⧸ I) := by
    rw [hdim]
    exact lt_of_lt_of_le (by norm_num : (0 : WithBot ℕ∞) < 1) (le_add_of_nonneg_left (by positivity))
  obtain ⟨i, hi⟩ := bertini_exists_coordinate_not_mem_of_positive_dimension I hpos
  let e : Fin (N + 1) ≃ Option (Fin N) :=
    (Equiv.swap i 0).trans (_root_.finSuccEquiv N)
  have hei : e i = none := by simp [e]
  let Io := I.map (renameEquiv K e)
  letI : I.IsPrime := hprime
  have hIoprime : Io.IsPrime := by dsimp only [Io]; infer_instance
  have hIohom : Io.IsHomogeneous (homogeneousSubmodule (Option (Fin N)) K) :=
    map_renameEquiv_isHomogeneous e I hhom
  have hIoX : X (none : Option (Fin N)) ∉ Io := by
    simpa only [hei] using bertini_X_not_mem_map_renameEquiv e I i hi
  have hIodim : ringKrullDim (MvPolynomial (Option (Fin N)) K ⧸ Io) = r + 1 :=
    (ringKrullDim_eq_of_ringEquiv (renameQuotientAlgEquiv K e I).toRingEquiv).symm.trans hdim
  obtain ⟨M, hMfield, hMdata⟩ :=
    bertini_exists_generic_projectiveSection_option Io hr hIoprime hIohom hIoX hIodim
  letI : Field M := hMfield
  obtain ⟨hMalgebra, hMdata⟩ := hMdata
  letI : Algebra K M := hMalgebra
  obtain ⟨hMclosed, hIoext, ℓ, J, hℓhom, hℓ, hJprime, hJhom, hJX, hTJ, hsat⟩ := hMdata
  letI : IsAlgClosed M := hMclosed
  letI : J.IsPrime := hJprime
  let b := renameEquiv M e.symm
  have hback : (Io.map (MvPolynomial.map (algebraMap K M))).map b =
      I.map (MvPolynomial.map (algebraMap K M)) := by
    change (Io.map (MvPolynomial.map (algebraMap K M))).map (renameEquiv M e.symm) = _
    rw [← bertini_coefficientExtension_map_renameEquiv,
      show Io.map (renameEquiv K e.symm) = I from bertini_map_renameEquiv_symm e I]
  have hTback : (Io.map (MvPolynomial.map (algebraMap K M)) ⊔ Ideal.span {ℓ}).map b =
      I.map (MvPolynomial.map (algebraMap K M)) ⊔ Ideal.span {b ℓ} := by
    rw [Ideal.map_sup, Ideal.map_span, Set.image_singleton, hback]
  refine ⟨M, inferInstance, inferInstance, hMclosed,
    coefficientExtension_isPrime_of_isAlgClosed I hprime,
    b ℓ, J.map b, ?_, ?_, inferInstance,
    map_renameEquiv_isHomogeneous e.symm J hJhom, ?_, ?_, ?_⟩
  · exact hℓhom.rename_isHomogeneous
  · intro h
    rw [← hback] at h
    exact hℓ ((Ideal.apply_mem_of_equiv_iff (f := b.toRingEquiv)).mp h)
  · exact ⟨e.symm none, bertini_X_not_mem_map_renameEquiv e.symm J none hJX⟩
  · rw [← hTback]
    exact Ideal.map_mono hTJ
  · intro F hF i
    obtain ⟨a, ha⟩ := bertini_coordinate_saturation_map_renameEquiv e.symm
      (Io.map (MvPolynomial.map (algebraMap K M)) ⊔ Ideal.span {ℓ}) J hsat F hF i
    refine ⟨a, ?_⟩
    rw [← hTback]
    exact ha

/-- The rational projective degree--span inequality, with no geometric
section-existence or degree--span input. -/
theorem rationalProjectiveDegreeSpan_internal :
    StandardAG.ProjectiveDegreeSpanInequality ℚ :=
  rationalProjectiveDegreeSpan_of_genericIntegralHyperplaneSections
    projectiveGenericIntegralHyperplaneSectionExists

end
end TranslatedDepthSeven
