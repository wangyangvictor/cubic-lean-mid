import TranslatedDepthSeven.ProjectiveBertiniGenericRegularity
import TranslatedDepthSeven.ProjectiveBertiniIncidenceProjectiveChart
import TranslatedDepthSeven.DehomogenizationBaseChange
import TranslatedDepthSeven.CoefficientExtensionHomogeneousIdeal
import TranslatedDepthSeven.ProjectiveBertiniGenericGeometricDomain

/-! # The homogeneous generic marked section and its actual affine chart

Dehomogenization identifies the homogeneous generic equation with the
marked affine generic equation. Primality of that actual affine chart,
together with the proved regularity on the coordinate-difference charts,
produces a prime homogeneous section with saturation at every coordinate.
-/

namespace TranslatedDepthSeven
noncomputable section
open MvPolynomial
attribute [local instance] MvPolynomial.gradedAlgebra
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 500000

variable {K : Type*} [Field K] {N : ℕ}

def bertiniProjectiveMarkedCoefficients (z : Fin N → K) (i : Fin N) :
    MvPolynomial (Option (Fin N)) K :=
  X (some i) - C (z i) * X none

def bertiniGenericProjectiveMarkedHyperplane (z : Fin N → K) :
    MvPolynomial (Option (Fin N)) (MvPolynomial (Fin N) K) :=
  bertiniCoefficientHyperplane (bertiniProjectiveMarkedCoefficients z)

def bertiniGenericProjectiveMarkedIdeal {M : Type*} [Field M]
    (φ : MvPolynomial (Fin N) K →+* M)
    (I : Ideal (MvPolynomial (Option (Fin N)) K)) (z : Fin N → K) :
    Ideal (MvPolynomial (Option (Fin N)) M) :=
  I.map (MvPolynomial.map (φ.comp C)) ⊔
    Ideal.span {MvPolynomial.map φ (bertiniGenericProjectiveMarkedHyperplane z)}

theorem bertiniGenericProjectiveMarkedHyperplane_isHomogeneous (z : Fin N → K) :
    (bertiniGenericProjectiveMarkedHyperplane z).IsHomogeneous 1 := by
  apply MvPolynomial.IsHomogeneous.sum
  intro i hi
  exact (isHomogeneous_C _ _).mul
    (((isHomogeneous_X K (some i)).sub (isHomogeneous_C_mul_X (z i) none)).map C)

theorem bertiniGenericProjectiveMarkedHyperplane_dehomogenization (z : Fin N → K) :
    multivariateDehomogenization (bertiniGenericProjectiveMarkedHyperplane z) =
      bertiniGenericMarkedHyperplane z := by
  simp [bertiniGenericProjectiveMarkedHyperplane, bertiniCoefficientHyperplane,
    bertiniProjectiveMarkedCoefficients, bertiniGenericMarkedHyperplane,
    multivariateDehomogenization]

/-- Literal equality of the affine chart ideal with the generic marked
affine ideal; it commutes with every supplied coefficient homomorphism. -/
theorem bertiniGenericProjectiveMarkedIdeal_dehomogenization
    {M : Type*} [Field M] (φ : MvPolynomial (Fin N) K →+* M)
    (I : Ideal (MvPolynomial (Option (Fin N)) K)) (z : Fin N → K) :
    (bertiniGenericProjectiveMarkedIdeal φ I z).map
        multivariateDehomogenization.toRingHom =
      (I.map multivariateDehomogenization.toRingHom).map (MvPolynomial.map (φ.comp C)) ⊔
        Ideal.span {MvPolynomial.map φ (bertiniGenericMarkedHyperplane z)} := by
  have hH : multivariateDehomogenization
      (MvPolynomial.map φ (bertiniGenericProjectiveMarkedHyperplane z)) =
      MvPolynomial.map φ (bertiniGenericMarkedHyperplane z) := by
    rw [show multivariateDehomogenization
        (MvPolynomial.map φ (bertiniGenericProjectiveMarkedHyperplane z)) =
        MvPolynomial.map φ
          (multivariateDehomogenization (bertiniGenericProjectiveMarkedHyperplane z)) from
      DFunLike.congr_fun (multivariateDehomogenization_comp_map φ)
        (bertiniGenericProjectiveMarkedHyperplane z)]
    rw [bertiniGenericProjectiveMarkedHyperplane_dehomogenization]
  rw [bertiniGenericProjectiveMarkedIdeal, Ideal.map_sup,
    map_dehomogenization_map_eq_map_map_dehomogenization,
    Ideal.map_span, Set.image_singleton]
  exact congrArg (fun p =>
    (I.map multivariateDehomogenization.toRingHom).map (MvPolynomial.map (φ.comp C)) ⊔
      Ideal.span {p}) hH

theorem bertiniGenericProjectiveMarkedIdeal_isHomogeneous
    {M : Type*} [Field M] (φ : MvPolynomial (Fin N) K →+* M)
    (I : Ideal (MvPolynomial (Option (Fin N)) K))
    (hI : I.IsHomogeneous (homogeneousSubmodule (Option (Fin N)) K))
    (z : Fin N → K) :
    (bertiniGenericProjectiveMarkedIdeal φ I z).IsHomogeneous
      (homogeneousSubmodule (Option (Fin N)) M) := by
  apply (isHomogeneous_map_mvPolynomialMap (φ.comp C) I hI).sup
  apply Ideal.homogeneous_span
  intro p hp
  obtain rfl := Set.mem_singleton_iff.mp hp
  exact ⟨1, (bertiniGenericProjectiveMarkedHyperplane_isHomogeneous z).map φ⟩

/-- The prime affine generic chart has a nonempty homogeneous prime closure,
and the original linear-section ideal has the same saturation at every
projective coordinate. The affine-chart primality is the actual ideal
statement supplied by the generic marked incidence construction. -/
theorem bertiniGenericProjectiveMarkedIdeal_exists_prime_saturation
    (L : Type*) [Field L] [Algebra (MvPolynomial (Fin N) K) L]
    [IsFractionRing (MvPolynomial (Fin N) K) L]
    (M : Type*) [Field M] [Algebra L M]
    (I : Ideal (MvPolynomial (Option (Fin N)) K)) (hprime : I.IsPrime)
    (hI : I.IsHomogeneous (homogeneousSubmodule (Option (Fin N)) K))
    (hX : X (none : Option (Fin N)) ∉ I) (z : Fin N → K)
    (hchart :
      ((I.map multivariateDehomogenization.toRingHom).map
          (MvPolynomial.map (((algebraMap L M).comp
            (algebraMap (MvPolynomial (Fin N) K) L)).comp C)) ⊔
        Ideal.span {MvPolynomial.map ((algebraMap L M).comp
          (algebraMap (MvPolynomial (Fin N) K) L))
          (bertiniGenericMarkedHyperplane z)}).IsPrime) :
    let φ := (algebraMap L M).comp (algebraMap (MvPolynomial (Fin N) K) L)
    let T := bertiniGenericProjectiveMarkedIdeal φ I z
    ∃ J : Ideal (MvPolynomial (Option (Fin N)) M),
      J.IsPrime ∧ J.IsHomogeneous (homogeneousSubmodule (Option (Fin N)) M) ∧
      T ≤ J ∧ X (none : Option (Fin N)) ∉ J ∧
      ∀ f ∈ J, ∀ i : Option (Fin N), ∃ a : ℕ, X i ^ a * f ∈ T := by
  intro φ T
  letI : I.IsPrime := hprime
  have hT : T.IsHomogeneous (homogeneousSubmodule (Option (Fin N)) M) :=
    bertiniGenericProjectiveMarkedIdeal_isHomogeneous φ I hI z
  have hTchart : (T.map multivariateDehomogenization.toRingHom).IsPrime := by
    change ((bertiniGenericProjectiveMarkedIdeal φ I z).map _).IsPrime
    rw [bertiniGenericProjectiveMarkedIdeal_dehomogenization]
    exact hchart
  obtain ⟨J, hJprime, hJhom, hTJ, hJX, hsat⟩ :=
    bertini_exists_prime_homogeneous_chart_saturation T hT hTchart
  let b (i : Fin N) : MvPolynomial (Option (Fin N)) M ⧸ T :=
    Ideal.Quotient.mk T (MvPolynomial.map (φ.comp C) (bertiniProjectiveMarkedCoefficients z i))
  have hreg : ∀ i, b i = 0 ∨ IsRegular
      (algebraMap (MvPolynomial (Option (Fin N)) M ⧸ T) (Localization.Away (b i))
        (Ideal.Quotient.mk T (X none))) := by
    have h := bertini_generic_coefficient_regular_overlaps_after_fieldExtension
      L M I (bertiniProjectiveMarkedCoefficients z) (X none) hX
    simpa only [MvPolynomial.map_X] using h
  have hcoords (i : Fin N) : Ideal.Quotient.mk T (X (some i)) ∈
      Ideal.span ({Ideal.Quotient.mk T (X none), b i} :
        Set (MvPolynomial (Option (Fin N)) M ⧸ T)) := by
    let S := Ideal.span ({Ideal.Quotient.mk T (X none), b i} :
      Set (MvPolynomial (Option (Fin N)) M ⧸ T))
    have ha : Ideal.Quotient.mk T (X none) ∈ S := Ideal.subset_span (by simp)
    have hb : b i ∈ S := Ideal.subset_span (by simp)
    have heq : Ideal.Quotient.mk T (X (some i)) =
        b i + Ideal.Quotient.mk T (C ((φ.comp C) (z i))) *
          Ideal.Quotient.mk T (X none) := by
      dsimp [b, bertiniProjectiveMarkedCoefficients]
      simp only [map_sub, map_mul, MvPolynomial.map_X, MvPolynomial.map_C,
        RingHom.comp_apply]
      ring
    rw [heq]
    exact S.add_mem hb (S.mul_mem_left _ ha)
  have hsatSome := bertini_coordinate_saturation_of_regular_overlaps T J (X none)
    (fun i : Fin N => X (some i)) b hcoords hsat hreg
  refine ⟨J, hJprime, hJhom, hTJ, hJX, ?_⟩
  intro f hf i
  cases i with
  | none => exact hsat f hf
  | some i => exact hsatSome f hf i

/-- A single marked point gives prime homogeneous generic sections over
every further extension of the parameter function field. All local smooth
chart and incidence-integrality hypotheses have been constructed internally;
the remaining dimension hypothesis refers to the actual affine chart. -/
theorem exists_bertiniGenericProjectiveMarked_prime_saturation_of_affine_dimension
    [CharZero K] [IsAlgClosed K] {r : ℕ}
    (I : Ideal (MvPolynomial (Option (Fin N)) K)) (hprime : I.IsPrime)
    (hI : I.IsHomogeneous (homogeneousSubmodule (Option (Fin N)) K))
    (hX : X (none : Option (Fin N)) ∉ I)
    (hdim : ringKrullDim (MvPolynomial (Fin N) K ⧸
      I.map multivariateDehomogenization.toRingHom) = (r : WithBot ℕ∞))
    (hr : 2 ≤ r) :
    ∃ (z : Fin N → K)
      (_hz : I.map multivariateDehomogenization.toRingHom ≤ RingHom.ker (aeval z).toRingHom),
      ∀ (L : Type*) [Field L] [Algebra (MvPolynomial (Fin N) K) L]
        [IsFractionRing (MvPolynomial (Fin N) K) L]
        (M : Type*) [Field M] [Algebra L M],
      let φ := (algebraMap L M).comp (algebraMap (MvPolynomial (Fin N) K) L)
      let T := bertiniGenericProjectiveMarkedIdeal φ I z
      ∃ J : Ideal (MvPolynomial (Option (Fin N)) M),
        J.IsPrime ∧ J.IsHomogeneous (homogeneousSubmodule (Option (Fin N)) M) ∧
        T ≤ J ∧ X (none : Option (Fin N)) ∉ J ∧
        ∀ f ∈ J, ∀ i : Option (Fin N), ∃ a : ℕ, X i ^ a * f ∈ T := by
  have hJ := map_multivariateDehomogenization_isPrime I hI hprime hX
  obtain ⟨z, hz, hdomain⟩ :=
    exists_bertiniGenericMarkedQuotient_geometricDomain_of_primeAffine_dimension
      (I.map multivariateDehomogenization.toRingHom) hJ hdim hr
  refine ⟨z, hz, ?_⟩
  intro L _ _ _ M _ _
  apply bertiniGenericProjectiveMarkedIdeal_exists_prime_saturation L M I hprime hI hX z
  exact (Ideal.Quotient.isDomain_iff_prime _).mp (hdomain L M)

end
end TranslatedDepthSeven
