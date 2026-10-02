import CubicTenVariables.FixedLeadingSurfaceHeightAlternativeChart
import CubicTenVariables.FixedLeadingSurfaceSingularCount
import TranslatedDepthSeven.PrimitiveBoundedHypersurfaceAlternative
import TranslatedDepthSeven.SurfaceProperCutProgressionBoxCount

/-!
# A degree-uniform coefficient-height alternative in the fixed leading family

Interpolation is applied after the fixed coordinate change. Either its
small equation cuts the actual surface properly, giving a linear count,
or the small primitive equation is a nonzero rational scalar multiple of
the whole original equation. All degree and coefficient thresholds below
depend only on d; no lower coefficient enters them.
-/
set_option autoImplicit false
set_option maxHeartbeats 3500000
noncomputable section
namespace CubicTenVariables.FixedLeadingSurfaceHeightAlternative
open MvPolynomial TranslatedDepthSeven Published
open FixedLeadingSurfaceCoordinateChoice FixedLeadingSurfaceCoordinateTransport
open FixedLeadingSurfaceHeightAlternativeChart FixedLeadingSurfaceSingularCount
attribute [local instance] MvPolynomial.gradedAlgebra

/-- Scaling the entire equation by a nonzero rational scalar preserves
each variable degree, including the packet's last-coordinate degree. -/
theorem degreeOf_C_mul_eq {σ K : Type*} [Field K]
    (F : MvPolynomial σ K) (s : K) (hs : s ≠ 0) (j : σ) :
    (C s * F).degreeOf j = F.degreeOf j := by
  apply Nat.le_antisymm (degreeOf_C_mul_le F j s)
  have hi : C s⁻¹ * (C s * F) = F := by
    rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ hs, map_one, one_mul]
  have hb := degreeOf_C_mul_le (C s * F) j s⁻¹
  rw [hi] at hb
  exact hb

theorem integer_zero_iff_of_rational_scalar {n : ℕ}
    (F P : MvPolynomial (Fin n) ℤ) (s : ℚ) (hs : s ≠ 0)
    (hscalar : map (Int.castRingHom ℚ) P = C s * map (Int.castRingHom ℚ) F)
    (x : IntVector n) : eval x P = 0 ↔ eval x F = 0 := by
  have he : ((eval x P : ℤ) : ℚ) = s * ((eval x F : ℤ) : ℚ) := by
    rw [← eval_map_intCast P x, hscalar, map_mul, eval_C, eval_map_intCast F x]
  constructor
  · intro hz
    have hmul : s * ((eval x F : ℤ) : ℚ) = 0 := by rw [← he, hz, Int.cast_zero]
    have hf := (mul_eq_zero.mp hmul).resolve_left hs
    exact Int.cast_injective (by simpa using hf)
  · intro hz
    have hp : ((eval x P : ℤ) : ℚ) = 0 := by rw [he, hz, Int.cast_zero, mul_zero]
    exact Int.cast_injective (by simpa using hp)

/-- Every conclusion is an actual property of P, its scalar and its
literal chart. This record is constructed, never taken as an input. -/
structure BoundedScalarReplacement (d H : ℕ)
    (F P : MvPolynomial (Fin 4) ℤ) (s : ℚ) : Prop where
  scalar_ne_zero : s ≠ 0
  equation_ne_zero : P ≠ 0
  primitive : IsPrimitiveIntegralMvPolynomial P
  homogeneous : P.IsHomogeneous d
  scalar_eq : map (Int.castRingHom ℚ) P = C s * map (Int.castRingHom ℚ) F
  coefficient_bound : ∀ μ, (P.coeff μ).natAbs ≤ H ^ heightExponent d
  chart_coefficient_bound : mvPolynomialCoefficientNatAbsMax
    (surfaceHypersurfaceFirstChartDehomogenize P) ≤ H ^ heightExponent d
  chart_degree_bound : (surfaceHypersurfaceFirstChartDehomogenize P).totalDegree ≤ d
  zero_iff : ∀ x : IntVector 4, eval x P = 0 ↔ eval x F = 0
  variable_degrees : ∀ j : Fin 4,
    (map (Int.castRingHom ℚ) P).degreeOf j = (map (Int.castRingHom ℚ) F).degreeOf j

/-- The replacement defines literally the same rational principal ideal.
This transfers the original prime, degree and normalization certificates. -/
theorem BoundedScalarReplacement.rationalIdeal_eq {d H : ℕ}
    {F P : MvPolynomial (Fin 4) ℤ} {s : ℚ}
    (h : BoundedScalarReplacement d H F P s) :
    Ideal.span {map (Int.castRingHom ℚ) P} =
      Ideal.span {map (Int.castRingHom ℚ) F} := by
  rw [h.scalar_eq]
  exact Ideal.span_singleton_mul_left_unit
    ((isUnit_iff_ne_zero.mpr h.scalar_ne_zero).map MvPolynomial.C) _

/-- The actual surface alternative, uniformly in coefficients, centers
and moduli. Both source height H and displacement radius B are explicit. -/
theorem small_scalar_equation_or_linear_progression_bound
    {d H B m : ℕ} (hm : 0 < m)
    (F : MvPolynomial (Fin 4) ℤ) (hF : F ≠ 0) (hFhom : F.IsHomogeneous d)
    (hprime : (Ideal.span {map (Int.castRingHom ℚ) F}).IsPrime)
    (hdegree : HasProjectiveDimensionDegree (Ideal.span {map (Int.castRingHom ℚ) F}) 2 d)
    (hH : max 1 (heightThreshold d) ≤ H)
    (u : IntVector 3) (S : Finset (IntVector 3))
    (hzero : ∀ z ∈ S, eval (progressionHomogeneousPoint u m z) F = 0)
    (hsource : ∀ z ∈ S, ∀ i, (progressionHomogeneousPoint u m z i).natAbs ≤ H)
    (hbox : ∀ z ∈ S, ∀ i, (z i).natAbs ≤ B) :
    S.card ≤ d * d * (2 * B + 1) ∨
      ∃ P : MvPolynomial (Fin 4) ℤ, ∃ s : ℚ, BoundedScalarReplacement d H F P s := by
  classical
  have hFQ : map (Int.castRingHom ℚ) F ≠ 0 := by
    intro hz
    exact hF (map_injective _ Int.cast_injective (by simpa only [map_zero] using hz))
  have hirr : Irreducible (map (Int.castRingHom ℚ) F) :=
    UniqueFactorizationMonoid.irreducible_iff_prime.mpr
      ((Ideal.span_singleton_prime hFQ).mp hprime)
  let Z := S.image (progressionHomogeneousPoint u m)
  obtain ⟨P, hP, hprimitive, hPhom, hPzero, hPcoeff, hcase⟩ :=
    exists_bounded_primitive_hypersurface_equation_or_proper_cut F hF hFhom hirr Z
      (by intro x hx; obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hx; exact hzero z hz)
      (by intro x hx; obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hx; exact hsource z hz)
  rcases hcase with hproper | ⟨⟨s, hs, hscalar⟩, _hclosure⟩
  · left
    have hIhom : (Ideal.span {map (Int.castRingHom ℚ) F}).IsHomogeneous
        (homogeneousSubmodule (Fin 4) ℚ) := by
      apply Ideal.homogeneous_span
      intro G hG
      exact ⟨d, (Set.mem_singleton_iff.mp hG).symm ▸ hFhom.map _⟩
    apply card_surface_progression_properCut_le hm _ hprime hIhom hdegree
      (map (Int.castRingHom ℚ) P) (hPhom.map _) hproper u S _ _ hbox
    · intro z hz
      have hle : Ideal.span {map (Int.castRingHom ℚ) F} ≤
          RingHom.ker (eval (fun i => (progressionHomogeneousPoint u m z i : ℚ))) := by
        apply Ideal.span_le.mpr
        intro G hG
        obtain rfl := Set.mem_singleton_iff.mp hG
        change eval _ (map (Int.castRingHom ℚ) F) = 0
        rw [eval_map_intCast, hzero z hz, Int.cast_zero]
      intro G hG
      exact hle hG
    · intro z hz
      rw [eval_map_intCast, hPzero _ (Finset.mem_image.mpr ⟨z, hz, rfl⟩), Int.cast_zero]
  · right
    have hcoeff : ∀ μ, (P.coeff μ).natAbs ≤ H ^ heightExponent d := by
      intro μ
      exact (hPcoeff μ).trans (by simpa using interpolation_bound_le_power hH)
    refine ⟨P, s, ⟨hs, hP, hprimitive, hPhom, hscalar, hcoeff, ?_, ?_, ?_, ?_⟩⟩
    · change mvPolynomialCoefficientNatAbsMax (standardDehomogenizationHom ℤ 3 P) ≤ _
      exact standardChart_coefficientMax_bound P hPhom hcoeff
    · change (standardDehomogenizationHom ℤ 3 P).totalDegree ≤ d
      exact standardChart_totalDegree_le P hPhom
    · exact integer_zero_iff_of_rational_scalar F P s hs hscalar
    · intro j
      rw [hscalar, degreeOf_C_mul_eq _ s hs]

/-- The fixed affine coordinate change commutes with the actual standard chart. -/
theorem standardChart_projectiveEquiv {R : Type*} [CommRing R]
    (a b : R) (F : MvPolynomial (Fin 4) R) :
    standardDehomogenizationHom R 3 (projectiveEquiv a b F) =
      coordinateEquiv a b (standardDehomogenizationHom R 3 F) := by
  have he : (standardDehomogenizationHom R 3).comp (projectiveEquiv a b).toRingHom =
      (coordinateEquiv a b).toRingHom.comp (standardDehomogenizationHom R 3) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [standardDehomogenizationHom, projectiveEquiv_apply, coordinateEquiv_apply]
    · intro i
      fin_cases i <;> norm_num [standardDehomogenizationHom, projectiveEquiv_apply,
        coordinateEquiv_apply, projectiveForms, FixedLeadingSurfaceCoordinateChoice.coordinateForms]
      all_goals simp only [show (1 : Fin 4) = (0 : Fin 3).succ by decide,
        show (2 : Fin 4) = (1 : Fin 3).succ by decide,
        show (3 : Fin 4) = (2 : Fin 3).succ by decide, Fin.cases_succ,
        bind₁_X_right, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]
  exact RingHom.congr_fun he F

theorem map_standardChart {R T : Type*} [CommRing R] [CommRing T]
    (φ : R →+* T) (F : MvPolynomial (Fin 4) R) :
    map φ (standardDehomogenizationHom R 3 F) =
      standardDehomogenizationHom T 3 (map φ F) := by
  exact (RingHom.congr_fun (standardDehomogenizationHom_comp_map 3 φ) F).symm

/-- The leading scalar is multiplied by s; it is never required to be integral. -/
theorem chart_scalar_leading_of_scalar_equation
    (F P : MvPolynomial (Fin 4) ℤ) (k : MvPolynomial (Fin 3) ℚ)
    (d : ℕ) (s c : ℚ)
    (hscalar : map (Int.castRingHom ℚ) P = C s * map (Int.castRingHom ℚ) F)
    (htop : map (Int.castRingHom ℚ)
      (homogeneousComponent d (standardDehomogenizationHom ℤ 3 F)) = C c * k) :
    map (Int.castRingHom ℚ)
      (homogeneousComponent d (standardDehomogenizationHom ℤ 3 P)) = C (s * c) * k := by
  have hC : standardDehomogenizationHom ℚ 3 (C s) = C s := by
    simp [standardDehomogenizationHom]
  rw [map_homogeneousComponent_boundary, map_standardChart, hscalar, map_mul, hC,
    homogeneousComponent_C_mul]
  have ht : homogeneousComponent d
      (standardDehomogenizationHom ℚ 3 (map (Int.castRingHom ℚ) F)) = C c * k := by
    rw [← map_standardChart, ← map_homogeneousComponent_boundary]
    exact htop
  rw [ht, ← mul_assoc, ← map_mul]

/-- The advertised alternative for every scalar member of the fixed
leading family, after its already chosen integral coordinates. -/
theorem fixed_leading_family_height_alternative
    {d H B m : ℕ} (hd : 0 < d) (hm : 0 < m)
    (k g : MvPolynomial (Fin 3) ℤ) (c : ℚ)
    (hirr : IsAbsolutelyIrreducible (map (Int.castRingHom ℚ) k)) (hc : c ≠ 0)
    (hdegree : g.totalDegree ≤ d)
    (htop : map (Int.castRingHom ℚ) (homogeneousComponent d g) =
      C c * map (Int.castRingHom ℚ) k)
    (a b : ℤ) (hH : max 1 (heightThreshold d) ≤ H)
    (u : IntVector 3) (S : Finset (IntVector 3))
    (hzero : ∀ z ∈ S, eval (progressionHomogeneousPoint u m z)
      (projectiveEquiv a b (homogenize d g)) = 0)
    (hsource : ∀ z ∈ S, ∀ i, (progressionHomogeneousPoint u m z i).natAbs ≤ H)
    (hbox : ∀ z ∈ S, ∀ i, (z i).natAbs ≤ B) :
    S.card ≤ d * d * (2 * B + 1) ∨
      ∃ P : MvPolynomial (Fin 4) ℤ, ∃ s : ℚ,
        BoundedScalarReplacement d H (projectiveEquiv a b (homogenize d g)) P s ∧
        s * c ≠ 0 ∧
        map (Int.castRingHom ℚ)
          (homogeneousComponent d (standardDehomogenizationHom ℤ 3 P)) =
            C (s * c) * coordinateEquiv (a : ℚ) (b : ℚ) (map (Int.castRingHom ℚ) k) := by
  obtain ⟨hF, hFhom, hprime, hdim⟩ := normalized_surface_certificate hd a b g hdegree
    (irreducible_actual_top k g c hirr hc htop)
  rcases small_scalar_equation_or_linear_progression_bound hm _ hF hFhom hprime hdim
      hH u S hzero hsource hbox with hsmall | ⟨P, s, hP⟩
  · exact Or.inl hsmall
  · right
    refine ⟨P, s, hP, mul_ne_zero hP.scalar_ne_zero hc, ?_⟩
    apply chart_scalar_leading_of_scalar_equation _ P _ d s c hP.scalar_eq
    rw [standardChart_projectiveEquiv, standardDehomogenizationHom_homogenize d g hdegree,
      map_homogeneousComponent_boundary, map_coordinateEquiv]
    apply scalar_leading_form_coordinateEquiv
    rw [← map_homogeneousComponent_boundary]
    exact htop

end CubicTenVariables.FixedLeadingSurfaceHeightAlternative
