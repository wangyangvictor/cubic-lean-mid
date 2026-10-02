import CubicTenVariables.FixedLeadingSurfaceHeightAlternative
import CubicTenVariables.FixedLeadingFormGoodSurfaceCountReduction

/-!
# Removing coefficient height from the fixed-leading surface count

The remaining determinant estimate may be restricted to equations whose
coefficient height is a fixed power of the box radius. Interpolation either
already gives a linear point bound or produces a scalar equation with the
same integer zeros and the same fixed leading form. This is a reduction;
the bounded-coefficient counting estimate is still an explicit hypothesis.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section

namespace CubicTenVariables.FixedLeadingSurfaceCoefficientReduction

open MvPolynomial TranslatedDepthSeven Published
open FixedLeadingSurfaceCoordinateTransport FixedLeadingSurfaceSingularCount
open FixedLeadingSurfaceHeightAlternative FixedLeadingSurfaceHeightAlternativeChart
open FixedLeadingFormGoodSurfaceCountReduction AffineFourCountByParallelSlices

/-- The unsheared equation has the same concrete surface certificate. -/
theorem homogenized_surface_certificate
    {d : ℕ} (hd : 0 < d) (g : MvPolynomial (Fin 3) ℤ)
    (hdegree : g.totalDegree ≤ d)
    (htop : Irreducible (homogeneousComponent d (map (Int.castRingHom ℚ) g))) :
    let F := homogenize d g
    F ≠ 0 ∧ F.IsHomogeneous d ∧
      (Ideal.span {map (Int.castRingHom ℚ) F}).IsPrime ∧
      HasProjectiveDimensionDegree (Ideal.span {map (Int.castRingHom ℚ) F}) 2 d := by
  obtain ⟨hne, _, hp, _⟩ := normalized_surface_certificate hd 0 0 g hdegree htop
  have hF : homogenize d g ≠ 0 := by
    intro hz
    apply hne
    rw [hz, map_zero]
  have hFQ : map (Int.castRingHom ℚ) (homogenize d g) ≠ 0 := by
    exact fun hz => hF (map_injective _ Int.cast_injective (by simpa using hz))
  have hprime : (Ideal.span {map (Int.castRingHom ℚ) (homogenize d g)}).IsPrime := by
    letI : (Ideal.span {projectiveEquiv (0 : ℚ) 0
        (map (Int.castRingHom ℚ) (homogenize d g))}).IsPrime := by
      simpa only [map_projectiveEquiv, Int.cast_zero] using hp
    have hh := Ideal.map_isPrime_of_equiv (projectiveEquiv (0 : ℚ) 0).symm
      (I := Ideal.span {projectiveEquiv (0 : ℚ) 0
        (map (Int.castRingHom ℚ) (homogenize d g))})
    simpa only [Ideal.map_span, Set.image_singleton, AlgEquiv.symm_apply_apply,
      Int.cast_zero] using hh
  exact ⟨hF, homogenize_isHomogeneous d g, hprime,
    hasProjectiveDimensionDegree_principal_homogeneous _
      ((homogenize_isHomogeneous d g).map _) hFQ hd hprime⟩

/-- One small affine equation works for all integer points, rather than
only for the sample used to construct it. The fixed leading scalar survives. -/
theorem affine_small_scalar_equation_or_linear_bound
    {d H : ℕ} (hd : 0 < d)
    (k g : MvPolynomial (Fin 3) ℤ) (c : ℚ)
    (hirr : IsAbsolutelyIrreducible (map (Int.castRingHom ℚ) k)) (hc : c ≠ 0)
    (hdegree : g.totalDegree ≤ d)
    (htop : map (Int.castRingHom ℚ) (homogeneousComponent d g) =
      C c * map (Int.castRingHom ℚ) k)
    (hH : max 1 (heightThreshold d) ≤ H)
    (S : Finset (IntVector 3))
    (hzero : ∀ z ∈ S, eval z g = 0)
    (hbox : ∀ z ∈ S, ∀ i, (z i).natAbs ≤ H) :
    S.card ≤ d * d * (2 * H + 1) ∨
      ∃ (p : MvPolynomial (Fin 3) ℤ) (s : ℚ),
        s ≠ 0 ∧ p.totalDegree ≤ d ∧
        map (Int.castRingHom ℚ) p = C s * map (Int.castRingHom ℚ) g ∧
        mvPolynomialCoefficientNatAbsMax p ≤ H ^ heightExponent d ∧
        s * c ≠ 0 ∧
        map (Int.castRingHom ℚ) (homogeneousComponent d p) =
          C (s * c) * map (Int.castRingHom ℚ) k ∧
        (∀ z : IntVector 3, eval z p = 0 ↔ eval z g = 0) := by
  have hH1 : 1 ≤ H := le_trans (le_max_left _ _) hH
  obtain ⟨hF, hhom, hp, hdim⟩ := homogenized_surface_certificate hd g hdegree
    (irreducible_actual_top k g c hirr hc htop)
  have hpoint (z : IntVector 3) : progressionHomogeneousPoint 0 1 z = Fin.cases 1 z := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;>
      simp [TranslatedDepthSeven.progressionHomogeneousPoint]
  have hchart := standardDehomogenizationHom_homogenize d g hdegree
  have hzeroF : ∀ z ∈ S, eval (progressionHomogeneousPoint 0 1 z) (homogenize d g) = 0 := by
    intro z hz
    rw [hpoint, ← eval_standardDehomogenizationHom, hchart]
    exact hzero z hz
  have hsource : ∀ z ∈ S, ∀ i,
      (progressionHomogeneousPoint 0 1 z i).natAbs ≤ H := by
    intro z hz i
    rw [hpoint]
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa using hH1
    · exact hbox z hz j
  rcases small_scalar_equation_or_linear_progression_bound (by decide : 0 < 1)
      (homogenize d g) hF hhom hp hdim hH 0 S hzeroF hsource hbox with
      hsmall | ⟨P, s, hP⟩
  · exact Or.inl hsmall
  · right
    let p := standardDehomogenizationHom ℤ 3 P
    have hscalar : map (Int.castRingHom ℚ) p = C s * map (Int.castRingHom ℚ) g := by
      dsimp only [p]
      rw [map_standardChart, hP.scalar_eq, map_mul]
      have hC : standardDehomogenizationHom ℚ 3 (C s) = C s := by
        simp [standardDehomogenizationHom]
      rw [hC, ← map_standardChart, hchart]
    refine ⟨p, s, hP.scalar_ne_zero, hP.chart_degree_bound, hscalar,
      hP.chart_coefficient_bound, mul_ne_zero hP.scalar_ne_zero hc, ?_, ?_⟩
    · exact chart_scalar_leading_of_scalar_equation _ P _ d s c hP.scalar_eq
        (by rw [hchart]; exact htop)
    · exact integer_zero_iff_of_rational_scalar g p s hP.scalar_ne_zero hscalar

/-- At integer radii above a degree-only threshold, a polynomial-height
count suffices for the unrestricted coefficient family. -/
theorem nat_count_of_polynomial_height_count
    {d : ℕ} (hd : 0 < d) (k : MvPolynomial (Fin 3) ℤ)
    (hirr : IsAbsolutelyIrreducible (map (Int.castRingHom ℚ) k))
    (ε C₀ : ℝ) (hε : 0 ≤ ε) (hC₀ : 0 < C₀) (H₀ : ℕ)
    (hbounded : ∀ (g : MvPolynomial (Fin 3) ℤ) (c : ℚ), c ≠ 0 →
      g.totalDegree ≤ d →
      map (Int.castRingHom ℚ) (homogeneousComponent d g) = C c * map (Int.castRingHom ℚ) k →
      ∀ H : ℕ, max H₀ (max 1 (heightThreshold d)) ≤ H →
      mvPolynomialCoefficientNatAbsMax g ≤ H ^ heightExponent d →
      ∀ S : Finset (IntVector 3),
      (∀ z ∈ S, eval z g = 0) → (∀ z ∈ S, ∀ i, (z i).natAbs ≤ H) →
      (S.card : ℝ) ≤ C₀ * (H : ℝ) ^ (1 + ε))
    (g : MvPolynomial (Fin 3) ℤ) (c : ℚ) (hc : c ≠ 0)
    (hdegree : g.totalDegree ≤ d)
    (htop : map (Int.castRingHom ℚ) (homogeneousComponent d g) = C c * map (Int.castRingHom ℚ) k)
    (H : ℕ) (hH : max H₀ (max 1 (heightThreshold d)) ≤ H)
    (S : Finset (IntVector 3)) (hzero : ∀ z ∈ S, eval z g = 0)
    (hbox : ∀ z ∈ S, ∀ i, (z i).natAbs ≤ H) :
    (S.card : ℝ) ≤ (3 * (d : ℝ) ^ 2 + C₀) * (H : ℝ) ^ (1 + ε) := by
  have hbase : max 1 (heightThreshold d) ≤ H := le_trans (le_max_right _ _) hH
  have hH1 : 1 ≤ (H : ℝ) := by exact_mod_cast le_trans (le_max_left _ _) hbase
  have hpow : (H : ℝ) ≤ (H : ℝ) ^ (1 + ε) := by
    simpa using Real.rpow_le_rpow_of_exponent_le hH1 (by linarith : (1 : ℝ) ≤ 1 + ε)
  have hnonneg : 0 ≤ (H : ℝ) ^ (1 + ε) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  rcases affine_small_scalar_equation_or_linear_bound hd k g c hirr hc hdegree htop
      hbase S hzero hbox with hsmall | ⟨p, s, _hs, hdeg, _, hheight, hsc, htopP, hzeros⟩
  · have hsmallR : (S.card : ℝ) ≤ (d : ℝ) * d * (2 * H + 1) := by exact_mod_cast hsmall
    have hlin : (S.card : ℝ) ≤ 3 * (d : ℝ) ^ 2 * H := by nlinarith [sq_nonneg (d : ℝ)]
    calc
      (S.card : ℝ) ≤ 3 * (d : ℝ) ^ 2 * H := hlin
      _ ≤ 3 * (d : ℝ) ^ 2 * (H : ℝ) ^ (1 + ε) :=
        mul_le_mul_of_nonneg_left hpow (by positivity)
      _ ≤ (3 * (d : ℝ) ^ 2 + C₀) * (H : ℝ) ^ (1 + ε) :=
        mul_le_mul_of_nonneg_right (by linarith) hnonneg
  · exact (hbounded p (s * c) hsc hdeg htopP H hH hheight S
      (fun z hz => (hzeros z).mpr (hzero z hz)) hbox).trans
        (mul_le_mul_of_nonneg_right (by nlinarith [sq_nonneg (d : ℝ)]) hnonneg)

/-- The exact remaining surface endpoint follows once the bounded-height
estimate is proved. Constants and thresholds precede the varying equation;
the conclusion has arbitrary coefficients and every real radius B >= 1. -/
theorem fixedIntegralLeadingSurfaceBounds_of_polynomial_height_count
    {d : ℕ} (hd : 0 < d) (ε : ℝ) (hε : 0 ≤ ε)
    (hbounded : ∀ k : MvPolynomial (Fin 3) ℤ,
      k.IsHomogeneous d → IsAbsolutelyIrreducible (map (Int.castRingHom ℚ) k) →
      ∃ (C₀ : ℝ) (H₀ : ℕ), 0 < C₀ ∧
      ∀ (g : MvPolynomial (Fin 3) ℤ) (c : ℚ), c ≠ 0 → g.totalDegree ≤ d →
      map (Int.castRingHom ℚ) (homogeneousComponent d g) = C c * map (Int.castRingHom ℚ) k →
      ∀ H : ℕ, max H₀ (max 1 (heightThreshold d)) ≤ H →
      mvPolynomialCoefficientNatAbsMax g ≤ H ^ heightExponent d →
      ∀ S : Finset (IntVector 3),
      (∀ z ∈ S, eval z g = 0) → (∀ z ∈ S, ∀ i, (z i).natAbs ≤ H) →
      (S.card : ℝ) ≤ C₀ * (H : ℝ) ^ (1 + ε)) :
    FixedIntegralLeadingSurfaceBounds d ε := by
  intro k hk hirr
  obtain ⟨C₀, H₀, hC₀, hcount⟩ := hbounded k hk hirr
  let T := max H₀ (max 1 (heightThreshold d))
  let M : ℝ := (T : ℝ) + 2
  let C₁ : ℝ := 3 * (d : ℝ) ^ 2 + C₀
  have hM : 0 < M := by dsimp [M]; positivity
  have hC₁ : 0 < C₁ := by dsimp [C₁]; positivity
  refine ⟨C₁ * M ^ (1 + ε), mul_pos hC₁ (Real.rpow_pos_of_pos hM _), ?_⟩
  intro g c hc htop B hB
  let H : ℕ := max T ⌈B⌉₊
  let S := affineHypersurfaceIntegerPoints g B
  have hHB : B ≤ (H : ℝ) :=
    (Nat.le_ceil B).trans (by exact_mod_cast (le_max_right T ⌈B⌉₊))
  have hH : T ≤ H := le_max_left _ _
  have hzero : ∀ z ∈ S, eval z g = 0 := fun z hz =>
    ((mem_affineHypersurfaceIntegerPoints_iff g B z).mp hz).2
  have hbox : ∀ z ∈ S, ∀ i, (z i).natAbs ≤ H := by
    intro z hz i
    have hh := ((mem_affineHypersurfaceIntegerPoints_iff g B z).mp hz).1 i
    have ha : ((z i).natAbs : ℝ) ≤ (H : ℝ) := by simpa using hh.trans hHB
    exact_mod_cast ha
  have hb := nat_count_of_polynomial_height_count hd k hirr ε C₀ hε hC₀ H₀ hcount
    g c hc (totalDegree_eq_of_isTopHomogeneousPart htop).le htop.1.symm H hH S hzero hbox
  have hB0 : 0 ≤ B := by linarith
  have hHupper : (H : ℝ) ≤ M * B := by
    dsimp only [H, M]
    rw [Nat.cast_max]
    apply max_le
    · have hT0 : 0 ≤ (T : ℝ) := Nat.cast_nonneg _
      nlinarith
    · have hh := Nat.ceil_lt_add_one (show 0 ≤ B from hB0)
      have hT0 : 0 ≤ (T : ℝ) := Nat.cast_nonneg _
      nlinarith
  calc
    ((affineHypersurfaceIntegerPoints g B).card : ℝ)
        ≤ C₁ * (H : ℝ) ^ (1 + ε) := hb
    _ ≤ C₁ * (M * B) ^ (1 + ε) := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (Nat.cast_nonneg _) hHupper (by linarith)) hC₁.le
    _ = (C₁ * M ^ (1 + ε)) * B ^ (1 + ε) := by
      rw [Real.mul_rpow hM.le hB0]
      ring

end CubicTenVariables.FixedLeadingSurfaceCoefficientReduction
