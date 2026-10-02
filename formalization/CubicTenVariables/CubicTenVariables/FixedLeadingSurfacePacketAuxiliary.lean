import CubicTenVariables.FixedLeadingSurfaceNormalizationBlock
import CubicTenVariables.FixedDegreeGradientPrimeSum
import TranslatedDepthSeven.FixedSurfacePacketMixedPrimeSumAuxiliary

/-!
# Actual packet auxiliaries with fixed normalization and gradient constants

The auxiliary degree offset is exactly d-1, the normalization height constant
is one, and the mixed-prime loss uses exponent e+d+2. The degree-only height
threshold is chosen before the equation. The hypotheses retain the actual
finite-field point counts, smoothness, packet divisibility, coefficient
height, and the displayed numerical comparison; none is silently assumed.
-/

set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section

namespace CubicTenVariables.FixedLeadingSurfacePacketAuxiliary
open MvPolynomial TranslatedDepthSeven
open FixedLeadingSurfaceNormalizationBlock FixedDegreeGradientPrimeSum
open scoped BigOperators

/-- The literal determinant construction with constants independent of the
varying lower coefficients, once coefficient growth is bounded by H^e. -/
theorem exists_fixedCoordinate_auxiliary_of_packetMixedPrimeSum
    {d e : ℕ} (hd : 0 < d)
    (F : MvPolynomial (Fin 4) ℤ)
    (hvariable : (map (Int.castRingHom ℚ) F).degreeOf 3 = d)
    (hchartDegree : (surfaceHypersurfaceFirstChartDehomogenize F).totalDegree ≤ d)
    (K : ℝ) (hK : 0 < K) :
      ∀ (k t s H B q m S : ℕ)
        (u : Fin 3 → ℤ) (y : Fin S → Fin 3 → ℤ) (P : Finset ℕ),
      max 2 ((d + 1) ^ 3 * d) ≤ H →
      mvPolynomialCoefficientNatAbsMax (surfaceHypersurfaceFirstChartDehomogenize F) ≤ H ^ e →
      m ≠ 0 → 0 < q → Squarefree q →
      Fintype.card (Fin d × AffinePlaneMonomialIndex k) =
        affinePlaneMonomialCount t + s →
      0 < affinePlaneMonomialWeight t + (t + 1) * s →
      (∀ p ∈ P, p.Prime) →
      (∀ p ∈ P, ¬ p ∣ m) →
      (∀ p ∈ P, ¬ p ∣ q) →
      (∀ p ∈ P, Real.log (H : ℝ) ≤ (p : ℝ)) →
      (∀ p ∈ P,
        (Nat.card (SurfaceReductionZeroPoint p
          (surfaceHypersurfaceFirstChartDehomogenize F)) : ℝ) ≤
            K * (p : ℝ) ^ 2) →
      (∀ j i, (progressionHomogeneousPoint u m (y j) i).natAbs ≤ H) →
      (∀ j i, (y j i).natAbs ≤ B) →
      (∀ j, MvPolynomial.eval (progressionHomogeneousPoint u m (y j)) F = 0) →
      (∀ j, ∃ v, MvPolynomial.eval (fun i => u i + (m : ℤ) * y j i)
        (MvPolynomial.pderiv v
          (surfaceHypersurfaceFirstChartDehomogenize F)) ≠ 0) →
      (∀ p, p.Prime → p ∣ q → ¬ p ∣ m ∧
        ∃ (z : Fin 3 → ℤ) (v : Fin 3),
          (∀ j i, (p : ℤ) ∣ y j i - z i) ∧
          (MvPolynomial.eval (fun i => u i + (m : ℤ) * z i)
            (MvPolynomial.pderiv v
              (surfaceHypersurfaceFirstChartDehomogenize F)) : ZMod p) ≠ 0) →
      (Real.log (((d * affinePlaneMonomialCount k).factorial *
          (H ^ (d - 1)) ^ (d * affinePlaneMonomialCount k) *
            B ^ (d * affinePlaneMonomialWeight k) : ℕ) : ℝ) <
        (affinePlaneMonomialWeight t + (t + 1) * s : ℕ) *
            Real.log (q : ℝ) +
          (2 * Real.sqrt 2 / 3) / Real.sqrt K *
              ((d * affinePlaneMonomialCount k : ℕ) : ℝ) ^ (3 / 2 : ℝ) *
              (∑ p ∈ P, Real.log (p : ℝ) / (p : ℝ)) -
            (Real.sqrt 2 * (e + d + 2 : ℕ) / Real.sqrt K) *
              (((d * affinePlaneMonomialCount k : ℕ) : ℝ) *
                Real.sqrt ((d * affinePlaneMonomialCount k : ℕ) : ℝ)) -
            2 * (d * affinePlaneMonomialCount k : ℕ) *
              (∑ p ∈ P, Real.log (p : ℝ))) →
      ∃ Q : MvPolynomial (Fin 4) ℚ, Q.IsHomogeneous (d - 1 + k) ∧ Q ∉ Ideal.span {map (Int.castRingHom ℚ) F} ∧
        ∀ j, MvPolynomial.eval
          (fun i => (progressionHomogeneousPoint u m (y j) i : ℚ)) Q = 0 := by
  classical
  intro k t s H B q m S u y P hH hcoeff hm hqpos hq hcard hE hP hPm hPq
    hlargeP hcount hsource hdisplacement hyF hgrad hlocal hlarge
  apply exists_progression_auxiliary_of_packet_mixedResidue_minors
    hd (d - 1) k t s 1 H B q m S hm hcard hE
    P hP hPm hPq (Ideal.span {map (Int.castRingHom ℚ) F})
      coordinateForms coordinateForms_isHomogeneous coordinateForms_first
      (auxiliaryForms d) (auxiliaryForms_isHomogeneous d)
      (linearIndependent_fixed_coordinate_block d k (map (Int.castRingHom ℚ) F) hvariable)
      F u y hyF hq hlocal
  · intro j i
    simpa only [one_mul] using auxiliaryForms_eval_natAbs_le d H _ (hsource j) i
  · intro j i
    apply coordinateForms_eval_natAbs_le B (progressionHomogeneousDirection (y j))
    intro a
    refine Fin.cases ?_ (fun a => ?_) a
    · simp [progressionHomogeneousDirection]
    · exact hdisplacement j a
  · intro select hinj
    let x : Fin d × AffinePlaneMonomialIndex k → Fin 3 → ℤ :=
      fun j i => u i + (m : ℤ) * y (select j) i
    have hbox : ∀ j i, (x j i).natAbs ≤ H := by
      intro j i
      exact hsource (select j) i.succ
    have hzero : ∀ j, MvPolynomial.eval (x j)
        (surfaceHypersurfaceFirstChartDehomogenize F) = 0 := by
      intro j
      rw [surfaceHypersurfaceFirstChart_eval]
      exact hyF (select j)
    have hclasses : ∀ p ∈ P,
        (Fintype.card (SurfaceOccupiedSmoothResidueClass p
          (surfaceHypersurfaceFirstChartDehomogenize F) x) : ℝ) ≤
            K * (p : ℝ) ^ 2 := by
      intro p hp
      have hinc := card_occupiedSmoothSurfaceResidues_le_zeroPoints p
        (hP p hp).ne_zero (surfaceHypersurfaceFirstChartDehomogenize F) x hzero
      have hincR :
          (Fintype.card (SurfaceOccupiedSmoothResidueClass p
            (surfaceHypersurfaceFirstChartDehomogenize F) x) : ℝ) ≤
          (Nat.card (SurfaceReductionZeroPoint p
            (surfaceHypersurfaceFirstChartDehomogenize F)) : ℝ) := by
        exact_mod_cast hinc
      exact hincR.trans (hcount p hp)
    have hbound := mixedResidue_log_lower_bound_uniform_height F hH hchartDegree hcoeff
      K hK P hP hlargeP x hbox (fun j => hgrad (select j)) hclasses
    have hmixed :
        (2 * Real.sqrt 2 / 3) / Real.sqrt K *
              ((d * affinePlaneMonomialCount k : ℕ) : ℝ) ^ (3 / 2 : ℝ) *
              (∑ p ∈ P, Real.log (p : ℝ) / (p : ℝ)) -
            (Real.sqrt 2 * (e + d + 2 : ℕ) / Real.sqrt K) *
              (((d * affinePlaneMonomialCount k : ℕ) : ℝ) *
                Real.sqrt ((d * affinePlaneMonomialCount k : ℕ) : ℝ)) -
            2 * (d * affinePlaneMonomialCount k : ℕ) *
              (∑ p ∈ P, Real.log (p : ℝ)) ≤
          ∑ p ∈ P,
            (progressionHypersurfaceSmoothResidueExponent p F u m
              (y ∘ select) : ℝ) * Real.log (p : ℝ) := by
      simpa only [Fintype.card_prod, Fintype.card_fin,
        card_affinePlaneMonomialIndex,
        progressionHypersurfaceSmoothResidueExponent, Function.comp_apply, x] using hbound
    apply lt_packetPrimePowerProduct_of_log_lt _ q
      (affinePlaneMonomialWeight t + (t + 1) * s) P
      (fun p => progressionHypersurfaceSmoothResidueExponent p F u m (y ∘ select))
      hqpos hP
    simp only [one_mul]
    apply hlarge.trans_le
    linarith


end CubicTenVariables.FixedLeadingSurfacePacketAuxiliary
