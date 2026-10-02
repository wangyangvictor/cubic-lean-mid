import CubicTenVariables.FixedLeadingSurfacePersistentRootDegreeSplit
import TranslatedDepthSeven.BoundedDegreeRationalProjectiveCurveCountInternal
import TranslatedDepthSeven.FiniteProjectiveAffineRescalingInternal
import TranslatedDepthSeven.ProjectiveConjugateHilbertInternal

/-!
# The centered bounded-degree root-curve count without Pila

Galois-stable geometric curves descend to actual rational homogeneous
ideals. The residue-class change is a literal homogeneous polynomial-ring
automorphism, and the internal half-power determinant count applies to its
integral displacement points. Nonstable curves are bounded by their
intersection with a distinct conjugate. The constant precedes the curve,
residue class, center, radius and finite set.
-/

set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section

namespace CubicTenVariables.FixedLeadingSurfaceCenteredCurveCountInternal

open MvPolynomial TranslatedDepthSeven Published
attribute [local instance] MvPolynomial.gradedAlgebra

private theorem rationalChart_eq_cons {N : ℕ} (z : IntVector N) :
    rationalIntegralAffineChartPoint z = Fin.cons 1 (fun i => (z i : ℚ)) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i <;>
    simp [rationalIntegralAffineChartPoint, integralAffineChartVector]

private theorem eval_rescaled_at_displacement
    {N q : ℕ} (hq : 0 < q) (base z : IntVector N)
    (hz : IntVectorCongruent q z base)
    (f : MvPolynomial (Fin (N + 1)) ℚ) :
    eval (rationalIntegralAffineChartPoint (congruenceDisplacementOrZero q base z))
        (finHomogeneousAffinePolynomialChange (fun i => (base i : ℚ)) (q : ℚ)
          (by exact_mod_cast hq.ne') f) =
      eval (rationalIntegralAffineChartPoint z) f := by
  rw [rationalChart_eq_cons, eval_finHomogeneousAffinePolynomialChange_affine,
    rationalChart_eq_cons]
  have hevalPoint :
      (Fin.cons (1 : ℚ)
        (fun j => (base j : ℚ) + (q : ℚ) *
          (congruenceDisplacementOrZero q base z j : ℚ)) : Fin (N + 1) → ℚ) =
      (Fin.cons (1 : ℚ) (fun j => (z j : ℚ)) : Fin (N + 1) → ℚ) := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · simp only [Fin.cons_succ]
      exact_mod_cast (congruenceDisplacementOrZero_spec base z hz j).symm
  rw [hevalPoint]

theorem exists_uniform_qbarProjectiveCurve_centeredPacket_internal
    (N D : ℕ) (hN : 1 < N) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {q : ℕ}, 0 < q →
        ∀ (base : IntVector N)
          (Q : Ideal (MvPolynomial (Fin (N + 1)) Qbar)) (d : ℕ),
        Q.IsPrime →
        Q.IsHomogeneous (homogeneousSubmodule (Fin (N + 1)) Qbar) →
        HasProjectiveDimensionDegree Q 1 d → 2 ≤ d → d ≤ D →
        ∀ S : Finset (IntVector N), base ∈ S →
        (∀ z ∈ S,
          (fun i => (integralAffineChartVector z i : Qbar)) ∈ affineIdealZeroLocus Q) →
        (∀ z ∈ S, IntVectorCongruent q z base) →
        ∀ (center : RealVector N) (R : ℝ), 0 ≤ R →
        (∀ z ∈ S, ∀ i, |(z i : ℝ) - center i| ≤ R) →
          (S.card : ℝ) ≤ (D : ℝ) ^ 2 +
            C * (2 * R / (q : ℝ) + 2) ^ ((1 : ℝ) / 2 + ε) := by
  classical
  obtain ⟨C, hC, hcount⟩ :=
    exists_boundedDegree_rationalCurve_halfPower_count N D hN ε hε
  refine ⟨C, hC, ?_⟩
  intro q hq base Q d hQprime hQhom hQdegree hd hdD S hbase hzero hcong center R hR hbox
  let V : ℝ := 2 * R / (q : ℝ) + 2
  have hqReal : (0 : ℝ) < q := by exact_mod_cast hq
  have hdiv : 0 ≤ 2 * R / (q : ℝ) :=
    div_nonneg (mul_nonneg (by norm_num) hR) hqReal.le
  have hV : 1 ≤ V := by dsimp only [V]; linarith
  rcases conjugateIdeal_fixed_or_exists_distinct Q with hstable | ⟨g, hg⟩
  · obtain ⟨I, hIhom, hIQ⟩ :=
      rationalHomogeneousIdeal_descent_of_galoisInvariant Q hstable hQhom
    have hIdegree : HasProjectiveDimensionDegree I 1 d :=
      rationalHasProjectiveDimensionDegree_of_qbar_map_eq I Q hIQ hQprime hQdegree
    have hIprime : I.IsPrime :=
      rationalIdeal_isPrime_of_qbarCoefficientExtension_isPrime I (by rwa [hIQ])
    let e := finHomogeneousAffinePolynomialChange (fun i => (base i : ℚ)) (q : ℚ)
      (by exact_mod_cast hq.ne')
    let J := I.map e
    obtain ⟨hJprime, hJhom, hJdegree⟩ :=
      finHomogeneousAffinePolynomialChange_map_data
        (fun i => (base i : ℚ)) (q : ℚ) (by exact_mod_cast hq.ne')
        I hIprime hIhom hIdegree
    let Y := S.image (congruenceDisplacementOrZero q base)
    have hinj : Set.InjOn (congruenceDisplacementOrZero q base) (↑S : Set (IntVector N)) := by
      apply (congruenceDisplacementOrZero_injOn base).mono
      intro z hz
      exact hcong z hz
    have hYcard : Y.card = S.card := Finset.card_image_of_injOn hinj
    have hYzero : ∀ y ∈ Y, ∀ f ∈ J,
        eval (rationalIntegralAffineChartPoint y) f = 0 := by
      intro y hy
      obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hy
      have hzI : (rationalIntegralAffineChartPoint z) ∈ affineIdealZeroLocus I := by
        apply (rational_zero_of_ideal_iff_qbar_zero_of_extension
          I Q hIQ (rationalIntegralAffineChartPoint z)).2
        simpa [rationalIntegralAffineChartPoint] using hzero z hz
      change J ≤ RingHom.ker
        (MvPolynomial.eval (rationalIntegralAffineChartPoint (congruenceDisplacementOrZero q base z)))
      change I.map e ≤ _
      rw [Ideal.map_le_iff_le_comap]
      intro f hf
      rw [Ideal.mem_comap, RingHom.mem_ker]
      rw [eval_rescaled_at_displacement hq base z (hcong z hz)]
      exact hzI f hf
    have hYbox : ∀ y ∈ Y, ∀ i, |(y i : ℝ)| ≤ V := by
      intro y hy i
      obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hy
      have h := congruenceDisplacementOrZero_coordinate_bound
        hq base z (hcong z hz) (hbox z hz) (hbox base hbase) i
      dsimp only [V]
      linarith
    have hbound := hcount d hd hdD J hJprime hJhom hJdegree V hV Y hYzero hYbox
    rw [hYcard] at hbound
    exact hbound.trans (le_add_of_nonneg_left (sq_nonneg (D : ℝ)))
  · have hconjPrime : (conjugateIdeal g Q).IsPrime := conjugateIdeal_isPrime g Q hQprime
    have hconjHom : (conjugateIdeal g Q).IsHomogeneous
        (homogeneousSubmodule (Fin (N + 1)) Qbar) := conjugateIdeal_isHomogeneous g Q hQhom
    have hconjDegree : HasProjectiveDimensionDegree (conjugateIdeal g Q) 1 d :=
      qbarConjugatePreservesProjectiveDimensionDegree N 1 d g Q hQdegree
    have hintersection : ∀ z ∈ S,
        (fun i => (progressionHomogeneousPoint (0 : IntVector N) 1 z i : Qbar)) ∈
          affineIdealZeroLocus (Q ⊔ conjugateIdeal g Q) := by
      intro z hz
      rw [mem_affineIdealZeroLocus_iff_le_ker_aeval]
      apply sup_le
      · have hQle := hzero z hz
        rw [mem_affineIdealZeroLocus_iff_le_ker_aeval] at hQle
        simpa [progressionHomogeneousPoint, integralAffineChartVector] using hQle
      · have hQle := hzero z hz
        rw [mem_affineIdealZeroLocus_iff_le_ker_aeval] at hQle
        have hgQ := conjugateIdeal_le_rationalEvaluationKernel
          g Q (fun i => (integralAffineChartVector z i : ℚ)) hQle
        simpa [progressionHomogeneousPoint, integralAffineChartVector] using hgQ
    have hcard := card_geometricProgression_on_distinct_curves_le_degree_mul
      (K := Qbar) (N := N) (d := d) (e := d) (m := 1) (by omega)
      Q (conjugateIdeal g Q) hQprime hconjPrime hQhom hconjHom
      hQdegree hconjDegree hg.symm (0 : IntVector N) S hintersection
    have hdegree : (S.card : ℝ) ≤ (D : ℝ) ^ 2 := by
      calc
        (S.card : ℝ) ≤ ((d * d : ℕ) : ℝ) := by exact_mod_cast hcard
        _ = (d : ℝ) ^ 2 := by norm_num [pow_two]
        _ ≤ (D : ℝ) ^ 2 := by gcongr
    exact hdegree.trans (le_add_of_nonneg_right
      (mul_nonneg hC.le (Real.rpow_nonneg (by positivity) _)))

end CubicTenVariables.FixedLeadingSurfaceCenteredCurveCountInternal
