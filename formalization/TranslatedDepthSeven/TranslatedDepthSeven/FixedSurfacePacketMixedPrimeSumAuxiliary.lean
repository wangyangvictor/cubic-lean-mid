import TranslatedDepthSeven.ProgressionNormalizationPacketMixedAuxiliary
import TranslatedDepthSeven.IntegralSurfaceNormalizationBlockExistence
import TranslatedDepthSeven.HypersurfaceOccupiedSmoothResidues
import TranslatedDepthSeven.HypersurfaceMixedResiduePrimeSum

/-!
# Fixed-surface auxiliary forms from one packet and the mixed-prime sum

One squarefree modulus supplies a common residue-disc determinant exponent.
A disjoint prime family supplies the sharp mixed-residue gain.  The final
hypothesis is a single logarithmic comparison with the literal archimedean
minor bound.
-/

namespace TranslatedDepthSeven
noncomputable section
open MvPolynomial Published
open scoped BigOperators
attribute [local instance] MvPolynomial.gradedAlgebra

set_option maxHeartbeats 1500000
set_option synthInstance.maxHeartbeats 200000

/-- Convert a logarithmic comparison into the packet-times-prime-power
integer threshold. -/
theorem lt_packetPrimePowerProduct_of_log_lt
    (U q E : ℕ) (P : Finset ℕ) (e : ℕ → ℕ)
    (hq : 0 < q) (hP : ∀ p ∈ P, p.Prime)
    (hlog : Real.log (U : ℝ) <
      (E : ℝ) * Real.log (q : ℝ) +
        ∑ p ∈ P, (e p : ℝ) * Real.log (p : ℝ)) :
    U < q ^ E * ∏ p ∈ P, p ^ e p := by
  have hprimeProduct : 0 < ∏ p ∈ P, p ^ e p :=
    Finset.prod_pos fun p hp => pow_pos (hP p hp).pos _
  have hproduct : 0 < q ^ E * ∏ p ∈ P, p ^ e p :=
    mul_pos (pow_pos hq _) hprimeProduct
  by_cases hU : U = 0
  · simpa only [hU] using hproduct
  have hUpos : (0 : ℝ) < U := by exact_mod_cast Nat.pos_of_ne_zero hU
  have hproductR : (0 : ℝ) < ((q ^ E * ∏ p ∈ P, p ^ e p : ℕ) : ℝ) := by
    exact_mod_cast hproduct
  have heq : Real.log ((q ^ E * ∏ p ∈ P, p ^ e p : ℕ) : ℝ) =
      (E : ℝ) * Real.log (q : ℝ) +
        ∑ p ∈ P, (e p : ℝ) * Real.log (p : ℝ) := by
    rw [Nat.cast_mul, Nat.cast_pow,
      Real.log_mul (pow_ne_zero _ (by exact_mod_cast hq.ne'))
        (by exact_mod_cast hprimeProduct.ne'),
      Real.log_pow, log_primePowerProduct_eq P e hP]
  rw [← heq] at hlog
  exact_mod_cast (Real.log_lt_log_iff hUpos hproductR).mp hlog

/-- A fixed surface supplies a proper auxiliary as soon as the packet gain
plus the sharp mixed-prime gain exceeds the explicit normalization-block
minor bound. -/
theorem exists_fixedSurface_auxiliary_of_packetMixedPrimeSum
    {d : ℕ} (hd : 0 < d)
    (I : Ideal (MvPolynomial (Fin 4) ℚ))
    (hprime : I.IsPrime)
    (hhom : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule _ ℚ))
    (hX : MvPolynomial.X 0 ∉ I)
    (hdegree : HasProjectiveDimensionDegree I 2 d)
    (F : MvPolynomial (Fin 4) ℤ) (K : ℝ) (hK : 0 < K) :
    ∃ b D A H₀ : ℕ, 1 ≤ D ∧ 2 ≤ A ∧ 2 ≤ H₀ ∧
      ∀ (k t s H B q m S : ℕ)
        (u : Fin 3 → ℤ) (y : Fin S → Fin 3 → ℤ) (P : Finset ℕ),
      H₀ ≤ H → m ≠ 0 → 0 < q → Squarefree q →
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
          (D * H ^ b) ^ (d * affinePlaneMonomialCount k) *
            (((d + 1) ^ 3) * B) ^ (d * affinePlaneMonomialWeight k) : ℕ) : ℝ) <
        (affinePlaneMonomialWeight t + (t + 1) * s : ℕ) *
            Real.log (q : ℝ) +
          (2 * Real.sqrt 2 / 3) / Real.sqrt K *
              ((d * affinePlaneMonomialCount k : ℕ) : ℝ) ^ (3 / 2 : ℝ) *
              (∑ p ∈ P, Real.log (p : ℝ) / (p : ℝ)) -
            (Real.sqrt 2 * A / Real.sqrt K) *
              (((d * affinePlaneMonomialCount k : ℕ) : ℝ) *
                Real.sqrt ((d * affinePlaneMonomialCount k : ℕ) : ℝ)) -
            2 * (d * affinePlaneMonomialCount k : ℕ) *
              (∑ p ∈ P, Real.log (p : ℝ))) →
      ∃ Q : MvPolynomial (Fin 4) ℚ, Q.IsHomogeneous (b + k) ∧ Q ∉ I ∧
        ∀ j, MvPolynomial.eval
          (fun i => (progressionHomogeneousPoint u m (y j) i : ℚ)) Q = 0 := by
  classical
  obtain ⟨b, D, L, G, hD, hL0, hL, hGhom, hLI, hGheight, hLheight⟩ :=
    exists_fixed_integral_surfaceNormalizationBlock I hprime hhom hX hdegree
  obtain ⟨A, H₀, hA, hH₀, hsum⟩ :=
    exists_hypersurface_mixedResidue_log_lower_bound F K hK
  refine ⟨b, D, A, H₀, hD, hA, hH₀, ?_⟩
  intro k t s H B q m S u y P hH hm hqpos hq hcard hE hP hPm hPq
    hlargeP hcount hsource hdisplacement hyF hgrad hlocal hlarge
  apply exists_progression_auxiliary_of_packet_mixedResidue_minors
    hd b k t s D H (((d + 1) ^ 3) * B) q m S hm hcard hE
    P hP hPm hPq I L hL hL0 G hGhom (hLI k) F u y hyF hq hlocal
  · intro j i
    exact hGheight H (by omega) _ (hsource j) i
  · intro j i
    apply hLheight B (progressionHomogeneousDirection (y j))
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
    have hbound := hsum H hH P hP hlargeP _ x hbox
      (fun j => hgrad (select j)) hclasses
    have hmixed :
        (2 * Real.sqrt 2 / 3) / Real.sqrt K *
              ((d * affinePlaneMonomialCount k : ℕ) : ℝ) ^ (3 / 2 : ℝ) *
              (∑ p ∈ P, Real.log (p : ℝ) / (p : ℝ)) -
            (Real.sqrt 2 * A / Real.sqrt K) *
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
    apply hlarge.trans_le
    linarith

end
end TranslatedDepthSeven
