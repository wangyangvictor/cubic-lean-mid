import TranslatedDepthSeven.FixedSurfacePacketMixedPrimeSumAuxiliary
import TranslatedDepthSeven.PrimeWeightedRange

/-!
# The actual large-prime range in the packet-plus-mixed auxiliary theorem

The mixed prime family is now the literal interval of primes above
`ceil (log H)` and at most `N`, after deleting the divisors of one displayed
certificate.  If `m*q` divides that certificate, the two disjointness
conditions needed by the determinant argument follow internally.
-/

namespace TranslatedDepthSeven
noncomputable section
open MvPolynomial Published
open scoped BigOperators
attribute [local instance] MvPolynomial.gradedAlgebra

set_option maxHeartbeats 1500000
set_option synthInstance.maxHeartbeats 200000

/-- Fixed-surface packet auxiliary with the mixed primes selected internally
from an actual weighted prime range. -/
theorem exists_fixedSurface_auxiliary_of_packetPrimeRange
    {d : ℕ} (hd : 0 < d)
    (I : Ideal (MvPolynomial (Fin 4) ℚ))
    (hprime : I.IsPrime)
    (hhom : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule _ ℚ))
    (hX : MvPolynomial.X 0 ∉ I)
    (hdegree : HasProjectiveDimensionDegree I 2 d)
    (F : MvPolynomial (Fin 4) ℤ) (K : ℝ) (hK : 0 < K) :
    ∃ b D A H₀ : ℕ, ∃ C : ℝ,
      1 ≤ D ∧ 2 ≤ A ∧ 2 ≤ H₀ ∧ 0 ≤ C ∧
      ∀ (k t s H B q m S N Aex Dex : ℕ)
        (u : Fin 3 → ℤ) (y : Fin S → Fin 3 → ℤ),
      H₀ ≤ H → 1 ≤ Real.log (H : ℝ) →
      ⌈Real.log (H : ℝ)⌉₊ ≤ N →
      0 < Dex → Dex ≤ H ^ Aex → m * q ∣ Dex →
      m ≠ 0 → 0 < q → Squarefree q →
      Fintype.card (Fin d × AffinePlaneMonomialIndex k) =
        affinePlaneMonomialCount t + s →
      0 < affinePlaneMonomialWeight t + (t + 1) * s →
      (∀ p ∈ PrimeWeightedRange.largePrimesAvoiding H N Dex,
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
              (Real.log (N : ℝ) - Real.log (Real.log (H : ℝ)) - C - Aex) -
            (Real.sqrt 2 * A / Real.sqrt K) *
              (((d * affinePlaneMonomialCount k : ℕ) : ℝ) *
                Real.sqrt ((d * affinePlaneMonomialCount k : ℕ) : ℝ)) -
            2 * (d * affinePlaneMonomialCount k : ℕ) *
              (Real.log 4 * (N : ℝ))) →
      ∃ Q : MvPolynomial (Fin 4) ℚ, Q.IsHomogeneous (b + k) ∧ Q ∉ I ∧
        ∀ j, MvPolynomial.eval
          (fun i => (progressionHomogeneousPoint u m (y j) i : ℚ)) Q = 0 := by
  classical
  obtain ⟨b, D, A, H₀, hD, hA, hH₀, haux⟩ :=
    exists_fixedSurface_auxiliary_of_packetMixedPrimeSum
      hd I hprime hhom hX hdegree F K hK
  obtain ⟨C, hC, hrange⟩ := PrimeWeightedRange.exists_largePrimeRange_estimates
  refine ⟨b, D, A, H₀, C, hD, hA, hH₀, hC, ?_⟩
  intro k t s H B q m S N Aex Dex u y hH hlogH hN hDex hDexHeight hmqdvd
    hm hqpos hq hcard hE hcount hsource hdisplacement hyF hgrad hlocal hlarge
  let P := PrimeWeightedRange.largePrimesAvoiding H N Dex
  have hP : ∀ p ∈ P, p.Prime := fun p hp =>
    (PrimeWeightedRange.prime_and_lower_bound_of_mem hp).1
  have hPlarge : ∀ p ∈ P, Real.log (H : ℝ) ≤ (p : ℝ) := fun p hp =>
    (PrimeWeightedRange.prime_and_lower_bound_of_mem hp).2
  have hPm : ∀ p ∈ P, ¬ p ∣ m := by
    intro p hp
    exact PrimeWeightedRange.not_dvd_factor_of_mem hp
      ((Nat.dvd_mul_right m q).trans hmqdvd)
  have hPq : ∀ p ∈ P, ¬ p ∣ q := by
    intro p hp
    exact PrimeWeightedRange.not_dvd_factor_of_mem hp
      ((Nat.dvd_mul_left q m).trans hmqdvd)
  obtain ⟨hweighted, hunweighted⟩ :=
    hrange H N Aex Dex hlogH hN hDex hDexHeight
  apply haux k t s H B q m S u y P hH hm hqpos hq hcard hE
    hP hPm hPq hPlarge hcount hsource hdisplacement hyF hgrad hlocal
  apply hlarge.trans_le
  have hcoeff : 0 ≤
      (2 * Real.sqrt 2 / 3) / Real.sqrt K *
        ((d * affinePlaneMonomialCount k : ℕ) : ℝ) ^ (3 / 2 : ℝ) := by
    positivity
  have hweighted' := mul_le_mul_of_nonneg_left hweighted hcoeff
  have hunweighted' := mul_le_mul_of_nonneg_left hunweighted
    (show 0 ≤ (2 : ℝ) * (d * affinePlaneMonomialCount k : ℕ) by positivity)
  dsimp only [P]
  linarith

end
end TranslatedDepthSeven
