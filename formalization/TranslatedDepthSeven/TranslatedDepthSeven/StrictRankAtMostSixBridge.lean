import TranslatedDepthSeven.StrictProjectiveInputBridge
import TranslatedDepthSeven.RankAtMostSixConcreteCount
import TranslatedDepthSeven.IntegralRationalJacobianRank
import TranslatedDepthSeven.SurfaceReservoirTangentBridge

/-!
# The literal low-rank cell of the strict normalized count

This file attaches the intrinsic Jacobian-exceptional estimate to the exact
finite set occurring in the strict theorem.  The result is deliberately
stated with its presently available fifth power; improving this single
branch to the required fourth power plus epsilon is a separate geometric
step, not hidden here.
-/

namespace TranslatedDepthSeven

noncomputable section

open MvPolynomial Published

attribute [local instance] MvPolynomial.gradedAlgebra
local instance strictLowRankClassicalDecidablePred {A : Type*} (q : A → Prop) :
    DecidablePred q := Classical.decPred q

/-- The rational affine image of every normalized point annihilates the
coefficient extension of each displayed integral equation. -/
theorem depthSevenNormalized_mem_rationalizedCommonZeroLocus
    (p : Parameters) (x₀ : IntVector 13)
    (equations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    {z : IntVector 13}
    (hz : z ∈ depthSevenNormalizedDisplacementFinset p x₀ equations CF) :
    (fun i ↦ (integralAffineMap x₀ z p.m i : ℚ)) ∈
      finiteAffineCommonZeroLocus
        (rationalizedEquationFinset equations) := by
  intro f hf
  obtain ⟨g, hg, rfl⟩ := Finset.mem_image.mp hf
  rw [eval_map_intCast,
    depthSevenNormalized_eval_eq_zero p x₀ equations CF hz hg,
    Int.cast_zero]

/-- Inside the normalized point set, the integral definition of the
rank-at-most-six cell is exactly the rational augmented-equation filter. -/
theorem depthSevenNormalizedRankAtMostSixFinset_eq_rationalFilter
    (p : Parameters) (x₀ : IntVector 13)
    (equations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ) :
    depthSevenNormalizedRankAtMostSixFinset p x₀ equations CF =
      (depthSevenNormalizedDisplacementFinset p x₀ equations CF).filter
        fun z ↦
          (fun i ↦ (integralAffineMap x₀ z p.m i : ℚ)) ∈
            finiteAffineCommonZeroLocus
              (depthSevenJacobianExceptionalEquationFinset
                (rationalizedEquationFinset equations)) := by
  classical
  ext z
  rw [mem_depthSevenNormalizedRankAtMostSixFinset_iff,
    Finset.mem_filter]
  constructor
  · rintro ⟨hz, hrank⟩
    refine ⟨hz, (mem_finiteAffineCommonZeroLocus_exceptional_iff
      (rationalizedEquationFinset equations) _).mpr ⟨?_, ?_⟩⟩
    · exact depthSevenNormalized_mem_rationalizedCommonZeroLocus
        p x₀ equations CF hz
    · exact (rationalized_rankAtMostSix_iff_not_integralRegular
        equations (integralAffineMap x₀ z p.m)).mpr hrank
  · rintro ⟨hz, hexceptional⟩
    refine ⟨hz, ?_⟩
    have hrank := (mem_finiteAffineCommonZeroLocus_exceptional_iff
      (rationalizedEquationFinset equations) _).mp hexceptional |>.2
    exact (rationalized_rankAtMostSix_iff_not_integralRegular
      equations (integralAffineMap x₀ z p.m)).mp hrank

/-- The strict projective input gives a uniform fifth-power estimate for
the exact low-rank cell.  The constant depends only on the fixed displayed
equation family. -/
theorem exists_strictRankAtMostSix_card_le_mul_fifthPower
    (equations : Finset (MvPolynomial (Fin 13) ℤ)) (degree : ℕ)
    (hI : IsIntegralProjectiveVariety
      (N := 12) (rationalDepthSevenEquationIdeal equations) 5 degree) :
    ∃ K : ℕ, ∀ (p : Parameters) (x₀ : IntVector 13) (CF : ℕ),
      (depthSevenNormalizedRankAtMostSixFinset
        p x₀ equations CF).card ≤
          K * (surfaceTangentNaturalSide p) ^ 5 := by
  have hdata := strictProjectiveInput_consequences equations degree hI
  obtain ⟨K₀, hK₀⟩ :=
    exists_rankAtMostSixDisplacement_card_le_mul_fifthPower_of_homogeneousIdeal
      (rationalizedEquationFinset equations)
      (rationalDepthSevenEquationIdeal equations)
      hdata.2.2.1 hdata.1 rfl hdata.2.2.2.1
  refine ⟨K₀ * 2 ^ 5, ?_⟩
  intro p x₀ CF
  have hraw := hK₀
    (depthSevenNormalizedDisplacementFinset p x₀ equations CF)
    x₀ p.m (2 * surfaceTangentNaturalSide p) p.hm
    (by
      have hside := one_le_surfaceTangentNaturalSide p
      omega)
    (by
      intro z hz
      exact depthSevenNormalized_coordinate_le_two_surfaceTangentNaturalSide
        p x₀ equations CF hz)
    (by
      intro z hz
      exact depthSevenNormalized_mem_rationalizedCommonZeroLocus
        p x₀ equations CF hz)
  rw [← depthSevenNormalizedRankAtMostSixFinset_eq_rationalFilter
    p x₀ equations CF] at hraw
  calc
    (depthSevenNormalizedRankAtMostSixFinset p x₀ equations CF).card ≤
        K₀ * (2 * surfaceTangentNaturalSide p) ^ 5 := hraw
    _ = (K₀ * 2 ^ 5) * (surfaceTangentNaturalSide p) ^ 5 := by ring

end

end TranslatedDepthSeven
