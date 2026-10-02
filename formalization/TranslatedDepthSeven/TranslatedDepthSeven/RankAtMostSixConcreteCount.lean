import TranslatedDepthSeven.JacobianGeneratorIndependence
import TranslatedDepthSeven.HomogeneousLinearNormalizationBoxCount
import TranslatedDepthSeven.FiniteHomogeneousIdealGenerators
import TranslatedDepthSeven.GenericJacobianMinor

namespace TranslatedDepthSeven

noncomputable section

open MvPolynomial
attribute [local instance] MvPolynomial.gradedAlgebra
local instance rankAtMostSixClassicalDecidablePred {A : Type*} (p : A → Prop) :
    DecidablePred p := Classical.decPred p

/-- The intrinsic `O(T^5)` rank-at-most-six estimate for an arbitrary finite
presentation of a homogeneous prime sixfold.  Homogeneous generators are
chosen internally; equality of Jacobian row spans at common zeroes transfers
the rank locus back to the displayed family. -/
theorem exists_rankAtMostSixDisplacement_card_le_mul_fifthPower_of_homogeneousIdeal
    (equations : Finset (MvPolynomial (Fin 13) ℚ))
    (P : Ideal (MvPolynomial (Fin 13) ℚ))
    (hprime : P.IsPrime)
    (hhom : P.IsHomogeneous
      (MvPolynomial.homogeneousSubmodule (Fin 13) ℚ))
    (hP : Ideal.span (equations : Set _) = P)
    (hPdim : ringKrullDim (MvPolynomial (Fin 13) ℚ ⧸ P) = 6) :
    ∃ K : ℕ, ∀ (points : Finset (IntVector 13)) (x₀ : IntVector 13)
      (m T : ℕ), 0 < m → 1 ≤ T →
      (∀ z ∈ points, ∀ i, (z i).natAbs ≤ T) →
      (∀ z ∈ points, (fun i ↦ (integralAffineMap x₀ z m i : ℚ)) ∈
        finiteAffineCommonZeroLocus equations) →
      (points.filter fun z ↦
        (fun i ↦ (integralAffineMap x₀ z m i : ℚ)) ∈
          finiteAffineCommonZeroLocus
            (depthSevenJacobianExceptionalEquationFinset equations)).card ≤
        K * T ^ 5 := by
  classical
  obtain ⟨E, hEhom, hEspan⟩ := exists_finite_homogeneous_generators P hhom
  have hEspan' : Ideal.span (E : Set _) = P := by
    simpa [finiteEquationIdeal] using hEspan
  letI : P.IsPrime := hprime
  obtain ⟨C, hC⟩ :=
    exists_depthSevenJacobianChart_determinant_notMem_of_prime_dimension_six
      E P hprime hEspan' hPdim
  obtain ⟨K, hK⟩ :=
    exists_exceptionalDisplacement_card_le_mul_fifthPower_of_dim_six
      E hEhom P hEspan' C hC hPdim
  refine ⟨K, ?_⟩
  intro points x₀ m T hm hT hbox hzero
  have hzeroE : ∀ z ∈ points,
      (fun i ↦ (integralAffineMap x₀ z m i : ℚ)) ∈
        finiteAffineCommonZeroLocus E := by
    intro z hz
    rw [← affineIdealZeroLocus_finiteEquationIdeal,
      hEspan]
    rw [← hP, ← finiteEquationIdeal]
    exact (by
      rw [affineIdealZeroLocus_finiteEquationIdeal]
      exact hzero z hz)
  have heq : (points.filter fun z ↦
        (fun i ↦ (integralAffineMap x₀ z m i : ℚ)) ∈
          finiteAffineCommonZeroLocus
            (depthSevenJacobianExceptionalEquationFinset equations)) =
      (points.filter fun z ↦
        (fun i ↦ (integralAffineMap x₀ z m i : ℚ)) ∈
          finiteAffineCommonZeroLocus
            (depthSevenJacobianExceptionalEquationFinset E)) := by
    ext z
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hz, hze⟩
      refine ⟨hz, (mem_finiteAffineCommonZeroLocus_exceptional_iff E _).mpr
        ⟨hzeroE z hz, ?_⟩⟩
      exact (rankAtMostSix_iff_of_idealSpan_eq equations E _
        (hzero z hz) (hzeroE z hz) (hP.trans hEspan'.symm)).mp
          ((mem_finiteAffineCommonZeroLocus_exceptional_iff equations _).mp hze).2
    · rintro ⟨hz, hze⟩
      refine ⟨hz, (mem_finiteAffineCommonZeroLocus_exceptional_iff equations _).mpr
        ⟨hzero z hz, ?_⟩⟩
      exact (rankAtMostSix_iff_of_idealSpan_eq equations E _
        (hzero z hz) (hzeroE z hz) (hP.trans hEspan'.symm)).mpr
          ((mem_finiteAffineCommonZeroLocus_exceptional_iff E _).mp hze).2
  rw [heq]
  exact hK points x₀ m T hm hT hbox

end

end TranslatedDepthSeven
