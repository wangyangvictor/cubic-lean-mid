import HessianTheorem11.QuadricLowRank
import HessianTheorem11.ReducibleCubicRank

/-! A quadratic polynomial with Hessian rank greater than two is irreducible.
The proof derives the two-linear-factor case directly from polynomial degrees. -/
noncomputable section
namespace HessianTheorem11
open MvPolynomial Matrix
variable {K : Type*} [Field K] {n : ℕ}

theorem hessian_linear_times_linear
    (L Q : MvPolynomial (Fin n) K) (hL : L.IsHomogeneous 1) (hQ : Q.IsHomogeneous 1)
    (x : Fin n → K) :
    hessian (L*Q) x =
      Matrix.vecMulVec (ReducibleCubicRank.linearCoefficient L)
        (ReducibleCubicRank.linearCoefficient Q) +
      Matrix.vecMulVec (ReducibleCubicRank.linearCoefficient Q)
        (ReducibleCubicRank.linearCoefficient L) := by
  ext i j
  simp [hessian, hessianPolynomial, Derivation.leibniz, smul_eq_mul,
    ReducibleCubicRank.linear_partial L hL, ReducibleCubicRank.linear_partial Q hQ,
    Matrix.vecMulVec_apply]
  ring

theorem homogeneous_quadratic_irreducible_of_hessian_rank
    (P : MvPolynomial (Fin n) K) (hP : P.IsHomogeneous 2)
    (x : Fin n → K) (hrank : 2 < (hessian P x).rank) : Irreducible P := by
  have hzero : P ≠ 0 := by
    intro h
    have hz : hessian (0 : MvPolynomial (Fin n) K) x = 0 := by
      ext i j
      simp [hessian, hessianPolynomial]
    rw [h, hz, Matrix.rank_zero] at hrank
    omega
  have hdegree := hP.totalDegree hzero
  refine ⟨?_, ?_⟩
  · intro hu
    have h := (isUnit_iff_totalDegree_of_isReduced.mp hu).2
    omega
  · intro A B hAB
    by_contra hunit
    push_neg at hunit
    have hAz : A ≠ 0 := by intro h; simp [h] at hAB; exact hzero hAB
    have hBz : B ≠ 0 := by intro h; simp [h] at hAB; exact hzero hAB
    have hAp := totalDegree_pos_of_nonzero_nonunit A hAz hunit.1
    have hBp := totalDegree_pos_of_nonzero_nonunit B hBz hunit.2
    have hd : A.totalDegree + B.totalDegree = 2 := by
      rw [← totalDegree_mul_of_isDomain hAz hBz, ← hAB, hdegree]
    have hA1 : A.totalDegree ≤ 1 := by omega
    have hB1 : B.totalDegree ≤ 1 := by omega
    have he : P = QuadricLowRank.linearPart A * QuadricLowRank.linearPart B :=
      hAB.trans (QuadricLowRank.homogeneous_quadric_eq_linearParts A B hA1 hB1 (hAB ▸ hP))
    rw [he, hessian_linear_times_linear _ _
      (QuadricLowRank.linearPart_isHomogeneous A hA1)
      (QuadricLowRank.linearPart_isHomogeneous B hB1)] at hrank
    have hr := MatrixRankBounds.rank_add_le
      (Matrix.vecMulVec (ReducibleCubicRank.linearCoefficient (QuadricLowRank.linearPart A))
        (ReducibleCubicRank.linearCoefficient (QuadricLowRank.linearPart B)))
      (Matrix.vecMulVec (ReducibleCubicRank.linearCoefficient (QuadricLowRank.linearPart B))
        (ReducibleCubicRank.linearCoefficient (QuadricLowRank.linearPart A)))
    have hr1 := Matrix.rank_vecMulVec_le
      (ReducibleCubicRank.linearCoefficient (QuadricLowRank.linearPart A))
      (ReducibleCubicRank.linearCoefficient (QuadricLowRank.linearPart B))
    have hr2 := Matrix.rank_vecMulVec_le
      (ReducibleCubicRank.linearCoefficient (QuadricLowRank.linearPart B))
      (ReducibleCubicRank.linearCoefficient (QuadricLowRank.linearPart A))
    omega

end HessianTheorem11
