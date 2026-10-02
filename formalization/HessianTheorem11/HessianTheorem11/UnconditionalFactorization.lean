import HessianTheorem11.QuadraticIrreducibility
import HessianTheorem11.CubicRankIrreducibility

/-! Elementary degree-one and degree-two factorization used in the direct
arithmetic proof of absolute irreducibility. No external geometric input. -/
noncomputable section
namespace HessianTheorem11.UnconditionalIrreducibility
open MvPolynomial
variable {K : Type*} [Field K] {n : ℕ}

theorem irreducible_of_totalDegree_one (P : MvPolynomial (Fin n) K)
    (hP : P.totalDegree = 1) : Irreducible P := by
  have hP0 : P ≠ 0 := by intro h; simp [h] at hP
  refine ⟨?_, ?_⟩
  · intro hu
    have h := (isUnit_iff_totalDegree_of_isReduced.mp hu).2
    omega
  · intro A B hAB
    by_contra hu
    push_neg at hu
    have hA : A ≠ 0 := by intro h; exact hP0 (by simp [hAB,h])
    have hB : B ≠ 0 := by intro h; exact hP0 (by simp [hAB,h])
    have ha := totalDegree_pos_of_nonzero_nonunit A hA hu.1
    have hb := totalDegree_pos_of_nonzero_nonunit B hB hu.2
    have hd := totalDegree_mul_of_isDomain hA hB
    rw [← hAB,hP] at hd
    omega

theorem reducible_homogeneous_quadratic_linear_times_linear
    (P : MvPolynomial (Fin n) K) (hP : P.IsHomogeneous 2)
    (hP0 : P ≠ 0) (hred : ¬ Irreducible P) :
    ∃ A B : MvPolynomial (Fin n) K,
      A.IsHomogeneous 1 ∧ B.IsHomogeneous 1 ∧ P = A * B := by
  have hdeg := hP.totalDegree hP0
  have hunit : ¬ IsUnit P := by
    intro hu
    have h := (isUnit_iff_totalDegree_of_isReduced.mp hu).2
    omega
  have hex : ∃ A B, P = A * B ∧ ¬ IsUnit A ∧ ¬ IsUnit B := by
    by_contra hh
    apply hred
    refine ⟨hunit, ?_⟩
    intro A B hAB
    by_contra h
    push_neg at h
    exact hh ⟨A,B,hAB,h.1,h.2⟩
  obtain ⟨A,B,hAB,hAu,hBu⟩ := hex
  have hA : A ≠ 0 := by intro h; exact hP0 (by simp [hAB,h])
  have hB : B ≠ 0 := by intro h; exact hP0 (by simp [hAB,h])
  have ha := totalDegree_pos_of_nonzero_nonunit A hA hAu
  have hb := totalDegree_pos_of_nonzero_nonunit B hB hBu
  have hd := totalDegree_mul_of_isDomain hA hB
  rw [← hAB,hdeg] at hd
  have ha1 : A.totalDegree ≤ 1 := by omega
  have hb1 : B.totalDegree ≤ 1 := by omega
  exact ⟨QuadricLowRank.linearPart A,QuadricLowRank.linearPart B,
    QuadricLowRank.linearPart_isHomogeneous A ha1,
    QuadricLowRank.linearPart_isHomogeneous B hb1,
    hAB.trans (QuadricLowRank.homogeneous_quadric_eq_linearParts A B ha1 hb1 (hAB ▸ hP))⟩

end HessianTheorem11.UnconditionalIrreducibility
