import HessianTheorem11.ReducibleCubicRank
import HessianTheorem11.RationalIrreducibility

/-! An intermediate Hessian rank on the zero set certifies irreducibility
of a cubic with nonzero Hessian determinant. The factorization into a linear
form and a quadric is proved by taking homogeneous components. -/
noncomputable section
namespace HessianTheorem11
open MvPolynomial

variable {K : Type*} [Field K] {n : ℕ}

theorem homogeneous_cubic_product_top_components
    (A B : MvPolynomial (Fin n) K) (ha : A.totalDegree = 1)
    (hb : B.totalDegree = 2) (hh : (A * B).IsHomogeneous 3) :
    A * B = homogeneousComponent 1 A * homogeneousComponent 2 B := by
  have hA : A = homogeneousComponent 0 A + homogeneousComponent 1 A := by
    have h := sum_homogeneousComponent A
    simpa [ha, Finset.sum_range_succ] using h.symm
  have hB : B = homogeneousComponent 0 B + homogeneousComponent 1 B +
      homogeneousComponent 2 B := by
    have h := sum_homogeneousComponent B
    simpa [hb, Finset.sum_range_succ] using h.symm
  have hc (i j : ℕ) : homogeneousComponent 3
      (homogeneousComponent i A * homogeneousComponent j B) =
      if 3 = i + j then homogeneousComponent i A * homogeneousComponent j B else 0 :=
    homogeneousComponent_of_mem
      ((homogeneousComponent_isHomogeneous i A).mul (homogeneousComponent_isHomogeneous j B))
  calc
    A * B = homogeneousComponent 3 (A * B) := by
      symm
      simpa using (homogeneousComponent_of_mem (m := 3) hh)
    _ = homogeneousComponent 1 A * homogeneousComponent 2 B := by
      conv_lhs => arg 2; rw [hA, hB]
      simp only [add_mul, mul_add, map_add, hc]
      norm_num

theorem reducible_homogeneous_cubic_linear_times_quadratic
    (F : MvPolynomial (Fin n) K) (hF : F.IsHomogeneous 3)
    (hzero : F ≠ 0) (hred : ¬ Irreducible F) :
    ∃ L Q : MvPolynomial (Fin n) K,
      L.IsHomogeneous 1 ∧ Q.IsHomogeneous 2 ∧ F = L * Q := by
  have hdegree := hF.totalDegree hzero
  have hunit : ¬ IsUnit F := by
    intro hu
    have h := (isUnit_iff_totalDegree_of_isReduced.mp hu).2
    omega
  have hex : ∃ A B, F = A * B ∧ ¬ IsUnit A ∧ ¬ IsUnit B := by
    by_contra hh
    apply hred
    refine ⟨hunit, ?_⟩
    intro A B hAB
    by_contra h
    push_neg at h
    exact hh ⟨A, B, hAB, h.1, h.2⟩
  obtain ⟨A, B, hAB, hAu, hBu⟩ := hex
  have hAz : A ≠ 0 := by intro h; simp [h] at hAB; exact hzero hAB
  have hBz : B ≠ 0 := by intro h; simp [h] at hAB; exact hzero hAB
  have hAp := totalDegree_pos_of_nonzero_nonunit A hAz hAu
  have hBp := totalDegree_pos_of_nonzero_nonunit B hBz hBu
  have hd : A.totalDegree + B.totalDegree = 3 := by
    rw [← totalDegree_mul_of_isDomain hAz hBz, ← hAB, hdegree]
  have ht : (A.totalDegree = 1 ∧ B.totalDegree = 2) ∨
      (B.totalDegree = 1 ∧ A.totalDegree = 2) := by omega
  rcases ht with ht | ht
  · refine ⟨homogeneousComponent 1 A, homogeneousComponent 2 B,
      homogeneousComponent_isHomogeneous 1 A, homogeneousComponent_isHomogeneous 2 B, ?_⟩
    rw [hAB]
    exact homogeneous_cubic_product_top_components A B ht.1 ht.2 (hAB ▸ hF)
  · refine ⟨homogeneousComponent 1 B, homogeneousComponent 2 A,
      homogeneousComponent_isHomogeneous 1 B, homogeneousComponent_isHomogeneous 2 A, ?_⟩
    have hBA : F = B * A := hAB.trans (mul_comm A B)
    rw [hBA]
    exact homogeneous_cubic_product_top_components B A ht.1 ht.2 (hBA ▸ hF)

theorem cubic_irreducible_of_intermediate_hessian_rank [CharZero K] [Infinite K]
    (F : MvPolynomial (Fin n) K) (hF : F.IsHomogeneous 3)
    (hdet : hessianDeterminantPolynomial F ≠ 0)
    (x : Fin n → K) (hx : eval x F = 0)
    (hlow : 2 < (hessian F x).rank) (hhigh : (hessian F x).rank < n - 1) :
    Irreducible F := by
  have hzero : F ≠ 0 := by
    intro hf
    have hm : hessian F x = 0 := by
      ext i j
      simp [hf, hessian, hessianPolynomial]
    have hz : (hessian F x).rank = 0 := by rw [hm, Matrix.rank_zero]
    omega
  by_contra hred
  obtain ⟨L, Q, hL, hQ, he⟩ := reducible_homogeneous_cubic_linear_times_quadratic F hF hzero hred
  rw [he] at hdet hx hlow hhigh
  rcases ReducibleCubicRank.rank_dichotomy_on_linear_times_quadratic L Q hL hQ hdet x hx with h | h
  · omega
  · omega

end HessianTheorem11
