import CubicTenVariables.CubicFactorCharts
import HessianTheorem11.RationalIrreducibility

/-!
# Top homogeneous factors in arbitrary degree

This is the elementary graded-ring step needed to express reducibility of
an arbitrary homogeneous polynomial by finite projective factor equations.
-/

set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.GeneralHomogeneousFactorization

open MvPolynomial
open scoped BigOperators

variable {K : Type*} [Field K] {n : ℕ}

/-- If a product is homogeneous of the sum of the two total degrees, it is
the product of the top homogeneous components of its factors. -/
theorem product_eq_top_components
    (A B : MvPolynomial (Fin n) K) {e f : ℕ}
    (he : A.totalDegree = e) (hf : B.totalDegree = f)
    (hhom : (A * B).IsHomogeneous (e + f)) :
    A * B = homogeneousComponent e A * homogeneousComponent f B := by
  have hA : A = ∑ i ∈ Finset.range (e + 1), homogeneousComponent i A := by
    rw [← he]
    exact (sum_homogeneousComponent A).symm
  have hB : B = ∑ j ∈ Finset.range (f + 1), homogeneousComponent j B := by
    rw [← hf]
    exact (sum_homogeneousComponent B).symm
  calc
    A * B = homogeneousComponent (e + f) (A * B) := by
      rw [homogeneousComponent_of_mem hhom]
      simp
    _ = homogeneousComponent e A * homogeneousComponent f B := by
      conv_lhs => arg 2; rw [hA, hB]
      simp only [Finset.sum_mul, Finset.mul_sum, map_sum]
      change (∑ j ∈ Finset.range (f + 1), ∑ i ∈ Finset.range (e + 1),
        homogeneousComponent (e + f)
          (homogeneousComponent i A * homogeneousComponent j B)) = _
      rw [Finset.sum_eq_single f]
      · rw [Finset.sum_eq_single e]
        · rw [homogeneousComponent_of_mem
            ((homogeneousComponent_isHomogeneous e A).mul
              (homogeneousComponent_isHomogeneous f B))]
          simp
        · intro i hi hine
          rw [homogeneousComponent_of_mem
            ((homogeneousComponent_isHomogeneous i A).mul
              (homogeneousComponent_isHomogeneous f B))]
          simp [Ne.symm hine]
        · simp
      · intro j hj hjne
        apply Finset.sum_eq_zero
        intro i hi
        rw [homogeneousComponent_of_mem
          ((homogeneousComponent_isHomogeneous i A).mul
            (homogeneousComponent_isHomogeneous j B))]
        have hile : i ≤ e := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
        have hjle : j ≤ f := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
        have hne : e + f ≠ i + j := by omega
        simp [hne]
      · simp

/-- A nonzero reducible homogeneous polynomial has a factorization by two
nonzero homogeneous polynomials of positive complementary degrees. -/
theorem exists_homogeneous_factorization_of_not_irreducible
    {d : ℕ} (F : MvPolynomial (Fin n) K)
    (hdpos : 1 ≤ d) (hF : F.IsHomogeneous d) (hF0 : F ≠ 0)
    (hred : ¬ Irreducible F) :
    ∃ e : ℕ, 1 ≤ e ∧ e < d ∧
      ∃ A B : MvPolynomial (Fin n) K,
        A.IsHomogeneous e ∧ B.IsHomogeneous (d - e) ∧
        A ≠ 0 ∧ B ≠ 0 ∧ F = A * B := by
  have hd : F.totalDegree = d := hF.totalDegree hF0
  have hunit : ¬ IsUnit F := by
    intro hu
    have hz := (isUnit_iff_totalDegree_of_isReduced.mp hu).2
    rw [hd] at hz
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
  have hA0 : A ≠ 0 := by
    intro h
    apply hF0
    rw [hAB, h, zero_mul]
  have hB0 : B ≠ 0 := by
    intro h
    apply hF0
    rw [hAB, h, mul_zero]
  let e := A.totalDegree
  let f := B.totalDegree
  have he : 1 ≤ e := HessianTheorem11.totalDegree_pos_of_nonzero_nonunit A hA0 hAu
  have hf : 1 ≤ f := HessianTheorem11.totalDegree_pos_of_nonzero_nonunit B hB0 hBu
  have hef : e + f = d := by
    dsimp only [e, f]
    rw [← totalDegree_mul_of_isDomain hA0 hB0, ← hAB, hd]
  have hed : e < d := by omega
  let A' := homogeneousComponent e A
  let B' := homogeneousComponent f B
  have hprod : F = A' * B' := by
    rw [hAB]
    apply product_eq_top_components A B rfl rfl
    rw [hef]
    exact hAB ▸ hF
  have hA'0 : A' ≠ 0 := by
    intro h
    rw [h, zero_mul] at hprod
    exact hF0 hprod
  have hB'0 : B' ≠ 0 := by
    intro h
    rw [h, mul_zero] at hprod
    exact hF0 hprod
  refine ⟨e, he, hed, A', B', homogeneousComponent_isHomogeneous e A, ?_,
    hA'0, hB'0, hprod⟩
  have hfe : d - e = f := by omega
  simpa only [hfe] using homogeneousComponent_isHomogeneous f B

end CubicTenVariables.GeneralHomogeneousFactorization
