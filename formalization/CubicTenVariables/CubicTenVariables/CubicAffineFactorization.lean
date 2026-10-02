import HessianTheorem11.RationalIrreducibility
import Mathlib.RingTheory.Polynomial.UniqueFactorization

/-! Literal affine factor charts for a cubic. Reducibility is equivalent to
a linear times quadratic factorization with one actual linear coefficient
normalized to one. For two variables there are exactly two choices of that
coefficient. No homogeneity, characteristic restriction or spreading theorem
is used. This does not construct an exceptional parameter polynomial. -/

set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.CubicAffineFactorization
open MvPolynomial HessianTheorem11

/-- An affine cubic which is reducible has a degree-one factor and a
degree-two complementary factor, including their lower-degree terms. -/
theorem exists_linear_times_quadratic
    {K σ : Type*} [Field K] (F : MvPolynomial σ K)
    (hdegree : F.totalDegree = 3) (hred : ¬ Irreducible F) :
    ∃ L Q : MvPolynomial σ K,
      L.totalDegree = 1 ∧ Q.totalDegree = 2 ∧ F = L * Q := by
  have hzero : F ≠ 0 := by intro h; simp [h] at hdegree
  have hunit : ¬ IsUnit F := by
    intro hu
    have hd := (isUnit_iff_totalDegree_of_isReduced.mp hu).2
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
  · exact ⟨A, B, ht.1, ht.2, hAB⟩
  · exact ⟨B, A, ht.1, ht.2, hAB.trans (mul_comm A B)⟩

/-- Reducibility of an actual cubic is covered by the finite affine charts
obtained by making one nonzero linear coefficient equal to one. -/
theorem not_irreducible_iff_normalized_factor
    {K σ : Type*} [Field K] [Fintype σ] (F : MvPolynomial σ K)
    (hdegree : F.totalDegree = 3) :
    (¬ Irreducible F) ↔
      ∃ (i : σ) (L Q : MvPolynomial σ K),
        coeff (Finsupp.single i 1) L = 1 ∧
        L.totalDegree = 1 ∧ Q.totalDegree = 2 ∧ F = L * Q := by
  classical
  constructor
  · intro hred
    obtain ⟨L, Q, hL, hQ, hF⟩ := exists_linear_times_quadratic F hdegree hred
    obtain ⟨i, hi⟩ := exists_linear_coefficient_ne_zero_of_totalDegree_one L hL
    let a := coeff (Finsupp.single i 1) L
    have ha : a ≠ 0 := hi
    have hL0 : L ≠ 0 := by intro h; simp [h] at hL
    have hQ0 : Q ≠ 0 := by intro h; simp [h] at hQ
    refine ⟨i, C a⁻¹ * L, C a * Q, ?_, ?_, ?_, ?_⟩
    · simp only [coeff_C_mul]
      exact inv_mul_cancel₀ ha
    · rw [totalDegree_mul_of_isDomain (C_ne_zero.mpr (inv_ne_zero ha)) hL0,
        totalDegree_C, zero_add, hL]
    · rw [totalDegree_mul_of_isDomain (C_ne_zero.mpr ha) hQ0,
        totalDegree_C, zero_add, hQ]
    · rw [mul_mul_mul_comm, ← map_mul, inv_mul_cancel₀ ha, map_one, one_mul]
      exact hF
  · rintro ⟨i, L, Q, _hi, hL, hQ, hF⟩ hred
    rcases hred.isUnit_or_isUnit hF with h | h
    · have hd := (isUnit_iff_totalDegree_of_isReduced.mp h).2
      omega
    · have hd := (isUnit_iff_totalDegree_of_isReduced.mp h).2
      omega

/-- The actual principal quotient of a cubic is a domain precisely when
none of the normalized affine factor charts has a point. -/
theorem isDomain_iff_no_normalized_factor
    {K σ : Type*} [Field K] [Fintype σ] (F : MvPolynomial σ K)
    (hdegree : F.totalDegree = 3) :
    IsDomain (MvPolynomial σ K ⧸ Ideal.span {F}) ↔
      ¬ ∃ (i : σ) (L Q : MvPolynomial σ K),
        coeff (Finsupp.single i 1) L = 1 ∧
        L.totalDegree = 1 ∧ Q.totalDegree = 2 ∧ F = L * Q := by
  have hF0 : F ≠ 0 := by intro h; simp [h] at hdegree
  rw [← not_irreducible_iff_normalized_factor F hdegree, not_not,
    Ideal.Quotient.isDomain_iff_prime, Ideal.span_singleton_prime hF0]
  exact ⟨fun h => h.irreducible, fun h => h.prime⟩

end CubicTenVariables.CubicAffineFactorization
