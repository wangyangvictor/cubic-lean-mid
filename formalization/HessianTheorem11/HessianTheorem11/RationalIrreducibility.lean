import HessianTheorem11.Geometry
import Mathlib.Algebra.MvPolynomial.Nilpotent
import Mathlib.RingTheory.MvPolynomial.MonomialOrder.DegLex

/-! Rational irreducibility of anisotropic cubic forms. The argument uses
actual polynomial degrees and constructs a nonzero rational zero of every
affine linear factor in at least two variables. No geometric input is used. -/

noncomputable section
namespace HessianTheorem11
open MvPolynomial

section AffineLinear
variable {σ K : Type*} [Fintype σ] [Field K]

/-- Every polynomial of total degree at most one has its actual affine linear
coefficient expansion. -/
theorem eq_affine_linear_of_totalDegree_le_one
    (P : MvPolynomial σ K) (hP : P.totalDegree ≤ 1) :
    P = C (coeff 0 P) + ∑ i, C (coeff (Finsupp.single i 1) P) * X i := by
  classical
  ext d
  simp only [coeff_add, coeff_sum, C_mul_X_eq_monomial]
  by_cases hd0 : d = 0
  · subst d
    simp
  by_cases hd1 : d.degree = 1
  · obtain ⟨i, rfl⟩ := (show d ∈ Set.range (fun i : σ => Finsupp.single i 1) by
      rw [Finsupp.range_single_one]
      exact hd1)
    simp [coeff_C, coeff_monomial, Finsupp.single_left_inj, Ne.symm hd0]
  · have hdegree : 1 < d.degree := by
      have hz : d.degree ≠ 0 := fun h => hd0 ((Finsupp.degree_eq_zero_iff d).mp h)
      omega
    have hc : coeff d P = 0 := coeff_eq_zero_of_totalDegree_lt (lt_of_le_of_lt hP hdegree)
    rw [hc, coeff_C, if_neg (Ne.symm hd0)]
    simp only [zero_add]
    symm
    apply Finset.sum_eq_zero
    intro i _
    have hne : d ≠ Finsupp.single i 1 := by
      intro h
      apply hd1
      simp [h]
    simp [coeff_monomial, Ne.symm hne]

theorem eval_affine_linear_of_totalDegree_le_one
    (P : MvPolynomial σ K) (hP : P.totalDegree ≤ 1) (x : σ → K) :
    eval x P = coeff 0 P + ∑ i, coeff (Finsupp.single i 1) P * x i := by
  conv_lhs => rw [eq_affine_linear_of_totalDegree_le_one P hP]
  simp

theorem exists_linear_coefficient_ne_zero_of_totalDegree_one
    (P : MvPolynomial σ K) (hP : P.totalDegree = 1) :
    ∃ i, coeff (Finsupp.single i 1) P ≠ 0 := by
  classical
  by_contra h
  push_neg at h
  have he := eq_affine_linear_of_totalDegree_le_one P hP.le
  simp only [h, C_0, zero_mul, Finset.sum_const_zero, add_zero] at he
  have hd := congrArg totalDegree he
  rw [hP, totalDegree_C] at hd
  omega

end AffineLinear

/-- A degree-one polynomial in at least two variables has a nonzero zero
over the coefficient field, even when its constant term is nonzero. -/
theorem exists_nonzero_zero_of_totalDegree_one
    {K : Type*} [Field K] {n : ℕ} (hn : 2 ≤ n)
    (P : MvPolynomial (Fin n) K) (hP : P.totalDegree = 1) :
    ∃ x : Fin n → K, x ≠ 0 ∧ eval x P = 0 := by
  classical
  letI : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr hn
  obtain ⟨i, hi⟩ := exists_linear_coefficient_ne_zero_of_totalDegree_one P hP
  obtain ⟨j, hji⟩ := exists_ne i
  let a : Fin n → K := fun k => coeff (Finsupp.single k 1) P
  let c := coeff 0 P
  let v : Fin n → K := Pi.single i (-(c + a j) / a i) + Pi.single j 1
  refine ⟨v, ?_, ?_⟩
  · intro hv
    have hj := congrFun hv j
    simp [v, hji] at hj
  · rw [eval_affine_linear_of_totalDegree_le_one P hP.le]
    change c + dotProduct a v = 0
    unfold v
    rw [dotProduct_add, dotProduct_single, dotProduct_single, mul_one]
    have hai : a i ≠ 0 := hi
    field_simp
    ring

theorem totalDegree_pos_of_nonzero_nonunit
    {σ K : Type*} [Field K] (P : MvPolynomial σ K)
    (hzero : P ≠ 0) (hunit : ¬ IsUnit P) : 0 < P.totalDegree := by
  by_contra h
  have hd : P.totalDegree = 0 := by omega
  have he := totalDegree_eq_zero_iff_eq_C.mp hd
  have hc : coeff 0 P ≠ 0 := by
    intro hc
    apply hzero
    simpa [hc] using he
  apply hunit
  rw [he]
  exact (isUnit_iff_ne_zero.mpr hc).map C

/-- An anisotropic rational cubic in at least two variables is irreducible
over the rationals. This does not assert geometric irreducibility. -/
theorem anisotropic_cubic_irreducible {n : ℕ}
    (F : AnisotropicCubic n) (hn : 2 ≤ n) : Irreducible F.polynomial := by
  have hFzero : F.polynomial ≠ 0 := anisotropic_polynomial_ne_zero (by omega) F
  have hFdegree : F.polynomial.totalDegree = 3 := F.homogeneous.totalDegree hFzero
  refine ⟨?_, ?_⟩
  · intro hu
    have hd := (isUnit_iff_totalDegree_of_isReduced.mp hu).2
    omega
  · intro A B hAB
    by_contra hunit
    push_neg at hunit
    have hAzero : A ≠ 0 := by
      intro hA
      apply hFzero
      simp [hAB, hA]
    have hBzero : B ≠ 0 := by
      intro hB
      apply hFzero
      simp [hAB, hB]
    have hApos := totalDegree_pos_of_nonzero_nonunit A hAzero hunit.1
    have hBpos := totalDegree_pos_of_nonzero_nonunit B hBzero hunit.2
    have hd : A.totalDegree + B.totalDegree = 3 := by
      rw [← totalDegree_mul_of_isDomain hAzero hBzero, ← hAB, hFdegree]
    have hone : A.totalDegree = 1 ∨ B.totalDegree = 1 := by omega
    rcases hone with hA | hB
    · obtain ⟨x, hx, hAx⟩ := exists_nonzero_zero_of_totalDegree_one hn A hA
      apply hx
      apply F.anisotropic
      rw [hAB, eval_mul, hAx, zero_mul]
    · obtain ⟨x, hx, hBx⟩ := exists_nonzero_zero_of_totalDegree_one hn B hB
      apply hx
      apply F.anisotropic
      rw [hAB, eval_mul, hBx, mul_zero]

end HessianTheorem11
