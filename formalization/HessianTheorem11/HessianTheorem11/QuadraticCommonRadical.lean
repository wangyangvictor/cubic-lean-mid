import HessianTheorem11.ThreeQuadricsLowImage
import HessianTheorem11.ReducibleCubicRank
import HessianTheorem11.SmoothCubicPoint

/-! Actual common differential radicals of binary quadratic tuples. -/
noncomputable section
namespace HessianTheorem11
open MvPolynomial Matrix Module
variable {K : Type*} [Field K] [CharZero K] {n m : ℕ}

def polynomialTupleDifferentialRadical (P : Fin m → MvPolynomial (Fin n) K) :
    Submodule K (Fin n → K) := ⨅ x : Fin n → K, ⨅ i : Fin m,
      LinearMap.ker (polynomialDifferential (P i) x)

theorem mem_polynomialTupleDifferentialRadical
    (P : Fin m → MvPolynomial (Fin n) K) (v : Fin n → K) :
    v ∈ polynomialTupleDifferentialRadical P ↔
      ∀ x i, polynomialDifferential (P i) x v = 0 := by
  simp [polynomialTupleDifferentialRadical]

theorem polynomialDifferential_combine {r s : ℕ}
    (A : Matrix (Fin r) (Fin s) K) (P : Fin s → MvPolynomial (Fin n) K)
    (i : Fin r) (x v : Fin n → K) :
    polynomialDifferential (combinePolynomials A P i) x v =
      ∑ j, A i j * polynomialDifferential (P j) x v := by
  simp only [polynomialDifferential_apply, combinePolynomials_apply, map_sum,
    Derivation.leibniz, smul_eq_mul, pderiv_C, zero_mul, zero_add,
    map_mul, eval_C, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  simp only [mul_zero, add_zero, map_mul, eval_C]
  ring

theorem polynomialTupleDifferentialRadical_le_combine {r s : ℕ}
    (A : Matrix (Fin r) (Fin s) K) (P : Fin s → MvPolynomial (Fin n) K) :
    polynomialTupleDifferentialRadical P ≤
      polynomialTupleDifferentialRadical (combinePolynomials A P) := by
  intro v hv
  rw [mem_polynomialTupleDifferentialRadical] at hv ⊢
  intro x i
  rw [polynomialDifferential_combine]
  simp only [hv, mul_zero, Finset.sum_const_zero]

theorem polynomialTupleDifferentialRadical_eq_of_mutual_combine {r s : ℕ}
    (A : Matrix (Fin r) (Fin s) K) (D : Matrix (Fin s) (Fin r) K)
    (P : Fin r → MvPolynomial (Fin n) K) (Q : Fin s → MvPolynomial (Fin n) K)
    (hP : P = combinePolynomials A Q) (hQ : Q = combinePolynomials D P) :
    polynomialTupleDifferentialRadical P = polynomialTupleDifferentialRadical Q := by
  apply le_antisymm
  · conv_rhs => rw [hQ]
    exact polynomialTupleDifferentialRadical_le_combine D P
  · conv_rhs => rw [hP]
    exact polynomialTupleDifferentialRadical_le_combine A Q

theorem polynomialTupleDifferentialRadical_combine
    (A : Matrix (Fin m) (Fin m) K) (hA : IsUnit A)
    (P : Fin m → MvPolynomial (Fin n) K) :
    polynomialTupleDifferentialRadical (combinePolynomials A P) =
      polynomialTupleDifferentialRadical P := by
  have hle (B : Matrix (Fin m) (Fin m) K) (Q : Fin m → MvPolynomial (Fin n) K) :
      polynomialTupleDifferentialRadical Q ≤
        polynomialTupleDifferentialRadical (combinePolynomials B Q) := by
    intro v hv
    rw [mem_polynomialTupleDifferentialRadical] at hv ⊢
    intro x i
    rw [polynomialDifferential_combine]
    simp only [hv, mul_zero, Finset.sum_const_zero]
  apply le_antisymm _ (hle A P)
  have h := hle A⁻¹ (combinePolynomials A P)
  rwa [combinePolynomials_comp, Matrix.nonsing_inv_mul _
    ((Matrix.isUnit_iff_isUnit_det A).mp hA), combinePolynomials_one] at h

theorem polynomialDifferential_homogeneous_one
    (P : MvPolynomial (Fin n) K) (hP : P.IsHomogeneous 1) (x v : Fin n → K) :
    polynomialDifferential P x v = eval v P := by
  rw [polynomialDifferential_apply, ReducibleCubicRank.eval_linear P hP]
  simp [ReducibleCubicRank.linear_partial P hP, dotProduct]

theorem binary_quadratic_tuple_radical_large
    (P : Fin 3 → MvPolynomial (Fin n) K) (t : K)
    (u v : MvPolynomial (Fin n) K) (hu : u.IsHomogeneous 1) (hv : v.IsHomogeneous 1)
    (h0 : P 0 = C t * u ^ 2) (h1 : P 1 = C t * u * v) (h2 : P 2 = C t * v ^ 2) :
    n ≤ finrank K (polynomialTupleDifferentialRadical P) + 2 := by
  let B : Matrix (Fin 2) (Fin n) K :=
    fun i => ![ReducibleCubicRank.linearCoefficient u, ReducibleCubicRank.linearCoefficient v] i
  let L := LinearMap.ker B.mulVecLin
  have hle : L ≤ polynomialTupleDifferentialRadical P := by
    intro w hw
    have hBu : eval w u = 0 := by
      rw [ReducibleCubicRank.eval_linear u hu]
      exact congrFun hw 0
    have hBv : eval w v = 0 := by
      rw [ReducibleCubicRank.eval_linear v hv]
      exact congrFun hw 1
    rw [mem_polynomialTupleDifferentialRadical]
    intro x i
    have hc : polynomialDifferential (C t : MvPolynomial (Fin n) K) x w = 0 := by
      simp [polynomialDifferential_apply]
    have hu' := polynomialDifferential_homogeneous_one u hu x w
    have hv' := polynomialDifferential_homogeneous_one v hv x w
    rw [hBu] at hu'
    rw [hBv] at hv'
    fin_cases i
    · change polynomialDifferential (P (0 : Fin 3)) x w = 0
      rw [h0]
      simp only [pow_two, polynomialDifferential_mul_apply, hc, hu', mul_zero, add_zero]
    · change polynomialDifferential (P (1 : Fin 3)) x w = 0
      rw [h1]
      simp only [polynomialDifferential_mul_apply, hc, hu', hv', mul_zero, add_zero]
    · change polynomialDifferential (P (2 : Fin 3)) x w = 0
      rw [h2]
      simp only [pow_two, polynomialDifferential_mul_apply, hc, hv', mul_zero, add_zero]
  have hdim := B.mulVecLin.finrank_range_add_finrank_ker
  have hbound := Matrix.rank_le_card_height B
  have hm := Submodule.finrank_mono hle
  change B.rank + finrank K L = finrank K (Fin n → K) at hdim
  simp only [Module.finrank_pi, Module.finrank_self, Fintype.card_fin, mul_one] at hdim
  simp only [Fintype.card_fin] at hbound
  omega

theorem three_quadrics_low_image_common_radical
    (GR : GenericRankOpenInput) (AD : AffineHypersurfaceDimensionInput)
    (P : Fin 3 → GeometricPolynomial n) (hP : ∀ i, (P i).IsHomogeneous 2)
    (hli : LinearIndependent GeometricField P)
    (hdim : affineDimension (geometricClosure (polynomialMap P '' Set.univ)) ≤ 2) :
    n ≤ finrank GeometricField (polynomialTupleDifferentialRadical P) + 2 := by
  obtain ⟨A, hA, t, ht, u, v, hu, hv, h0, h1, h2⟩ :=
    three_independent_quadrics_low_image GR AD P hP hli hdim
  have h := binary_quadratic_tuple_radical_large (combinePolynomials A P) t u v hu hv h0 h1 h2
  rwa [polynomialTupleDifferentialRadical_combine A hA P] at h

end HessianTheorem11
