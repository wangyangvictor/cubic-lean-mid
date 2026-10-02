import HessianTheorem11.LocalCubicFormalCurve
import HessianTheorem11.PolynomialSchurVanishing
import HessianTheorem11.CliffordNormalization
import HessianTheorem11.SimpleNormalRank
import Mathlib.RingTheory.PowerSeries.Inverse

/-! The actual cubic normal form, its geometric Hessian rank, and the general
formal implicit-function input imply the Schur relations. Matrix invertibility,
vanishing along formal curves, and every coefficient identity are proved. -/

noncomputable section
namespace HessianTheorem11.LocalCubicNormalForm
open MvPolynomial Matrix

variable {K : Type*} [Field K] [CharZero K]

/-- The polynomial Hessian in the actual sum-coordinate basis. -/
def polynomialHessian {m q : ℕ} (D : Data (K := K) m q) :
    Matrix (Coordinate m q) (Coordinate m q) (MvPolynomial (Coordinate m q) K) :=
  fun i j => pderiv j (pderiv i (polynomial D))

omit [CharZero K] in
theorem polynomialHessian_map_series {m q : ℕ} (D : Data (K := K) m q)
    (v : Fin q → K) (z : PowerSeries K) :
    (polynomialHessian D).map (seriesEval v z) = hessianSeries D v z := rfl

omit [CharZero K] in
theorem hessianSeries_fromBlocks {m q : ℕ} (D : Data (K := K) m q)
    (v : Fin q → K) (z : PowerSeries K) :
    Matrix.fromBlocks (aBlock D v z) (crossBlock D v z)
      (crossBlock D v z).transpose (normalBlock D v z) = hessianSeries D v z := by
  apply Matrix.ext
  intro i j
  rcases i with i | i <;> rcases j with j | j
  · rfl
  · rfl
  · exact congrArg (seriesEval v z)
      (partials_commute_general (polynomial D) (Sum.inr i) (Sum.inl j))
  · rfl

/-- The actual complementary series matrix has invertible determinant as
soon as the middle quadratic Hessian is nonsingular. -/
theorem normalBlock_isUnit_det {m q : ℕ} (D : Data (K := K) m q)
    (hdet : (quadraticMatrix D.Q0).det ≠ 0)
    (v : Fin q → K) (z : PowerSeries K) (hz : PowerSeries.coeff 0 z = 0) :
    IsUnit (normalBlock D v z).det := by
  apply PowerSeries.isUnit_iff_constantCoeff.mpr
  rw [RingHom.map_det]
  change IsUnit ((normalBlock D v z).map PowerSeries.constantCoeff).det
  have hc : (normalBlock D v z).map PowerSeries.constantCoeff =
      SchurSecondOrder.matrixCoeff 0 (normalBlock D v z) := by
    apply Matrix.ext
    intro i j
    exact (PowerSeries.coeff_zero_eq_constantCoeff_apply _).symm
  rw [hc, normalBlock_coeff_zero D v z hz]
  apply Matrix.isUnit_det_of_left_inverse
    (B := SchurSecondOrder.normalInverse (quadraticMatrix D.Q0)⁻¹ (2 : K)⁻¹)
  exact SchurSecondOrder.normalInverse_mul _ _ _ _
    (Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hdet))
    (by apply inv_mul_cancel₀; norm_num)

theorem normalBlock_mul_inverse {m q : ℕ} (D : Data (K := K) m q)
    (hdet : (quadraticMatrix D.Q0).det ≠ 0)
    (v : Fin q → K) (z : PowerSeries K) (hz : PowerSeries.coeff 0 z = 0) :
    normalBlock D v z * (normalBlock D v z)⁻¹ = 1 :=
  Matrix.mul_nonsing_inv _ (normalBlock_isUnit_det D hdet v z hz)

/-- Multiplication by one half does not change the rank of the actual first
normal quadratic Hessian. -/
theorem half_quadraticMatrix_rank {m : ℕ} (Q : MvPolynomial (Fin m) K) :
    ((2 : K)⁻¹ • quadraticMatrix Q).rank = (quadraticMatrix Q).rank := by
  have hu : IsUnit (((2 : K)⁻¹ • (1 : Matrix (Fin m) (Fin m) K)).det) := by
    rw [Matrix.det_smul, Matrix.det_one, mul_one]
    exact (isUnit_iff_ne_zero.mpr (inv_ne_zero (by norm_num))).pow _
  simpa only [Matrix.smul_mul, Matrix.one_mul] using
    Matrix.rank_mul_eq_right_of_isUnit_det
      ((2 : K)⁻¹ • (1 : Matrix (Fin m) (Fin m) K)) (quadraticMatrix Q) hu

/-- An actual determinant factorization transverse to the normal line gives
the first normal rank inequality. No first-normal matrix is assumed as input. -/
theorem normal_rank_bound_of_determinant_factor {m q : ℕ}
    (D : Data (K := K) m q) (hB0 : (quadraticMatrix D.Q0).det ≠ 0)
    (h : ℕ) (G : MvPolynomial (Coordinate m q) K)
    (hG : eval (basePoint m q) G ≠ 0)
    (hdet : (polynomialHessian D).det = polynomial D ^ h * G) :
    2 * m ≤ h + (quadraticMatrix D.QA).rank := by
  let N := normalBlock D 0 PowerSeries.X
  letI : Invertible N := invertibleOfRightInverse N N⁻¹
    (normalBlock_mul_inverse D hB0 0 PowerSeries.X (by simp))
  have hfactor : (Matrix.fromBlocks (aBlock D 0 PowerSeries.X)
      (crossBlock D 0 PowerSeries.X) (crossBlock D 0 PowerSeries.X).transpose N).det =
      seriesEval 0 PowerSeries.X (polynomial D) ^ h * seriesEval 0 PowerSeries.X G := by
    rw [hessianSeries_fromBlocks]
    have hm := congrArg (seriesEval (m := m) 0 PowerSeries.X) hdet
    rw [map_mul, map_pow, RingHom.map_det] at hm
    exact hm
  have hD0 : SchurSecondOrder.matrixCoeff 0 (crossBlock D 0 PowerSeries.X).transpose = 0 := by
    rw [SchurSecondOrder.matrixCoeff_transpose, crossBlock_normalLine_coeff_zero]
    rfl
  have hf0 : PowerSeries.constantCoeff
      (seriesEval 0 PowerSeries.X (polynomial D)) = 0 := by
    simpa only [PowerSeries.coeff_zero_eq_constantCoeff_apply] using
      polynomial_normalLine_coeff_zero D
  have hd0 : PowerSeries.constantCoeff (seriesEval (m := m) 0 PowerSeries.X G) ≠ 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply,
      coeff_zero_seriesEval 0 PowerSeries.X (by simp) G]
    exact hG
  have hb := SimpleNormalRank.first_normal_block_rank_bound
    (aBlock D 0 PowerSeries.X) (crossBlock D 0 PowerSeries.X)
    (crossBlock D 0 PowerSeries.X).transpose N
    (seriesEval 0 PowerSeries.X (polynomial D)) (seriesEval 0 PowerSeries.X G) h
    (aBlock_normalLine_coeff_zero D) (crossBlock_normalLine_coeff_zero D) hD0 hf0
    (by rw [polynomial_normalLine_coeff_one]; exact one_ne_zero) hd0 hfactor
  simpa only [Fintype.card_fin, aBlock_normalLine_coeff_one] using hb

section Geometric

variable {m q : ℕ} (D : Data (K := GeometricField) m q)

/-- A rank condition on every actual geometric point of this irreducible
hypersurface forces the Schur complement to vanish on every actual formal
root. This uses the proved bordered-minor Nullstellensatz argument. -/
theorem schur_zero_of_geometric_rank
    (hF : Irreducible (polynomial D))
    (hdet : (quadraticMatrix D.Q0).det ≠ 0)
    (hRank : ∀ x : Coordinate m q → GeometricField, eval x (polynomial D) = 0 →
      ((polynomialHessian D).map (eval x)).rank ≤ q + 2)
    (v : Fin q → GeometricField) (z : PowerSeries GeometricField)
    (hz : PowerSeries.coeff 0 z = 0) (hroot : seriesEval v z (polynomial D) = 0) :
    aBlock D v z - crossBlock D v z * (normalBlock D v z)⁻¹ *
      (crossBlock D v z).transpose = 0 := by
  have h := PolynomialSchurVanishing.schur_eq_zero_of_geometric_rank_le
    (polynomial D) hF (polynomialHessian D).toBlocks₁₁
    (polynomialHessian D).toBlocks₁₂ (polynomialHessian D).toBlocks₂₁
    (polynomialHessian D).toBlocks₂₂
    (by
      intro x hx
      rw [Matrix.fromBlocks_toBlocks]
      simpa only [Fintype.card_sum, Fintype.card_fin] using hRank x hx)
    (seriesEval v z) hroot (normalBlock D v z)⁻¹
    (normalBlock_mul_inverse D hdet v z hz)
  have h21 : (polynomialHessian D).toBlocks₂₁.map (seriesEval v z) =
      (crossBlock D v z).transpose := by
    apply Matrix.ext
    intro i j
    exact congrArg (seriesEval v z)
      (partials_commute_general (polynomial D) (Sum.inl j) (Sum.inr i))
  rw [h21] at h
  exact h

/-- The complete source Schur relations, derived from the displayed cubic
expression and an actual geometric Hessian-rank bound. The sole external
input is the general simple-root theorem for formal power series. -/
theorem clifford_relations_of_geometric_rank
    (FI : FormalImplicitFunctionInput GeometricField)
    (hF : Irreducible (polynomial D))
    (hdet : (quadraticMatrix D.Q0).det ≠ 0)
    (hRank : ∀ x : Coordinate m q → GeometricField, eval x (polynomial D) = 0 →
      ((polynomialHessian D).map (eval x)).rank ≤ q + 2) :
    ∀ i j,
      quadraticMatrix (D.Q i) * (quadraticMatrix D.Q0)⁻¹ * quadraticMatrix (D.Q j) +
        quadraticMatrix (D.Q j) * (quadraticMatrix D.Q0)⁻¹ * quadraticMatrix (D.Q i) =
      (-2 * (((2 : GeometricField)⁻¹ • quadraticMatrix D.QA) i j)) •
        quadraticMatrix D.Q0 := by
  classical
  choose Z hZ hroot using fun v => exists_formal_root FI D v
  exact clifford_relations_of_formal_roots D hdet Z hZ hroot
    (fun v => (normalBlock D v (Z v))⁻¹)
    (fun v => normalBlock_mul_inverse D hdet v (Z v) (hZ v))
    (fun v => schur_zero_of_geometric_rank D hF hdet hRank v (Z v) (hZ v) (hroot v))

/-- Two nondegenerate first normal directions force an even middle block. -/
theorem two_dvd_of_geometric_rank
    (FI : FormalImplicitFunctionInput GeometricField)
    (hF : Irreducible (polynomial D))
    (hdet : (quadraticMatrix D.Q0).det ≠ 0)
    (hRank : ∀ x : Coordinate m q → GeometricField, eval x (polynomial D) = 0 →
      ((polynomialHessian D).map (eval x)).rank ≤ q + 2)
    (hP : 2 ≤ (quadraticMatrix D.QA).rank) : 2 ∣ q := by
  exact CliffordNormalization.two_dvd_of_schur_relations
    ((2 : GeometricField)⁻¹ • quadraticMatrix D.QA)
    (Matrix.IsSymm.smul (quadraticMatrix_symmetric D.QA) _)
    (by rwa [half_quadraticMatrix_rank]) (quadraticMatrix D.Q0) hdet
    (fun i => quadraticMatrix (D.Q i))
    (clifford_relations_of_geometric_rank D FI hF hdet hRank)

/-- Three nondegenerate first normal directions force a middle block whose
dimension is divisible by four; common self-adjointness is derived from the
actual symmetric quadratic Hessians. -/
theorem four_dvd_of_geometric_rank
    (FI : FormalImplicitFunctionInput GeometricField)
    (hF : Irreducible (polynomial D))
    (hdet : (quadraticMatrix D.Q0).det ≠ 0)
    (hRank : ∀ x : Coordinate m q → GeometricField, eval x (polynomial D) = 0 →
      ((polynomialHessian D).map (eval x)).rank ≤ q + 2)
    (hP : 3 ≤ (quadraticMatrix D.QA).rank) : 4 ∣ q := by
  exact CliffordNormalization.four_dvd_of_schur_relations
    ((2 : GeometricField)⁻¹ • quadraticMatrix D.QA)
    (Matrix.IsSymm.smul (quadraticMatrix_symmetric D.QA) _)
    (by rwa [half_quadraticMatrix_rank]) (quadraticMatrix D.Q0) hdet
    (quadraticMatrix_symmetric D.Q0) (fun i => quadraticMatrix (D.Q i))
    (fun i => quadraticMatrix_symmetric (D.Q i))
    (clifford_relations_of_geometric_rank D FI hF hdet hRank)

end Geometric
end HessianTheorem11.LocalCubicNormalForm
