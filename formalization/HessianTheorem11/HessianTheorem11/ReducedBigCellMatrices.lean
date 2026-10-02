import HessianTheorem11.NonzeroLimitTransport

/-! Ordinary big-cell and orbit-map openness interfaces, separated from the
specialized orbit-curve factorization. Their exact two textbook hypotheses
remain explicit; the weight-curve argument is proved in ReducedBigCell.

References: Milne, Algebraic Groups, corrected 2022 edition, Theorem 13.33(d)
p. 266; Proposition 1.65(a),(c), pp. 26–27 and A.69, p. 586. -/
noncomputable section
namespace HessianTheorem11.ReducedBigCell
open MvPolynomial PolynomialRestriction PolynomialWeightTransport NonzeroLimitTransport
open scoped BigOperators

/-- The ordinary opposite big cell contains a principal neighborhood of the
identity in SL. This concerns matrices only: no form, orbit, or limit occurs. -/
structure SpecialLinearBigCellInput : Prop where
  principal_neighborhood : ∀ {n : ℕ} (w : Fin n → ℤ),
    ∃ q : MvPolynomial (Fin n × Fin n) GeometricField,
      eval (fun ij => (1 : Matrix (Fin n) (Fin n) GeometricField) ij.1 ij.2) q ≠ 0 ∧
      ∀ A : Matrix (Fin n) (Fin n) GeometricField, A.det = 1 →
        eval (fun ij => A ij.1 ij.2) q ≠ 0 →
        ∃ U V P : Matrix (Fin n) (Fin n) GeometricField,
          A = P * U ∧ U * V = 1 ∧ V.det = 1 ∧
          WeightUpperUnipotent w U ∧ WeightUpperUnipotent w V ∧
          WeightLowerTriangular w P

/-- Openness of the orbit map for the ordinary SL representation on forms,
expressed in principal coefficient neighborhoods. It has no closed-orbit,
weight, or curve hypothesis and asserts no unipotent factorization. -/
structure FormOrbitOpenMapInput : Prop where
  principal_image : ∀ {n d : ℕ} (F : GeometricPolynomial n), F.IsHomogeneous d →
    ∀ q : MvPolynomial (Fin n × Fin n) GeometricField,
      eval (fun ij => (1 : Matrix (Fin n) (Fin n) GeometricField) ij.1 ij.2) q ≠ 0 →
    ∃ p : MvPolynomial (Fin n →₀ ℕ) GeometricField,
      eval (fun e => coeff e F) p ≠ 0 ∧
      ∀ G ∈ slOrbit F, eval (fun e => coeff e G) p ≠ 0 →
        ∃ A : Matrix (Fin n) (Fin n) GeometricField,
          A.det = 1 ∧ eval (fun ij => A ij.1 ij.2) q ≠ 0 ∧ G = restrict A F

variable {K : Type*} [Field K] {n : ℕ}

def diagonalConjugate (a : Fin n → K) (A : Matrix (Fin n) (Fin n) K) :
    Matrix (Fin n) (Fin n) K :=
  Matrix.diagonal a * A * Matrix.diagonal (fun i => (a i)⁻¹)

@[simp] theorem diagonalConjugate_apply (a : Fin n → K)
    (A : Matrix (Fin n) (Fin n) K) (i j : Fin n) :
    diagonalConjugate a A i j = a i * A i j * (a j)⁻¹ := by
  simp [diagonalConjugate, Matrix.diagonal_mul, Matrix.mul_diagonal]

theorem diagonalConjugate_upper (a : Fin n → K) (ha : ∀ i, a i ≠ 0)
    (w : Fin n → ℤ) (A : Matrix (Fin n) (Fin n) K)
    (hA : WeightUpperUnipotent w A) :
    WeightUpperUnipotent w (diagonalConjugate a A) := by
  constructor
  · intro i
    simp [hA.1 i, ha i]
  · intro i j hij hw
    simp [hA.2 i j hij hw]

theorem diagonalConjugate_lower (a : Fin n → K) (w : Fin n → ℤ)
    (A : Matrix (Fin n) (Fin n) K) (hA : WeightLowerTriangular w A) :
    WeightLowerTriangular w (diagonalConjugate a A) := by
  intro i j hij
  apply hA i j
  intro hz
  exact hij (by simp [hz])

theorem diagonal_mul_inverse (a : Fin n → K) (ha : ∀ i, a i ≠ 0) :
    Matrix.diagonal a * Matrix.diagonal (fun i => (a i)⁻¹) = 1 := by
  classical
  simp [Matrix.diagonal_mul_diagonal, ha]

theorem diagonal_inverse_mul (a : Fin n → K) (ha : ∀ i, a i ≠ 0) :
    Matrix.diagonal (fun i => (a i)⁻¹) * Matrix.diagonal a = 1 := by
  classical
  simp [Matrix.diagonal_mul_diagonal, ha]

theorem diagonalConjugate_mul (a : Fin n → K) (ha : ∀ i, a i ≠ 0)
    (A B : Matrix (Fin n) (Fin n) K) :
    diagonalConjugate a A * diagonalConjugate a B = diagonalConjugate a (A * B) := by
  unfold diagonalConjugate
  calc
    _ = Matrix.diagonal a * A *
        (Matrix.diagonal (fun i => (a i)⁻¹) * Matrix.diagonal a) * B *
        Matrix.diagonal (fun i => (a i)⁻¹) := by noncomm_ring
    _ = _ := by rw [diagonal_inverse_mul a ha]; simp [Matrix.mul_assoc]

@[simp] theorem diagonalConjugate_one (a : Fin n → K) (ha : ∀ i, a i ≠ 0) :
    diagonalConjugate a (1 : Matrix (Fin n) (Fin n) K) = 1 := by
  simpa [diagonalConjugate] using diagonal_mul_inverse a ha

theorem diagonalConjugate_det (a : Fin n → K) (ha : ∀ i, a i ≠ 0)
    (A : Matrix (Fin n) (Fin n) K) : (diagonalConjugate a A).det = A.det := by
  have h : (Matrix.diagonal a).det *
      (Matrix.diagonal (fun i => (a i)⁻¹)).det = 1 := by
    rw [← Matrix.det_mul, diagonal_mul_inverse a ha, Matrix.det_one]
  unfold diagonalConjugate
  rw [Matrix.det_mul, Matrix.det_mul]
  calc
    _ = A.det * ((Matrix.diagonal a).det *
        (Matrix.diagonal (fun i => (a i)⁻¹)).det) := by ring
    _ = A.det := by rw [h, mul_one]

end HessianTheorem11.ReducedBigCell
