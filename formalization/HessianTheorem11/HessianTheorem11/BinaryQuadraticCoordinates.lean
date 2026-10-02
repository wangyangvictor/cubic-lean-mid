import HessianTheorem11.PolynomialImageRelations
import HessianTheorem11.QuadricLowRank

/-! Explicit coordinates and normalization for three independent binary
quadrics. These are polynomial identities, not geometric classification inputs. -/
noncomputable section
namespace HessianTheorem11
open MvPolynomial Matrix Module
variable {K : Type*} [Field K] [CharZero K]

def binaryQuadraticMonomials : Fin 3 → MvPolynomial (Fin 2) K :=
  ![X 0 ^ 2, X 0 * X 1, X 1 ^ 2]

def binaryQuadraticCoefficients (Q : MvPolynomial (Fin 2) K) : Fin 3 → K :=
  ![eval ![1,0] Q, eval ![1,1] Q - eval ![1,0] Q - eval ![0,1] Q, eval ![0,1] Q]

theorem binaryQuadratic_expansion (Q : MvPolynomial (Fin 2) K)
    (hQ : Q.IsHomogeneous 2) :
    Q = ∑ j : Fin 3, C (binaryQuadraticCoefficients Q j) * binaryQuadraticMonomials j := by
  apply MvPolynomial.funext
  intro x
  have he := quadratic_eval_two_vector_expansion Q hQ
    (![1,0] : Fin 2 → K) ![0,1] (x 0) (x 1)
  have hx : x 0 • (![1,0] : Fin 2 → K) + x 1 • ![0,1] = x := by
    ext i
    fin_cases i <;> simp
  have hone : (![1,0] : Fin 2 → K) + ![0,1] = ![1,1] := by
    ext i
    fin_cases i <;> simp
  rw [hx, hone] at he
  simpa [binaryQuadraticCoefficients, binaryQuadraticMonomials, Fin.sum_univ_three,
    mul_comm, mul_left_comm, mul_assoc] using he

def combinePolynomials {r s : ℕ} {σ : Type*}
    (A : Matrix (Fin r) (Fin s) K) (P : Fin s → MvPolynomial σ K) :
    Fin r → MvPolynomial σ K := (A.map C).mulVec P

theorem combinePolynomials_apply {r s : ℕ} {σ : Type*}
    (A : Matrix (Fin r) (Fin s) K) (P : Fin s → MvPolynomial σ K) (i : Fin r) :
    combinePolynomials A P i = ∑ j, C (A i j) * P j := rfl

theorem combinePolynomials_comp {r s t : ℕ} {σ : Type*}
    (A : Matrix (Fin r) (Fin s) K) (B : Matrix (Fin s) (Fin t) K)
    (P : Fin t → MvPolynomial σ K) :
    combinePolynomials A (combinePolynomials B P) = combinePolynomials (A * B) P := by
  unfold combinePolynomials
  rw [Matrix.mulVec_mulVec, Matrix.map_mul]

theorem combinePolynomials_one {r : ℕ} {σ : Type*}
    (P : Fin r → MvPolynomial σ K) : combinePolynomials 1 P = P := by
  simp [combinePolynomials, Matrix.map_one]

theorem combinePolynomials_homogeneous {r s d : ℕ} {σ : Type*}
    (A : Matrix (Fin r) (Fin s) K) (P : Fin s → MvPolynomial σ K)
    (hP : ∀ j, (P j).IsHomogeneous d) :
    ∀ i, (combinePolynomials A P i).IsHomogeneous d := by
  intro i
  rw [combinePolynomials_apply]
  apply IsHomogeneous.sum
  intro j _
  simpa using (isHomogeneous_C σ (A i j)).mul (hP j)

theorem combinePolynomials_restrict {r s n k : ℕ}
    (A : Matrix (Fin r) (Fin s) K) (P : Fin s → MvPolynomial (Fin n) K)
    (B : Matrix (Fin n) (Fin k) K) :
    (fun i => PolynomialRestriction.restrict B (combinePolynomials A P i)) =
      combinePolynomials A (fun j => PolynomialRestriction.restrict B (P j)) := by
  ext i
  simp [combinePolynomials_apply, PolynomialRestriction.restrict]

theorem span_combinePolynomials_le {r s : ℕ} {σ : Type*}
    (A : Matrix (Fin r) (Fin s) K) (P : Fin s → MvPolynomial σ K) :
    Submodule.span K (Set.range (combinePolynomials A P)) ≤
      Submodule.span K (Set.range P) := by
  apply Submodule.span_le.mpr
  rintro _ ⟨i, rfl⟩
  rw [combinePolynomials_apply]
  apply Submodule.sum_mem
  intro j _
  rw [← MvPolynomial.smul_eq_C_mul]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j,rfl⟩)

theorem span_combinePolynomials_eq {r : ℕ} {σ : Type*}
    (A : Matrix (Fin r) (Fin r) K) (hA : IsUnit A) (P : Fin r → MvPolynomial σ K) :
    Submodule.span K (Set.range (combinePolynomials A P)) =
      Submodule.span K (Set.range P) := by
  apply le_antisymm (span_combinePolynomials_le A P)
  have h := span_combinePolynomials_le A⁻¹ (combinePolynomials A P)
  rw [combinePolynomials_comp, Matrix.nonsing_inv_mul _
    ((Matrix.isUnit_iff_isUnit_det A).mp hA), combinePolynomials_one] at h
  exact h

theorem combinePolynomials_linearIndependent {r : ℕ} {σ : Type*}
    (A : Matrix (Fin r) (Fin r) K) (hA : IsUnit A)
    (P : Fin r → MvPolynomial σ K) (hP : LinearIndependent K P) :
    LinearIndependent K (combinePolynomials A P) := by
  rw [linearIndependent_iff_card_eq_finrank_span]
  change Fintype.card (Fin r) = finrank K (Submodule.span K
    (Set.range (combinePolynomials A P)))
  rw [span_combinePolynomials_eq A hA P]
  exact (finrank_span_eq_card hP).symm

def outputLinearForms {r s : ℕ} (A : Matrix (Fin r) (Fin s) K) :
    Fin r → MvPolynomial (Fin s) K := fun i => ∑ j, C (A i j) * X j

theorem aeval_outputLinearForms {r s : ℕ} {σ : Type*}
    (A : Matrix (Fin r) (Fin s) K) (P : Fin s → MvPolynomial σ K) :
    (fun i => aeval P (outputLinearForms A i)) = combinePolynomials A P := by
  funext i
  simp [outputLinearForms, combinePolynomials_apply]

theorem combinePolynomials_relation_transfer {r s n k : ℕ}
    (A : Matrix (Fin r) (Fin s) GeometricField)
    (P : Fin s → GeometricPolynomial n) (Q : Fin s → GeometricPolynomial k)
    (h : geometricClosure (polynomialMap P '' Set.univ) =
      geometricClosure (polynomialMap Q '' Set.univ))
    (R : GeometricPolynomial r) :
    aeval (combinePolynomials A P) R = 0 ↔ aeval (combinePolynomials A Q) R = 0 := by
  have he := aeval_relation_iff_of_same_imageClosure P Q h (aeval (outputLinearForms A) R)
  simpa only [comp_aeval_apply, aeval_outputLinearForms] using he

def binaryQuadraticCoefficientMatrix (Q : Fin 3 → MvPolynomial (Fin 2) K) :
    Matrix (Fin 3) (Fin 3) K := fun i j => binaryQuadraticCoefficients (Q i) j

theorem binaryQuadratic_coefficient_matrix_unit
    (Q : Fin 3 → MvPolynomial (Fin 2) K)
    (hQ : ∀ j, (Q j).IsHomogeneous 2) (hli : LinearIndependent K Q) :
    IsUnit (binaryQuadraticCoefficientMatrix Q) := by
  let A := binaryQuadraticCoefficientMatrix Q
  let L := Fintype.linearCombination K (binaryQuadraticMonomials (K := K))
  have he : L ∘ A.row = Q := by
    funext i
    change L (A.row i) = Q i
    rw [binaryQuadratic_expansion (Q i) (hQ i)]
    simp [L, A, binaryQuadraticCoefficientMatrix, Matrix.row,
      Fintype.linearCombination_apply, MvPolynomial.smul_eq_C_mul]
  have hrow : LinearIndependent K A.row := LinearIndependent.of_comp L (he.symm ▸ hli)
  apply Matrix.vecMul_injective_iff_isUnit.mp
  exact Matrix.vecMul_injective_iff.mpr hrow

theorem binaryQuadratic_normalize
    (Q : Fin 3 → MvPolynomial (Fin 2) K)
    (hQ : ∀ j, (Q j).IsHomogeneous 2) (hli : LinearIndependent K Q) :
    ∃ A : Matrix (Fin 3) (Fin 3) K, IsUnit A ∧
      combinePolynomials A Q = binaryQuadraticMonomials := by
  let B := binaryQuadraticCoefficientMatrix Q
  have hB : IsUnit B := binaryQuadratic_coefficient_matrix_unit Q hQ hli
  have hQe : Q = combinePolynomials B binaryQuadraticMonomials := by
    funext i
    exact binaryQuadratic_expansion (Q i) (hQ i)
  refine ⟨B⁻¹, Matrix.isUnit_nonsing_inv_iff.mpr hB, ?_⟩
  rw [hQe, combinePolynomials_comp, Matrix.nonsing_inv_mul _
    ((Matrix.isUnit_iff_isUnit_det B).mp hB),
    combinePolynomials_one]

end HessianTheorem11
