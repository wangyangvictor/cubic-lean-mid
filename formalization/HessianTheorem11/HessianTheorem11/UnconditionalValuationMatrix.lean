import HessianTheorem11.UnconditionalValuationMatrixOperations

/-! Finite-dimensional Cartan diagonal factorization over an arbitrary
valuation subring of a field, proved by integral Gaussian induction.
No discreteness, rank-one, completeness, or PID assumption is imposed. -/
noncomputable section
namespace HessianTheorem11.UnconditionalValuationMatrix
open Matrix
variable {K : Type*} [Field K] (V : ValuationSubring K)

/-- Every square field matrix admits a diagonal reduction by matrices
invertible over V. Zero diagonal entries are permitted here, so induction
does not need a separate nonsingularity argument on the remaining block. -/
theorem hasDiagonalReduction (n : ℕ) :
    ∀ M : Matrix (Fin n) (Fin n) K, HasDiagonalReduction V M := by
  classical
  induction n with
  | zero =>
    intro M
    have hM : M = 0 := Subsingleton.elim _ _
    rw [hM]
    exact zero_hasDiagonalReduction V
  | succ r ih =>
    intro M
    let e : Fin (r+1) ≃ Fin r ⊕ Unit := Fintype.equivOfCardEq (by simp)
    apply hasDiagonalReduction_of_reindex V e M
    let N := Matrix.reindexAlgEquiv K K e M
    change HasDiagonalReduction V N
    by_cases hN : N = 0
    · rw [hN]
      exact zero_hasDiagonalReduction V
    obtain ⟨i,j,hp,hdiv⟩ := exists_dominating_entry V N hN
    let er : Equiv.Perm (Fin r ⊕ Unit) := Equiv.swap (Sum.inr ()) i
    let ec : Equiv.Perm (Fin r ⊕ Unit) := Equiv.swap (Sum.inr ()) j
    let Q := N.submatrix er ec
    have hcorner : Q (Sum.inr ()) (Sum.inr ()) = N i j := by simp [Q,er,ec]
    have hQ : Q (Sum.inr ()) (Sum.inr ()) ≠ 0 := by rw [hcorner]; exact hp
    have hQdiv : ∀ a b, Q a b / Q (Sum.inr ()) (Sum.inr ()) ∈ V := by
      intro a b
      rw [hcorner]
      exact hdiv (er a) (ec b)
    apply hasDiagonalReduction_of_permute V er ec N
    obtain ⟨A,B,hA,hB,hblock⟩ := integral_pivot_block V Q hQ hQdiv
    apply hasDiagonalReduction_of_operations V Q A B hA hB
    exact block_hasDiagonalReduction V _ hblock (ih _)

/-- Actual Cartan factorization. Both outer matrices are units over the
valuation subring, not merely matrices with integral entries. The middle
entries are nonzero for an invertible input matrix. -/
theorem exists_factorization {n : ℕ} (M : Matrix (Fin n) (Fin n) K)
    (hM : M.det ≠ 0) :
    ∃ (A B : Matrix (Fin n) (Fin n) V) (d : Fin n → K),
      IsUnit A ∧ IsUnit B ∧ (∀ i, d i ≠ 0) ∧
      M = matrixMap V A * diagonal d * matrixMap V B := by
  obtain ⟨A₀,B₀,hA,hB,d,hd⟩ := hasDiagonalReduction V n M
  obtain ⟨A,rfl⟩ := hA
  obtain ⟨B,rfl⟩ := hB
  have hAA : matrixMap V (↑A⁻¹ : Matrix (Fin n) (Fin n) V) * matrixMap V (↑A) = 1 := by
    rw [←map_mul]
    simp
  have hBB : matrixMap V (↑B : Matrix (Fin n) (Fin n) V) * matrixMap V (↑B⁻¹) = 1 := by
    rw [←map_mul]
    simp
  have he : M = matrixMap V (↑A⁻¹) * diagonal d * matrixMap V (↑B⁻¹) := by
    calc
      M = (matrixMap V (↑A⁻¹) * matrixMap V (↑A)) * M *
          (matrixMap V (↑B) * matrixMap V (↑B⁻¹)) := by rw [hAA,hBB]; simp
      _ = matrixMap V (↑A⁻¹) * (matrixMap V (↑A) * M * matrixMap V (↑B)) *
          matrixMap V (↑B⁻¹) := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hd]
  refine ⟨↑A⁻¹,↑B⁻¹,d,(A⁻¹).isUnit,(B⁻¹).isUnit,?_,he⟩
  have hz : (diagonal d).det ≠ 0 := by
    intro h
    apply hM
    rw [he,Matrix.det_mul,Matrix.det_mul,h,mul_zero,zero_mul]
  rw [Matrix.det_diagonal] at hz
  intro i
  exact (Finset.prod_ne_zero_iff.mp hz) i (Finset.mem_univ i)

end HessianTheorem11.UnconditionalValuationMatrix
