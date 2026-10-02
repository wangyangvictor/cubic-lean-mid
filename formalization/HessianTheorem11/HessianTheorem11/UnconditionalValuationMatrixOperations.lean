import HessianTheorem11.UnconditionalValuationMatrixPivot

/-! Integral row and column equivalence, permutation operations, and
extension of a reduction from a diagonal block. -/
noncomputable section
namespace HessianTheorem11.UnconditionalValuationMatrix
open Matrix
variable {K : Type*} [Field K] (V : ValuationSubring K)

/-- A diagonal reduction whose two transforming matrices are invertible
over the actual valuation subring. -/
def HasDiagonalReduction {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι K) : Prop :=
  ∃ A B : Matrix ι ι V, IsUnit A ∧ IsUnit B ∧
    ∃ d : ι → K, matrixMap V A * M * matrixMap V B = diagonal d

theorem zero_hasDiagonalReduction {ι : Type*} [Fintype ι] [DecidableEq ι] :
    HasDiagonalReduction V (0 : Matrix ι ι K) := by
  exact ⟨1,1,isUnit_one,isUnit_one,0,by ext i j; simp [Matrix.diagonal]⟩

theorem hasDiagonalReduction_of_operations {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι K) (A B : Matrix ι ι V) (hA : IsUnit A) (hB : IsUnit B)
    (h : HasDiagonalReduction V (matrixMap V A * M * matrixMap V B)) :
    HasDiagonalReduction V M := by
  obtain ⟨C,D,hC,hD,d,hd⟩ := h
  refine ⟨C*A,B*D,hC.mul hA,hB.mul hD,d,?_⟩
  simpa only [map_mul,Matrix.mul_assoc] using hd

@[simp] theorem matrixMap_reindex {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] (e : ι ≃ κ) (A : Matrix ι ι V) :
    matrixMap V (Matrix.reindexAlgEquiv V V e A) =
      Matrix.reindexAlgEquiv K K e (matrixMap V A) := rfl

theorem hasDiagonalReduction_of_reindex {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] (e : ι ≃ κ) (M : Matrix ι ι K)
    (h : HasDiagonalReduction V (Matrix.reindexAlgEquiv K K e M)) :
    HasDiagonalReduction V M := by
  obtain ⟨A,B,hA,hB,d,hd⟩ := h
  refine ⟨Matrix.reindexAlgEquiv V V e.symm A,Matrix.reindexAlgEquiv V V e.symm B,
    hA.map _,hB.map _,d ∘ e,?_⟩
  have hh := congrArg (Matrix.reindexAlgEquiv K K e.symm) hd
  simpa only [map_mul,←matrixMap_reindex,Matrix.reindexAlgEquiv_apply,
    Matrix.reindex_apply,Matrix.submatrix_submatrix,Equiv.symm_symm,
    Equiv.symm_comp_self,Matrix.submatrix_id_id,Matrix.submatrix_diagonal_equiv] using hh

/-- Permutation matrices and their inverse have entries in V. -/
theorem permutation_isUnit {ι : Type*} [Fintype ι] [DecidableEq ι]
    (e : Equiv.Perm ι) : IsUnit (e.toPEquiv.toMatrix : Matrix ι ι V) := by
  have h (e : Equiv.Perm ι) :
      (e.toPEquiv.toMatrix : Matrix ι ι V) * e.symm.toPEquiv.toMatrix = 1 := by
    rw [PEquiv.toMatrix_toPEquiv_mul]
    ext i j
    simp [PEquiv.toMatrix_apply,Matrix.one_apply]
  exact ⟨⟨e.toPEquiv.toMatrix,e.symm.toPEquiv.toMatrix,h e,h e.symm⟩,rfl⟩

@[simp] theorem matrixMap_permutation {ι : Type*} [Fintype ι] [DecidableEq ι]
    (e : Equiv.Perm ι) :
    matrixMap V (e.toPEquiv.toMatrix : Matrix ι ι V) = (e.toPEquiv.toMatrix : Matrix ι ι K) :=
  PEquiv.map_toMatrix V.subtype _

theorem hasDiagonalReduction_of_permute {ι : Type*} [Fintype ι] [DecidableEq ι]
    (er ec : Equiv.Perm ι) (M : Matrix ι ι K)
    (h : HasDiagonalReduction V (M.submatrix er ec)) : HasDiagonalReduction V M := by
  apply hasDiagonalReduction_of_operations V M
    (er.toPEquiv.toMatrix) (ec.symm.toPEquiv.toMatrix)
    (permutation_isUnit V er) (permutation_isUnit V ec.symm)
  simpa only [matrixMap_permutation,PEquiv.toMatrix_toPEquiv_mul,
    PEquiv.mul_toMatrix_toPEquiv,Matrix.submatrix_submatrix,Equiv.symm_symm,
    Function.comp_id,Function.id_comp] using h

/-- A unit on the leading block extends by the identity on the complementary
block to a unit over V. -/
theorem block_unit {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] (A : Matrix ι ι V) (hA : IsUnit A) :
    IsUnit (fromBlocks A 0 0 (1 : Matrix κ κ V)) := by
  apply (Matrix.isUnit_iff_isUnit_det _).mpr
  rw [Matrix.det_fromBlocks_zero₂₁,Matrix.det_one,mul_one]
  exact (Matrix.isUnit_iff_isUnit_det _).mp hA

@[simp] theorem matrixMap_block {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] (A : Matrix ι ι V) :
    matrixMap V (fromBlocks A 0 0 (1 : Matrix κ κ V)) =
      fromBlocks (matrixMap V A) 0 0 (1 : Matrix κ κ K) := by
  ext (i|i) (j|j) <;> simp [matrixMap,Matrix.fromBlocks,Matrix.one_apply,apply_ite]

theorem block_hasDiagonalReduction {r : ℕ}
    (M : Matrix (Fin r ⊕ Unit) (Fin r ⊕ Unit) K) (hM : IsTwoBlockDiagonal M)
    (h : HasDiagonalReduction V (Matrix.toBlocks₁₁ M)) : HasDiagonalReduction V M := by
  obtain ⟨A,B,hA,hB,d,hd⟩ := h
  let a := M (Sum.inr ()) (Sum.inr ())
  have he : M = fromBlocks (Matrix.toBlocks₁₁ M) 0 0 (diagonal (fun _ : Unit => a)) := by
    rw [←Matrix.fromBlocks_toBlocks M,hM.1,hM.2]
    rfl
  refine ⟨fromBlocks A 0 0 1,fromBlocks B 0 0 1,
    block_unit V A hA,block_unit V B hB,Sum.elim d (fun _ => a),?_⟩
  rw [matrixMap_block,matrixMap_block,he]
  simp [Matrix.fromBlocks_multiply, hd]

end HessianTheorem11.UnconditionalValuationMatrix
