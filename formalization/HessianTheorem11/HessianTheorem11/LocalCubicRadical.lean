import HessianTheorem11.LocalCubicSchur
import HessianTheorem11.NilpotentRadical
import HessianTheorem11.MatrixRankBounds

noncomputable section
namespace HessianTheorem11.LocalCubicNormalForm
open MvPolynomial Matrix Module CliffordNormalization

section SchurRadical
variable {K : Type*} [Field K] [CharZero K] [IsAlgClosed K] {m q : ℕ}

theorem schur_radical_middle_rank_le_two
    (P : Matrix (Fin m) (Fin m) K) (hP : P.IsSymm) (hRank : 1 ≤ P.rank)
    (B0 : Matrix (Fin q) (Fin q) K) (hB0 : B0.det ≠ 0) (hB0sym : B0.IsSymm)
    (B : Fin m → Matrix (Fin q) (Fin q) K) (hB : ∀ i, (B i).IsSymm)
    (hSchur : ∀ i j, B i * B0⁻¹ * B j + B j * B0⁻¹ * B i = (-2 * P i j) • B0)
    (v : Fin m → K) (hv : P.mulVec v = 0) (hq : q ≤ 7) :
    (∑ i, v i • B i).rank ≤ 2 := by
  let J := schurCliffordMap B0 B
  have hJ := schurCliffordMap_anticommutator P B0 hB0 B hSchur
  obtain ⟨u, hu, _⟩ := exists_anticommuting_involutions P hP hRank J hJ
  have hpair (w : Fin m → K) : Matrix.toBilin' P w v = 0 := by
    rw [Matrix.toBilin'_apply', hv]
    simp
  have hvv := hJ v v
  rw [hpair, mul_zero, zero_smul] at hvv
  have hN : J v * J v = 0 := by
    apply smul_right_injective (Module.End K (Fin q → K)) (by norm_num : (2 : K) ≠ 0)
    simpa only [two_smul K, smul_zero, add_zero] using hvv
  have hanti : J v * J (u 0) = -(J (u 0) * J v) := by
    have h := hJ (u 0) v
    rw [hpair, mul_zero, zero_smul] at h
    exact eq_neg_of_add_eq_zero_right h
  have hn := NilpotentRadical.rank_le_two_of_dimension_le_seven
    (Matrix.toBilin' B0) (LinearMap.BilinForm.nondegenerate_toBilin'_iff_det_ne_zero.mpr hB0)
    (toBilin'_isSymm B0 hB0sym) (J v) (J (u 0)) hN (hu 0) hanti
    (schurCliffordMap_self_adjoint B0 hB0 hB0sym B hB v)
    (schurCliffordMap_self_adjoint B0 hB0 hB0sym B hB (u 0)) (by simpa using hq)
  have hmap : J v = Matrix.toLinAlgEquiv' (B0⁻¹ * ∑ i, v i • B i) := by
    simp only [J, schurCliffordMap, Fintype.linearCombination_apply, schurGenerator,
      map_mul, map_sum, map_smul, Finset.mul_sum, mul_smul_comm]
  rw [hmap] at hn
  change (B0⁻¹ * ∑ i, v i • B i).rank ≤ 2 at hn
  have huinv : IsUnit (B0⁻¹).det := Matrix.isUnit_nonsing_inv_det B0 (isUnit_iff_ne_zero.mpr hB0)
  rwa [Matrix.rank_mul_eq_right_of_isUnit_det B0⁻¹ _ huinv] at hn

end SchurRadical

section PureRadicalPoint
variable {K : Type*} [Field K] {m q : ℕ}

def pureAPoint (v : Fin m → K) : Coordinate m q → K :=
  Sum.elim v (fun _ => 0)

@[simp] theorem pureAPoint_a (v : Fin m → K) (i : Fin m) :
    pureAPoint (q := q) v (aIndex i) = v i := rfl
@[simp] theorem pureAPoint_b (v : Fin m → K) (i : Fin q) :
    pureAPoint v (bIndex i) = 0 := rfl
@[simp] theorem pureAPoint_x (v : Fin m → K) : pureAPoint v (xIndex m q) = 0 := rfl
@[simp] theorem pureAPoint_z (v : Fin m → K) : pureAPoint v (zIndex m q) = 0 := rfl

@[simp] theorem eval_pureA_rename_a (v : Fin m → K) (p : MvPolynomial (Fin m) K) :
    eval (pureAPoint (q := q) v) (rename aIndex p) = eval v p := by
  rw [eval_rename]
  rfl

@[simp] theorem eval_pureA_rename_b (v : Fin m → K) (p : MvPolynomial (Fin q) K) :
    eval (pureAPoint v) (rename bIndex p) = eval 0 p := by
  rw [eval_rename]
  rfl

@[simp] theorem eval_pureA_rename_residual (v : Fin m → K)
    (p : MvPolynomial (ResidualCoordinate q) K) :
    eval (pureAPoint v) (rename residualIndex p) = eval 0 p := by
  rw [eval_rename]
  have he : pureAPoint (q := q) v ∘ residualIndex = (0 : ResidualCoordinate q → K) := by
    funext i
    cases i <;> simp [pureAPoint, residualIndex, bIndex, zIndex]
  rw [he]

theorem pureA_gradient_zero [CharZero K] (D : Data (K := K) m q) (v : Fin m → K)
    (hv : (quadraticMatrix D.QA).mulVec v = 0) :
    ∀ i, eval (pureAPoint v) (pderiv i (polynomial D)) = 0 := by
  have hQA : eval v D.QA = 0 := by
    have h := quadratic_eval_identity D.QA D.QA_homogeneous v
    rw [hv, dotProduct_zero] at h
    exact (mul_eq_zero.mp h.symm).resolve_left (by norm_num)
  have hQ0 : eval (0 : Fin q → K) D.Q0 = 0 :=
    eval_zero_positive_homogeneous _ D.Q0_homogeneous (by decide)
  have hQi (i : Fin m) : eval (0 : Fin q → K) (D.Q i) = 0 :=
    eval_zero_positive_homogeneous _ (D.Q_homogeneous i) (by decide)
  have hQip (i : Fin m) (j : Fin q) : eval (0 : Fin q → K) (pderiv j (D.Q i)) = 0 :=
    eval_zero_positive_homogeneous _ (D.Q_homogeneous i).pderiv (by decide)
  have hRp (i : ResidualCoordinate q) : eval (0 : ResidualCoordinate q → K) (pderiv i D.R) = 0 :=
    eval_zero_positive_homogeneous _ D.R_homogeneous.pderiv (by decide)
  simp only [eval_zero] at hQ0 hQi hQip hRp
  intro i
  rcases i with i | (i | i)
  · rw [show Sum.inl i = aIndex i from rfl, a_partial]
    simp [hQi]
  · rw [show Sum.inr (Sum.inl i) = bIndex i from rfl, b_partial]
    simp [hQip, hRp]
  · fin_cases i
    · change eval (pureAPoint v) (pderiv (xIndex m q) (polynomial D)) = 0
      rw [x_partial]
      simp [hQ0]
    · change eval (pureAPoint v) (pderiv (zIndex m q) (polynomial D)) = 0
      rw [z_partial]
      simp [hQA, hRp]

def pureAHessian (D : Data (K := K) m q) (v : Fin m → K) :
    Matrix (Coordinate m q) (Coordinate m q) K :=
  (polynomialHessian D).map (eval (pureAPoint v))

theorem pureAHessian_symmetric (D : Data (K := K) m q) (v : Fin m → K) :
    (pureAHessian D v).IsSymm := by
  ext i j
  exact congrArg (eval (pureAPoint v)) (partials_commute_general (polynomial D) i j)

theorem pureAHessian_a (D : Data (K := K) m q) (v : Fin m → K)
    (hv : (quadraticMatrix D.QA).mulVec v = 0) (i : Fin m) (j : Coordinate m q) :
    pureAHessian D v (aIndex i) j = 0 := by
  change eval (pureAPoint v) (pderiv j (pderiv (aIndex i) (polynomial D))) = 0
  rcases j with j | (j | j)
  · rw [show Sum.inl j = aIndex j from rfl, aa_partial]
    simp
  · rw [show Sum.inr (Sum.inl j) = bIndex j from rfl, ab_partial]
    have hp : eval (0 : Fin q → K) (pderiv j (D.Q i)) = 0 :=
      eval_zero_positive_homogeneous _ (D.Q_homogeneous i).pderiv (by decide)
    simp only [eval_zero] at hp
    simp [hp]
  · fin_cases j
    · change eval (pureAPoint v) (pderiv (xIndex m q) (pderiv (aIndex i) (polynomial D))) = 0
      rw [ax_partial, map_zero]
    · change eval (pureAPoint v) (pderiv (zIndex m q) (pderiv (aIndex i) (polynomial D))) = 0
      rw [az_partial]
      have hp : eval v (pderiv i D.QA) = 0 := by
        rw [quadratic_first_partial D.QA D.QA_homogeneous]
        simpa [Matrix.mulVec, dotProduct] using congrFun hv i
      simp [hp]

theorem pureAHessian_x (D : Data (K := K) m q) (v : Fin m → K) (j : Coordinate m q) :
    pureAHessian D v (xIndex m q) j = 0 := by
  classical
  change eval (pureAPoint v) (pderiv j (pderiv (xIndex m q) (polynomial D))) = 0
  rw [x_partial]
  rcases j with j | (j | j)
  · change eval (pureAPoint v) (pderiv (aIndex j) _) = 0
    simp only [map_add, pderiv_mul, pderiv_a_rename_b]
    simp [pderiv_mul, pderiv_X, Pi.single_apply, pureAPoint, aIndex, xIndex, zIndex]
  · change eval (pureAPoint v) (pderiv (bIndex j) _) = 0
    have hp : eval (0 : Fin q → K) (pderiv j D.Q0) = 0 :=
      eval_zero_positive_homogeneous _ D.Q0_homogeneous.pderiv (by decide)
    simp only [map_add, pderiv_mul, pderiv_b_rename_b, eval_pureA_rename_b, hp]
    simp [pderiv_mul, pderiv_X, Pi.single_apply, pureAPoint, bIndex, xIndex, zIndex, hp]
  · fin_cases j
    · change eval (pureAPoint v) (pderiv (xIndex m q) _) = 0
      simp only [map_add, pderiv_mul, pderiv_x_rename_b]
      simp [pderiv_mul, pderiv_X, Pi.single_apply, pureAPoint, xIndex, zIndex]
    · change eval (pureAPoint v) (pderiv (zIndex m q) _) = 0
      simp only [map_add, pderiv_mul, pderiv_z_rename_b]
      simp [pderiv_mul, pderiv_X, Pi.single_apply, pureAPoint, xIndex, zIndex]

theorem pureAHessian_bb (D : Data (K := K) m q) (v : Fin m → K) (i j : Fin q) :
    pureAHessian D v (bIndex i) (bIndex j) =
      (∑ a, v a • quadraticMatrix (D.Q a)) i j := by
  classical
  change eval (pureAPoint v) (pderiv (bIndex j) (pderiv (bIndex i) (polynomial D))) = _
  rw [b_partial]
  have hp : eval (0 : ResidualCoordinate q → K)
      (pderiv (Sum.inl j) (pderiv (Sum.inl i) D.R)) = 0 :=
    eval_zero_positive_homogeneous _ D.R_homogeneous.pderiv.pderiv (by decide)
  simp only [map_add, map_sum, pderiv_mul, pderiv_b_rename_b, pderiv_b_rename_residual,
    quadratic_second_partial D.Q0 D.Q0_homogeneous,
    quadratic_second_partial _ (D.Q_homogeneous _)]
  simp only [map_add, map_sum, map_mul, eval_pureA_rename_residual, hp]
  simp [pderiv_X, Pi.single_apply, pureAPoint, aIndex, bIndex, xIndex, zIndex,
    Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]

theorem pureAHessian_rank_le_middle_add_two (D : Data (K := K) m q) (v : Fin m → K)
    (hv : (quadraticMatrix D.QA).mulVec v = 0) :
    (pureAHessian D v).rank ≤ (∑ a, v a • quadraticMatrix (D.Q a)).rank + 2 := by
  classical
  let H := pureAHessian D v
  let M := H.submatrix (residualIndex (m := m)) residualIndex
  let E : Matrix (Coordinate m q) (ResidualCoordinate q) K :=
    Matrix.fromRows 0 (Matrix.fromBlocks 1 0 0
      (fun i _ => if i = (0 : Fin 2) then 0 else 1))
  have ha (i : Fin m) (j : Coordinate m q) : H (Sum.inl i) j = 0 :=
    pureAHessian_a D v hv i j
  have hx (j : Coordinate m q) : H (Sum.inr (Sum.inr 0)) j = 0 := pureAHessian_x D v j
  have hs : H.IsSymm := pureAHessian_symmetric D v
  have hac (i : Coordinate m q) (j : Fin m) : H i (Sum.inl j) = 0 := by
    rw [hs.apply]
    exact ha j i
  have hxc (i : Coordinate m q) : H i (Sum.inr (Sum.inr 0)) = 0 := by
    rw [hs.apply]
    exact hx i
  have hrecover : H = E * M * E.transpose := by
    ext i j
    rcases i with i | (i | i) <;> rcases j with j | (j | j)
    all_goals try fin_cases i
    all_goals try fin_cases j
    all_goals simp [E, M, Matrix.mul_apply, Fintype.sum_sum_type, residualIndex,
      bIndex, zIndex, Matrix.one_apply, ha, hx, hac, hxc]
  have hRank : H.rank ≤ M.rank := by
    rw [hrecover]
    exact (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)
  have hBB : M.toBlocks₁₁ = ∑ a, v a • quadraticMatrix (D.Q a) := by
    ext i j
    exact pureAHessian_bb D v i j
  have hb := MatrixRankBounds.rank_fromBlocks_le M.toBlocks₁₁ M.toBlocks₁₂ M.toBlocks₂₁ M.toBlocks₂₂
  rw [Matrix.fromBlocks_toBlocks, hBB] at hb
  exact hRank.trans (by simpa using hb)

end PureRadicalPoint

theorem pureA_radical_singular_rank_le_four {m q : ℕ}
    (D : Data (K := GeometricField) m q) (FI : FormalImplicitFunctionInput GeometricField)
    (hirred : Irreducible (polynomial D)) (hB0 : (quadraticMatrix D.Q0).det ≠ 0)
    (hRank : ∀ x : Coordinate m q → GeometricField, eval x (polynomial D) = 0 →
      ((polynomialHessian D).map (eval x)).rank ≤ q + 2)
    (hP : 1 ≤ (quadraticMatrix D.QA).rank) (hq : q ≤ 7)
    (v : Fin m → GeometricField) (hv : (quadraticMatrix D.QA).mulVec v = 0) :
    (∀ i, eval (pureAPoint v) (pderiv i (polynomial D)) = 0) ∧
      (pureAHessian D v).rank ≤ 4 := by
  refine ⟨pureA_gradient_zero D v hv, ?_⟩
  have hmid := schur_radical_middle_rank_le_two
    ((2 : GeometricField)⁻¹ • quadraticMatrix D.QA)
    (Matrix.IsSymm.smul (quadraticMatrix_symmetric D.QA) _)
    (by rwa [half_quadraticMatrix_rank]) (quadraticMatrix D.Q0) hB0
    (quadraticMatrix_symmetric D.Q0) (fun i => quadraticMatrix (D.Q i))
    (fun i => quadraticMatrix_symmetric (D.Q i))
    (clifford_relations_of_geometric_rank D FI hirred hB0 hRank) v
    (by rw [Matrix.smul_mulVec, hv, smul_zero]) hq
  change (∑ a, v a • quadraticMatrix (D.Q a)).rank ≤ 2 at hmid
  have hfull := pureAHessian_rank_le_middle_add_two D v hv
  omega

end HessianTheorem11.LocalCubicNormalForm
