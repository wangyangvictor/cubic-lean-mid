import HessianTheorem11.LocalCubicRadical

noncomputable section
namespace HessianTheorem11.LocalCubicNormalForm
open MvPolynomial Matrix Module SchurSecondOrder

variable {K : Type*} [Field K] [CharZero K] {m q : ℕ}

@[simp] theorem pureAPoint_right (u : Fin m → K) (j : Fin q ⊕ Fin 2) :
    pureAPoint u (Sum.inr j) = 0 := rfl

def localHessian (D : Data (K := K) m q) (x : Coordinate m q → K) :
    Matrix (Coordinate m q) (Coordinate m q) K :=
  (polynomialHessian D).map (eval x)

theorem localHessian_base (D : Data (K := K) m q) :
    localHessian D (basePoint m q) =
      Matrix.fromBlocks (0 : Matrix (Fin m) (Fin m) K) 0 0
        (normalInverse (quadraticMatrix D.Q0) 2) := by
  have he : matrixCoeff 0 (hessianSeries D 0 0) = localHessian D (basePoint m q) := by
    ext i j
    exact coeff_zero_seriesEval 0 0 (by simp) _
  rw [← he, ← hessianSeries_fromBlocks]
  ext i j
  rcases i with i | i <;> rcases j with j | j
  · change matrixCoeff 0 (aBlock D 0 0) i j = 0
    rw [aBlock_coefficient]
    simp
  · change matrixCoeff 0 (crossBlock D 0 0) i j = 0
    rw [crossBlock_coeff_zero D 0 0 (by simp)]
    rfl
  · change matrixCoeff 0 (crossBlock D 0 0).transpose i j = 0
    rw [matrixCoeff_transpose, crossBlock_coeff_zero D 0 0 (by simp)]
    rfl
  · change matrixCoeff 0 (normalBlock D 0 0) i j = _
    rw [normalBlock_coeff_zero D 0 0 (by simp)]
    rfl

theorem base_hessian_kernel_iff (D : Data (K := K) m q)
    (hB0 : (quadraticMatrix D.Q0).det ≠ 0) (w : Coordinate m q → K) :
    (localHessian D (basePoint m q)).mulVec w = 0 ↔ w = pureAPoint (w ∘ Sum.inl) := by
  let N := normalInverse (quadraticMatrix D.Q0) 2
  let J := normalInverse (quadraticMatrix D.Q0)⁻¹ (2 : K)⁻¹
  have hJN : J * N = 1 := normalInverse_mul _ _ _ _
    (Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hB0))
    (inv_mul_cancel₀ (by norm_num))
  rw [localHessian_base, Matrix.fromBlocks_mulVec]
  simp only [Matrix.zero_mulVec, zero_add, add_zero]
  constructor
  · intro hw
    have hN : N.mulVec (w ∘ Sum.inr) = 0 := by
      funext i
      exact congrFun hw (Sum.inr i)
    have hz : w ∘ Sum.inr = 0 := by
      have h := congrArg (J.mulVec) hN
      rwa [Matrix.mulVec_mulVec, hJN, Matrix.one_mulVec, Matrix.mulVec_zero] at h
    funext i
    cases i with
    | inl i => rfl
    | inr i => exact congrFun hz i
  · intro hw
    have hz : w ∘ Sum.inr = 0 := by
      rw [hw]
      rfl
    rw [hz, Matrix.mulVec_zero]
    ext i
    cases i <;> rfl

theorem pureAHessian_a_exact (D : Data (K := K) m q) (u : Fin m → K)
    (i : Fin m) (j : Coordinate m q) :
    pureAHessian D u (aIndex i) j =
      if j = zIndex m q then ((quadraticMatrix D.QA).mulVec u) i else 0 := by
  classical
  change eval (pureAPoint u) (pderiv j (pderiv (aIndex i) (polynomial D))) = _
  rcases j with j | (j | j)
  · change eval (pureAPoint u) (pderiv (aIndex j) _) = _
    rw [aa_partial]
    simp [zIndex]
  · change eval (pureAPoint u) (pderiv (bIndex j) _) = _
    rw [ab_partial]
    have hp : eval (0 : Fin q → K) (pderiv j (D.Q i)) = 0 :=
      eval_zero_positive_homogeneous _ (D.Q_homogeneous i).pderiv (by decide)
    simp only [eval_zero] at hp
    simp [hp, zIndex]
  · fin_cases j
    · change eval (pureAPoint u) (pderiv (xIndex m q) _) = _
      rw [ax_partial]
      simp [zIndex]
    · change eval (pureAPoint u) (pderiv (zIndex m q) _) = _
      rw [az_partial]
      have he : eval u (pderiv i D.QA) = ((quadraticMatrix D.QA).mulVec u) i := by
        rw [quadratic_first_partial D.QA D.QA_homogeneous]
        simp [Matrix.mulVec, dotProduct]
      simp [he, zIndex]

theorem pureAHessian_mul_pureA (D : Data (K := K) m q) (u v : Fin m → K) :
    (pureAHessian D u).mulVec (pureAPoint v) =
      fun j => if j = zIndex m q then dotProduct u ((quadraticMatrix D.QA).mulVec v) else 0 := by
  classical
  ext j
  change (∑ k, pureAHessian D u j k * pureAPoint v k) = _
  rw [Fintype.sum_sum_type]
  simp only [pureAPoint, Sum.elim_inl, Sum.elim_inr, mul_zero, Finset.sum_const_zero, add_zero]
  have he (i : Fin m) : pureAHessian D u j (Sum.inl i) =
      if j = zIndex m q then ((quadraticMatrix D.QA).mulVec u) i else 0 := by
    rw [(pureAHessian_symmetric D u).apply]
    exact pureAHessian_a_exact D u i j
  simp only [he]
  by_cases hj : j = zIndex m q
  · rw [if_pos hj]
    simp only [if_pos hj]
    have hs := (CliffordNormalization.toBilin'_isSymm _ (quadraticMatrix_symmetric D.QA)).eq v u
    simpa only [Matrix.toBilin'_apply', dotProduct, mul_comm] using hs
  · simp [hj]

def localIntrinsicRadical (D : Data (K := K) m q) : Submodule K (Coordinate m q → K) :=
  LinearMap.ker (localHessian D (basePoint m q)).mulVecLin ⊓
    ⨅ u : LinearMap.ker (localHessian D (basePoint m q)).mulVecLin,
      LinearMap.ker (localHessian D u).mulVecLin

theorem mem_localIntrinsicRadical_iff (D : Data (K := K) m q) (w : Coordinate m q → K) :
    w ∈ localIntrinsicRadical D ↔ (localHessian D (basePoint m q)).mulVec w = 0 ∧
      ∀ u, (localHessian D (basePoint m q)).mulVec u = 0 →
        (localHessian D u).mulVec w = 0 := by
  simp only [localIntrinsicRadical, Submodule.mem_inf, Submodule.mem_iInf,
    LinearMap.mem_ker, Matrix.mulVecLin_apply]
  constructor
  · rintro ⟨hw, h⟩
    exact ⟨hw, fun u hu => h ⟨u, hu⟩⟩
  · rintro ⟨hw, h⟩
    exact ⟨hw, fun u => h u u.property⟩

theorem pureA_mem_localIntrinsicRadical_iff (D : Data (K := K) m q)
    (hB0 : (quadraticMatrix D.Q0).det ≠ 0) (v : Fin m → K) :
    pureAPoint v ∈ localIntrinsicRadical D ↔ (quadraticMatrix D.QA).mulVec v = 0 := by
  rw [mem_localIntrinsicRadical_iff]
  have hk (u : Fin m → K) : (localHessian D (basePoint m q)).mulVec (pureAPoint u) = 0 :=
    (base_hessian_kernel_iff D hB0 _).mpr rfl
  constructor
  · rintro ⟨_, h⟩
    ext i
    have hz := congrFun (h (pureAPoint (Pi.single i 1)) (hk _)) (zIndex m q)
    change (pureAHessian D (Pi.single i 1)).mulVec (pureAPoint v) (zIndex m q) = 0 at hz
    rw [pureAHessian_mul_pureA] at hz
    simpa [dotProduct, Pi.single_apply] using hz
  · intro hv
    refine ⟨hk v, ?_⟩
    intro w hw
    have he := (base_hessian_kernel_iff D hB0 w).mp hw
    rw [he]
    change (pureAHessian D (w ∘ Sum.inl)).mulVec (pureAPoint v) = 0
    rw [pureAHessian_mul_pureA, hv]
    ext i
    simp

def localRadicalEquiv (D : Data (K := K) m q)
    (hB0 : (quadraticMatrix D.Q0).det ≠ 0) :
    LinearMap.ker (quadraticMatrix D.QA).mulVecLin ≃ₗ[K] localIntrinsicRadical D where
  toFun v := ⟨pureAPoint v, (pureA_mem_localIntrinsicRadical_iff D hB0 v).mpr v.property⟩
  invFun w := ⟨(w : Coordinate m q → K) ∘ Sum.inl, by
    have he := (base_hessian_kernel_iff D hB0 w).mp
      ((mem_localIntrinsicRadical_iff D w).mp w.property).1
    apply (pureA_mem_localIntrinsicRadical_iff D hB0 _).mp
    rw [← he]
    exact w.property⟩
  left_inv v := by
    apply Subtype.ext
    rfl
  right_inv w := by
    apply Subtype.ext
    exact ((base_hessian_kernel_iff D hB0 w).mp
      ((mem_localIntrinsicRadical_iff D w).mp w.property).1).symm
  map_add' v w := by
    apply Subtype.ext
    ext i
    cases i <;> simp [pureAPoint]
  map_smul' c v := by
    apply Subtype.ext
    ext i
    cases i <;> simp [pureAPoint]

theorem finrank_localIntrinsicRadical (D : Data (K := K) m q)
    (hB0 : (quadraticMatrix D.Q0).det ≠ 0) :
    finrank K (localIntrinsicRadical D) = m - (quadraticMatrix D.QA).rank := by
  rw [← (localRadicalEquiv D hB0).finrank_eq]
  have hd := (quadraticMatrix D.QA).mulVecLin.finrank_range_add_finrank_ker
  change (quadraticMatrix D.QA).rank +
    finrank K (LinearMap.ker (quadraticMatrix D.QA).mulVecLin) = finrank K (Fin m → K) at hd
  simp only [Module.finrank_fin_fun] at hd
  omega

end HessianTheorem11.LocalCubicNormalForm
