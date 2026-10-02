import HessianTheorem11.RadialDefectLimit

/-! The exceptional radial weight has a single zero-weight coordinate.
Its actual cubic limit splits as a polynomial in the other coordinates plus
one pure cube. This is an algebraic support calculation, with no geometry
supplied as an input. -/

noncomputable section
namespace HessianTheorem11
open MvPolynomial Matrix Module NonzeroLimitTransport

variable {K : Type*} [Field K] [CharZero K] {n : ℕ}

/-- Set just one coordinate equal to zero. -/
def eraseCoordinate (c : Fin n) : MvPolynomial (Fin n) K →ₐ[K] MvPolynomial (Fin n) K :=
  aeval (fun i => if i = c then 0 else X i)

/-- Retain just one coordinate. -/
def retainCoordinate (c : Fin n) : MvPolynomial (Fin n) K →ₐ[K] MvPolynomial (Fin n) K :=
  aeval (fun i => if i = c then X i else 0)

theorem mixed_thirdPartial_zero_of_single_zero_weight
    (G : MvPolynomial (Fin n) K) (w : Fin n → ℤ) (c : Fin n)
    (hW : ∀ d ∈ G.support, monomialWeight w d = 0)
    (hw : ∀ i, w i = -2 ∨ w i = 0 ∨ w i = 1 ∨ w i = 4)
    (hzero : ∀ i, w i = 0 ↔ i = c)
    (i j k : Fin n) (hc : i = c ∨ j = c ∨ k = c)
    (hmixed : ¬ (i = c ∧ j = c ∧ k = c)) :
    thirdPartialCoefficient G i j k = 0 := by
  by_contra hne
  have hs := thirdPartialCoefficient_weight G w 0 hW i j k hne
  have hci := hzero i
  have hcj := hzero j
  have hck := hzero k
  rcases hw i with hi | hi | hi | hi <;>
    rcases hw j with hj | hj | hj | hj <;>
    rcases hw k with hk | hk | hk | hk <;> omega

/-- Vanishing of the actual mixed third derivatives gives an actual
polynomial decomposition into the two coordinate blocks. -/
theorem split_erase_retain_of_mixed_thirdPartials
    (G : MvPolynomial (Fin n) K) (hG : G.IsHomogeneous 3) (c : Fin n)
    (hmixed : ∀ i j k, (i = c ∨ j = c ∨ k = c) →
      ¬ (i = c ∧ j = c ∧ k = c) → thirdPartialCoefficient G i j k = 0) :
    G = eraseCoordinate c G + retainCoordinate c G := by
  classical
  rw [cubic_third_partial_expansion G hG]
  simp only [map_smul, map_sum, ← smul_add, ← Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  by_cases hall : i = c ∧ j = c ∧ k = c
  · rcases hall with ⟨rfl, rfl, rfl⟩
    simp [cubicExpansionTerm, eraseCoordinate, retainCoordinate]
  by_cases hnone : i ≠ c ∧ j ≠ c ∧ k ≠ c
  · rcases hnone with ⟨hi, hj, hk⟩
    simp [cubicExpansionTerm, eraseCoordinate, retainCoordinate, hi, hj, hk]
  have hz := hmixed i j k (by tauto) hall
  simp [cubicExpansionTerm, hz]

theorem retainCoordinate_cubic
    (G : MvPolynomial (Fin n) K) (hG : G.IsHomogeneous 3) (c : Fin n) :
    retainCoordinate c G = C ((6 : K)⁻¹ * thirdPartialCoefficient G c c c) * X c ^ 3 := by
  classical
  conv_lhs => rw [cubic_third_partial_expansion G hG]
  simp only [map_smul, map_sum]
  have hterm (i j k : Fin n) :
      retainCoordinate c (cubicExpansionTerm G i j k) =
        if i = c then (if j = c then (if k = c then cubicExpansionTerm G c c c else 0) else 0) else 0 := by
    by_cases hi : i = c <;> by_cases hj : j = c <;> by_cases hk : k = c <;>
      simp [cubicExpansionTerm, retainCoordinate, hi, hj, hk]
  simp_rw [hterm]
  simp [cubicExpansionTerm, smul_eq_C_mul, map_mul, pow_succ, mul_assoc]

theorem pure_cube_split_of_single_zero_weight
    (G : MvPolynomial (Fin n) K) (hG : G.IsHomogeneous 3)
    (w : Fin n → ℤ) (c : Fin n)
    (hW : ∀ d ∈ G.support, monomialWeight w d = 0)
    (hw : ∀ i, w i = -2 ∨ w i = 0 ∨ w i = 1 ∨ w i = 4)
    (hzero : ∀ i, w i = 0 ↔ i = c) :
    G = eraseCoordinate c G + C ((6 : K)⁻¹ * thirdPartialCoefficient G c c c) * X c ^ 3 := by
  rw [← retainCoordinate_cubic G hG c]
  exact split_erase_retain_of_mixed_thirdPartials G hG c
    (mixed_thirdPartial_zero_of_single_zero_weight G w c hW hw hzero)

/-- The unique transverse kernel coordinate is the unique zero-weight
coordinate, so the actual radial limit contains it only as a pure cube. -/
theorem SmoothRadialSupportData.pure_cube_split_of_defect_one
    {F : MvPolynomial (Fin n) K} {x : Fin n → K} {T : Submodule K (Fin n → K)}
    (E : SmoothRadialSupportData F x T) (G : MvPolynomial (Fin n) K)
    (hG : G.IsHomogeneous 3)
    (hW : ∀ d ∈ G.support, monomialWeight
      (smoothRadialWeight E.adapted.radial E.adapted.tangentIndices E.adapted.kernelIndices) d = 0)
    (hc : E.defect = 1) :
    ∃ c : Fin n, c ∈ E.adapted.kernelIndices ∧ c ∉ E.adapted.tangentIndices ∧
      G = eraseCoordinate c G + C ((6 : K)⁻¹ * thirdPartialCoefficient G c c c) * X c ^ 3 := by
  classical
  obtain ⟨c, hcset⟩ := Finset.card_eq_one.mp hc
  have hmem (i : Fin n) :
      i ∈ E.adapted.kernelIndices ∧ i ∉ E.adapted.tangentIndices ↔ i = c := by
    rw [← Finset.mem_sdiff, hcset]
    exact Finset.mem_singleton
  refine ⟨c, ((hmem c).mpr rfl).1, ((hmem c).mpr rfl).2, ?_⟩
  apply pure_cube_split_of_single_zero_weight G hG _ c hW
  · intro i
    rw [E.weight_values i]
    split_ifs <;> norm_num
  · intro i
    rw [E.weight_values i, ← hmem i]
    have hrT := E.adapted.radial_mem_tangent
    have hrL := E.adapted.radial_notMem_kernel
    by_cases hiT : i ∈ E.adapted.tangentIndices <;>
      by_cases hiL : i ∈ E.adapted.kernelIndices <;>
      by_cases hir : i = E.adapted.radial <;> simp_all

@[simp] theorem pderiv_eraseCoordinate (G : MvPolynomial (Fin n) K) (c : Fin n) :
    pderiv c (eraseCoordinate c G) = 0 := by
  classical
  induction G using MvPolynomial.induction_on with
  | C a => simp [eraseCoordinate]
  | add p q hp hq => simp only [map_add, hp, hq, add_zero]
  | mul_X p i hp =>
    rw [map_mul]
    by_cases hi : i = c
    · simp [eraseCoordinate, hi]
    · rw [show eraseCoordinate c (X i : MvPolynomial (Fin n) K) = X i by
        simp [eraseCoordinate, hi], Derivation.leibniz, hp]
      simp [Pi.single_apply, hi, Ne.symm hi]

/-- The pure-cube coefficient is nonzero whenever the full Hessian
polynomial has nonzero determinant. -/
theorem pure_cube_coefficient_ne_zero
    (G : MvPolynomial (Fin n) K) (c : Fin n) (κ : K)
    (hsplit : G = eraseCoordinate c G + C κ * X c ^ 3)
    (hdet : Matrix.det (fun i j : Fin n => pderiv j (pderiv i G)) ≠ 0) : κ ≠ 0 := by
  intro hk
  have he : G = eraseCoordinate c G := by simpa [hk] using hsplit
  apply hdet
  apply Matrix.det_eq_zero_of_row_eq_zero c
  intro j
  rw [show pderiv c G = 0 by rw [he]; exact pderiv_eraseCoordinate G c]
  exact map_zero _

end HessianTheorem11
