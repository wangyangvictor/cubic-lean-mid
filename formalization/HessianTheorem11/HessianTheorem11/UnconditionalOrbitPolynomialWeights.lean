import HessianTheorem11.UnconditionalOrbitWeightComponents

/-! Actual polynomial weight projections are preserved by every linear
subspace invariant under the corresponding diagonal substitutions. -/
noncomputable section
namespace HessianTheorem11.UnconditionalOrbitWeights
open MvPolynomial PolynomialRestriction ReducedWeightCurve
variable {K σ : Type*} [Field K] [Fintype σ] [DecidableEq σ]

def exponentWeight (w : σ → ℤ) (e : σ →₀ ℕ) : ℤ :=
  e.sum (fun i a => (a : ℤ) * w i)

def diagonalScale (P : MvPolynomial σ K) (w : σ → ℤ) (t : K) : MvPolynomial σ K :=
  P.sum (fun e c => monomial e (c * t ^ exponentWeight w e))

def weightPart (P : MvPolynomial σ K) (w : σ → ℤ) (a : ℤ) : MvPolynomial σ K :=
  Finsupp.filter (fun e => exponentWeight w e = a) P

@[simp] theorem coeff_weightPart (P : MvPolynomial σ K) (w : σ → ℤ)
    (a : ℤ) (e : σ →₀ ℕ) :
    coeff e (weightPart P w a) = if exponentWeight w e = a then coeff e P else 0 := rfl

@[simp] theorem coeff_diagonalScale (P : MvPolynomial σ K) (w : σ → ℤ)
    (t : K) (e : σ →₀ ℕ) :
    coeff e (diagonalScale P w t) = coeff e P * t ^ exponentWeight w e := by
  classical
  simp [diagonalScale,Finsupp.sum,coeff_sum,coeff_monomial,Finset.sum_ite_eq',
    Finsupp.mem_support_iff]
  split_ifs with h
  · change 0 = coeff e P * _
    rw [show coeff e P = 0 from h,zero_mul]
  · rfl

theorem restrict_diagonal_monomial_generic (w : σ → ℤ) (t : K) (ht : t ≠ 0)
    (e : σ →₀ ℕ) (c : K) :
    restrict (Matrix.diagonal (fun i => t ^ w i)) (monomial e c) =
      monomial e (c * t ^ exponentWeight w e) := by
  classical
  have hlin (i : σ) : linearForms (Matrix.diagonal (fun i => t ^ w i)) i =
      C (t ^ w i) * X i := by
    simp [linearForms,Matrix.diagonal_apply,apply_ite,ite_mul]
  change aeval _ (monomial e c) = _
  rw [aeval_monomial]
  simp only [hlin,mul_pow,Finset.prod_mul_distrib,← map_pow,← map_prod,Finsupp.prod]
  have hp : (∏ i ∈ e.support, (t ^ w i) ^ e i) = t ^ exponentWeight w e := by
    simp_rw [← zpow_natCast,← zpow_mul]
    rw [prod_zpow_nonzero t ht]
    congr 1
    unfold exponentWeight Finsupp.sum
    apply Finset.sum_congr rfl
    intro i _
    exact mul_comm _ _
  rw [hp,← C_mul_monomial,monomial_eq]
  simp [Finsupp.prod,mul_assoc]

theorem diagonalScale_eq_restrict (P : MvPolynomial σ K) (w : σ → ℤ)
    (t : K) (ht : t ≠ 0) :
    diagonalScale P w t = restrict (Matrix.diagonal (fun i => t ^ w i)) P := by
  classical
  calc
    _ = ∑ e ∈ P.support, restrict (Matrix.diagonal (fun i => t ^ w i))
        (monomial e (coeff e P)) := by
      unfold diagonalScale Finsupp.sum
      apply Finset.sum_congr rfl
      intro e he
      exact (restrict_diagonal_monomial_generic w t ht e (coeff e P)).symm
    _ = _ := by
      simpa only [restrict,map_sum] using (congrArg (restrict (Matrix.diagonal
        (fun i => t ^ w i))) P.as_sum).symm

theorem sum_weightParts (P : MvPolynomial σ K) (w : σ → ℤ) (t : K) :
    (∑ a ∈ P.support.image (exponentWeight w), t ^ a • weightPart P w a) =
      diagonalScale P w t := by
  classical
  ext e
  simp only [coeff_sum,coeff_smul,coeff_weightPart,coeff_diagonalScale,smul_eq_mul]
  by_cases hc : coeff e P = 0
  · simp [hc]
  · have he : exponentWeight w e ∈ P.support.image (exponentWeight w) :=
      Finset.mem_image.mpr ⟨e,mem_support_iff.mpr hc,rfl⟩
    rw [Finset.sum_eq_single (exponentWeight w e)]
    · simp [mul_comm]
    · intro a ha hne
      simp [Ne.symm hne]
    · exact fun h => (h he).elim

theorem weightPart_zero_outside (P : MvPolynomial σ K) (w : σ → ℤ) (a : ℤ)
    (ha : a ∉ P.support.image (exponentWeight w)) : weightPart P w a = 0 := by
  ext e
  rw [coeff_weightPart,coeff_zero]
  split_ifs with he
  · by_contra hc
    exact ha (Finset.mem_image.mpr ⟨e,mem_support_iff.mpr hc,he⟩)
  · rfl

theorem sum_weightParts_one (P : MvPolynomial σ K) (w : σ → ℤ) :
    (∑ a ∈ P.support.image (exponentWeight w), weightPart P w a) = P := by
  have h := sum_weightParts P w (1 : K)
  have he : diagonalScale P w (1 : K) = P := by ext e; simp
  simpa only [one_zpow,one_smul,he] using h

/-- The literal monomial projection belongs to the invariant subspace,
including negative and repeated weights. -/
theorem weightPart_mem [Infinite K] (W : Submodule K (MvPolynomial σ K))
    (P : MvPolynomial σ K) (w : σ → ℤ)
    (hW : ∀ t : K, t ≠ 0 → restrict (Matrix.diagonal (fun i => t ^ w i)) P ∈ W)
    (a : ℤ) : weightPart P w a ∈ W := by
  classical
  by_cases ha : a ∈ P.support.image (exponentWeight w)
  · apply laurent_coefficients_mem W (P.support.image (exponentWeight w))
      (weightPart P w) _ a ha
    intro t ht
    rw [sum_weightParts,diagonalScale_eq_restrict P w t ht]
    exact hW t ht
  · rw [weightPart_zero_outside P w a ha]
    exact W.zero_mem

end HessianTheorem11.UnconditionalOrbitWeights
