import HessianTheorem11.HessianMultiplicity
import Mathlib.Algebra.MvPolynomial.Equiv

/-! A polynomial involving both disjoint coordinate blocks cannot divide a
nonzero polynomial supported on just one of them. This is the algebraic
obstruction behind the split-form exclusion; no geometric input is used. -/
noncomputable section
namespace HessianTheorem11.SplitPolynomial
open MvPolynomial

variable {K σ τ : Type*} [Field K]

theorem sumEquiv_rename_left (G : MvPolynomial σ K) :
    sumAlgEquiv K σ τ (rename Sum.inl G) = map C G := by
  have h := congrArg (fun f : MvPolynomial σ K →ₐ[K]
    MvPolynomial σ (MvPolynomial τ K) => f G)
    (sumAlgEquiv_comp_rename_inl (R := K) (S₁ := σ) (S₂ := τ))
  exact h

theorem sumEquiv_rename_right (G : MvPolynomial τ K) :
    sumAlgEquiv K σ τ (rename Sum.inr G) = C G := by
  have h := congrArg (fun f : MvPolynomial τ K →ₐ[K]
    MvPolynomial σ (MvPolynomial τ K) => f G)
    (sumAlgEquiv_comp_rename_inr (R := K) (S₁ := σ) (S₂ := τ))
  exact h

/-- A nonconstant left summand prevents divisibility into any nonzero
polynomial in the right variables alone. -/
theorem split_not_dvd_right (G : MvPolynomial σ K) (H D : MvPolynomial τ K)
    (hG : ∃ d : σ →₀ ℕ, d ≠ 0 ∧ coeff d G ≠ 0) (hD : D ≠ 0) :
    ¬ (rename Sum.inl G + rename Sum.inr H) ∣ rename Sum.inr D := by
  classical
  intro hdiv
  have hd := map_dvd (sumAlgEquiv K σ τ).toRingHom hdiv
  change sumAlgEquiv K σ τ (rename Sum.inl G + rename Sum.inr H) ∣
    sumAlgEquiv K σ τ (rename Sum.inr D) at hd
  rw [map_add, sumEquiv_rename_left, sumEquiv_rename_right, sumEquiv_rename_right] at hd
  have hz : (map C G + C H : MvPolynomial σ (MvPolynomial τ K)).totalDegree = 0 := by
    have hb := MvPolynomial.totalDegree_le_of_dvd_of_isDomain hd (C_ne_zero.mpr hD)
    simpa only [totalDegree_C, Nat.le_zero] using hb
  have he := totalDegree_eq_zero_iff_eq_C.mp hz
  obtain ⟨d, hd0, hcoeff⟩ := hG
  have hc := congrArg (coeff d) he
  simp [coeff_map, coeff_C, hd0, Ne.symm hd0] at hc
  exact hcoeff hc

theorem rename_swap_left (G : MvPolynomial σ K) :
    rename Sum.swap (rename (Sum.inl : σ → σ ⊕ τ) G) = rename Sum.inr G := by
  rw [rename_rename]
  rfl

theorem rename_swap_right (G : MvPolynomial τ K) :
    rename Sum.swap (rename (Sum.inr : τ → σ ⊕ τ) G) = rename Sum.inl G := by
  rw [rename_rename]
  rfl

theorem split_not_dvd_left (G D : MvPolynomial σ K) (H : MvPolynomial τ K)
    (hH : ∃ d : τ →₀ ℕ, d ≠ 0 ∧ coeff d H ≠ 0) (hD : D ≠ 0) :
    ¬ (rename Sum.inl G + rename Sum.inr H) ∣ rename Sum.inl D := by
  intro hdiv
  have hd := map_dvd (rename Sum.swap).toRingHom hdiv
  change rename Sum.swap (rename Sum.inl G + rename Sum.inr H) ∣
    rename Sum.swap (rename (Sum.inl : σ → σ ⊕ τ) D) at hd
  rw [map_add, rename_swap_left, rename_swap_right, rename_swap_left, add_comm] at hd
  exact split_not_dvd_right H G D hH hD hd

def fullHessian (F : MvPolynomial σ K) : Matrix σ σ (MvPolynomial σ K) :=
  fun i j => pderiv j (pderiv i F)

theorem pderiv_right_rename_left (i : τ) (G : MvPolynomial σ K) :
    pderiv (Sum.inr i) (rename (Sum.inl : σ → σ ⊕ τ) G) = 0 := by
  classical
  induction G using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p j hp => simp [Derivation.leibniz, hp, Pi.single_apply]

theorem pderiv_left_rename_right (i : σ) (H : MvPolynomial τ K) :
    pderiv (Sum.inl i) (rename (Sum.inr : τ → σ ⊕ τ) H) = 0 := by
  classical
  induction H using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p j hp => simp [Derivation.leibniz, hp, Pi.single_apply]

theorem fullHessian_split (G : MvPolynomial σ K) (H : MvPolynomial τ K) :
    fullHessian (rename Sum.inl G + rename Sum.inr H) = Matrix.fromBlocks
      ((fullHessian G).map (rename Sum.inl)) 0 0
      ((fullHessian H).map (rename Sum.inr)) := by
  ext i j
  cases i <;> cases j <;>
    simp [fullHessian, pderiv_rename Sum.inl_injective,
      pderiv_rename Sum.inr_injective, pderiv_right_rename_left, pderiv_left_rename_right]

theorem determinant_split [Fintype σ] [Fintype τ] [DecidableEq σ] [DecidableEq τ]
    (G : MvPolynomial σ K) (H : MvPolynomial τ K) :
    (fullHessian (rename Sum.inl G + rename Sum.inr H)).det =
      rename Sum.inl (fullHessian G).det * rename Sum.inr (fullHessian H).det := by
  rw [fullHessian_split, Matrix.det_fromBlocks_zero₂₁]
  congr 1
  · exact ((rename (R := K) (Sum.inl : σ → σ ⊕ τ)).toRingHom.map_det (fullHessian G)).symm
  · exact ((rename (R := K) (Sum.inr : τ → σ ⊕ τ)).toRingHom.map_det (fullHessian H)).symm

/-- Source Lemma 11.2's divisibility contradiction, proved directly in the
polynomial ring. Neither summand need be a determinant or be classified. -/
theorem split_not_dvd_hessian_determinant
    [Fintype σ] [Fintype τ] [DecidableEq σ] [DecidableEq τ]
    (G : MvPolynomial σ K) (H : MvPolynomial τ K)
    (hG : ∃ d : σ →₀ ℕ, d ≠ 0 ∧ coeff d G ≠ 0)
    (hH : ∃ d : τ →₀ ℕ, d ≠ 0 ∧ coeff d H ≠ 0)
    (hirred : Irreducible (rename Sum.inl G + rename Sum.inr H))
    (hdet : (fullHessian (rename Sum.inl G + rename Sum.inr H)).det ≠ 0) :
    ¬ (rename Sum.inl G + rename Sum.inr H) ∣
      (fullHessian (rename Sum.inl G + rename Sum.inr H)).det := by
  rw [determinant_split] at hdet ⊢
  have hg : (fullHessian G).det ≠ 0 := by
    intro hz
    exact hdet (by simp [hz])
  have hh : (fullHessian H).det ≠ 0 := by
    intro hz
    exact hdet (by simp [hz])
  intro hd
  rcases hirred.prime.dvd_or_dvd hd with hd | hd
  · exact split_not_dvd_left G (fullHessian G).det H hH hg hd
  · exact split_not_dvd_right G H (fullHessian H).det hG hh hd

/-- A nonzero full Hessian determinant in a nonempty coordinate space
forces an actual nonconstant coefficient; no homogeneity is required. -/
theorem exists_nonconstant_coefficient_of_det_ne_zero
    [Fintype σ] [DecidableEq σ] [Nonempty σ]
    (F : MvPolynomial σ K) (hdet : (fullHessian F).det ≠ 0) :
    ∃ d : σ →₀ ℕ, d ≠ 0 ∧ coeff d F ≠ 0 := by
  classical
  by_contra h
  push_neg at h
  have he : F = C (coeff 0 F) := by
    ext d
    by_cases hd : d = 0
    · subst d; simp
    · simp [coeff_C, Ne.symm hd, h d hd]
  apply hdet
  rw [he]
  have hz : fullHessian (C (coeff 0 F) : MvPolynomial σ K) = 0 := by
    ext i j
    simp [fullHessian]
  rw [hz, Matrix.det_zero]
  infer_instance

end HessianTheorem11.SplitPolynomial
