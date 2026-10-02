import HessianTheorem11.Geometry

/-! Rational diagonal weight test in source §4. This does not assert geometric
weight descent: the passage from geometric to rational weighted flags is a
separate proof obligation. -/

namespace HessianTheorem11
open MvPolynomial

def monomialWeight {n : ℕ} (w : Fin n → ℤ) (d : Fin n →₀ ℕ) : ℤ :=
  ∑ j, (d j : ℤ) * w j

def HasNonnegativeMonomialWeights {n : ℕ} (F : RationalPolynomial n)
    (w : Fin n → ℤ) : Prop :=
  ∀ d ∈ F.support, 0 ≤ monomialWeight w d

/-- A homogeneous cubic with nonnegative monomial weights vanishes at the
coordinate vector of any strictly negative variable weight. -/
theorem eval_coordinate_zero_of_negative_weight {n : ℕ}
    (F : RationalPolynomial n) (hF : F.IsHomogeneous 3)
    (w : Fin n → ℤ) (hw : HasNonnegativeMonomialWeights F w)
    (i : Fin n) (hi : w i < 0) : eval (Pi.single i 1) F = 0 := by
  classical
  apply MvPolynomial.eval₂Hom_eq_zero
  intro d hd
  have hex : ∃ j ∈ d.support, j ≠ i := by
    by_contra! h
    have hsub : d.support ⊆ {i} := by
      intro j hj
      exact Finset.mem_singleton.mpr (h j hj)
    have hdform : d = Finsupp.single i (d i) :=
      Finsupp.support_subset_singleton.mp hsub
    have hdegree : d.degree = 3 := by
      rw [Finsupp.degree_eq_weight_one]
      exact hF hd
    have hdegree' : (Finsupp.single i (d i)).degree = 3 := by
      rw [← hdform]
      exact hdegree
    have hdi : d i = 3 := by simpa only [Finsupp.degree_single] using hdegree'
    have hweight := hw d (Finsupp.mem_support_iff.mpr hd)
    have heq : monomialWeight w d = 3 * w i := by
      unfold monomialWeight
      conv_lhs => rw [hdform]
      simp [Finsupp.single_apply, hdi]
    rw [heq] at hweight
    omega
  obtain ⟨j, hj, hji⟩ := hex
  refine ⟨j, hj, ?_⟩
  simp [hji]

/-- Anisotropy already forces every admissible rational diagonal variable
weight to be nonnegative, without any hypothesis about their sum. -/
theorem rational_admissible_weight_nonnegative {n : ℕ} (F : AnisotropicCubic n)
    (w : Fin n → ℤ) (hw : HasNonnegativeMonomialWeights F.polynomial w)
    (i : Fin n) : 0 ≤ w i := by
  by_contra hn
  have he := eval_coordinate_zero_of_negative_weight F.polynomial F.homogeneous
    w hw i (by omega)
  have hz := F.anisotropic (Pi.single i 1) he
  have hi := congrFun hz i
  simp at hi

theorem rational_admissible_weight_sum_nonnegative {n : ℕ} (F : AnisotropicCubic n)
    (w : Fin n → ℤ) (hw : HasNonnegativeMonomialWeights F.polynomial w) :
    0 ≤ ∑ i, w i :=
  Finset.sum_nonneg (fun i _ => rational_admissible_weight_nonnegative F w hw i)

/-- Thus a rational determinant-one diagonal subgroup with an existing limit
must be trivial. This is the rational anisotropy step, not geometric descent. -/
theorem rational_zero_sum_admissible_weights_trivial {n : ℕ} (F : AnisotropicCubic n)
    (w : Fin n → ℤ) (hw : HasNonnegativeMonomialWeights F.polynomial w)
    (hsum : ∑ i, w i = 0) : w = 0 := by
  funext i
  have h := (Finset.sum_eq_zero_iff_of_nonneg
    (fun j _ => rational_admissible_weight_nonnegative F w hw j)).mp hsum i
      (Finset.mem_univ i)
  exact h

end HessianTheorem11
