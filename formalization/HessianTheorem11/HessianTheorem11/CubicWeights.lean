import HessianTheorem11.HessianLinearity
import HessianTheorem11.RationalWeights

/-!
From the actual third-partial coefficient tensor to monomial weights.
The cubic is reconstructed by iterated Euler identities, so the support
criterion does not assume an unspecified polarization formula. Centering
turns a negative total weight into strictly positive support weights with
zero total weight, the algebraic input to a special-linear zero limit.
-/

noncomputable section

namespace HessianTheorem11

open MvPolynomial
open scoped BigOperators

/-- The coefficient of the constant third derivative of a cubic. -/
def thirdPartialCoefficient {K : Type*} [CommRing K] {n : ℕ}
    (F : MvPolynomial (Fin n) K) (i j k : Fin n) : K :=
  coeff 0 (pderiv k (pderiv j (pderiv i F)))

/-- The scalar-weighted ordered cubic monomial in the polarization sum. -/
def cubicExpansionTerm {K : Type*} [CommRing K] {n : ℕ}
    (F : MvPolynomial (Fin n) K) (i j k : Fin n) : MvPolynomial (Fin n) K :=
  C (thirdPartialCoefficient F i j k) * X i * X j * X k

/-- Iterated Euler identity reconstructs six times the actual cubic. -/
theorem cubic_third_partial_expansion_six
    {K : Type*} [CommRing K] {n : ℕ}
    (F : MvPolynomial (Fin n) K) (hF : F.IsHomogeneous 3) :
    ∑ i, ∑ j, ∑ k, cubicExpansionTerm F i j k = 6 * F := by
  have hj (i j : Fin n) :
      ∑ k, X k * C (thirdPartialCoefficient F i j k) = pderiv j (pderiv i F) :=
    (homogeneous_one_expansion hF.pderiv.pderiv).symm
  have hi (i : Fin n) :
      ∑ j, X j * (∑ k, X k * C (thirdPartialCoefficient F i j k)) =
        2 * pderiv i F := by
    simp_rw [hj i]
    simpa only [nsmul_eq_mul] using hF.pderiv.sum_X_mul_pderiv
  calc
    _ = ∑ i, X i * (∑ j, X j *
        (∑ k, X k * C (thirdPartialCoefficient F i j k))) := by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      apply Finset.sum_congr rfl
      intro k hk
      unfold cubicExpansionTerm
      ring
    _ = ∑ i, X i * (2 * pderiv i F) := by simp_rw [hi]
    _ = 2 * (∑ i, X i * pderiv i F) := by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ = 6 * F := by
      rw [hF.sum_X_mul_pderiv]
      simp only [nsmul_eq_mul]
      ring

theorem cubic_third_partial_expansion
    {K : Type*} [Field K] [CharZero K] {n : ℕ}
    (F : MvPolynomial (Fin n) K) (hF : F.IsHomogeneous 3) :
    F = (6 : K)⁻¹ • (∑ i, ∑ j, ∑ k, cubicExpansionTerm F i j k) := by
  rw [cubic_third_partial_expansion_six F hF]
  rw [show (6 : MvPolynomial (Fin n) K) * F = (6 : K) • F by
    rw [MvPolynomial.smul_eq_C_mul]
    congr 1]
  rw [smul_smul, inv_mul_cancel₀ (by norm_num : (6 : K) ≠ 0), one_smul]

/-- Generic-coefficient counterpart of the rational weight predicate. -/
def HasNonnegativeWeights {K : Type*} [CommRing K] {n : ℕ}
    (F : MvPolynomial (Fin n) K) (w : Fin n → ℤ) : Prop :=
  ∀ d ∈ F.support, 0 ≤ monomialWeight w d

def HasPositiveWeights {K : Type*} [CommRing K] {n : ℕ}
    (F : MvPolynomial (Fin n) K) (w : Fin n → ℤ) : Prop :=
  ∀ d ∈ F.support, 0 < monomialWeight w d

theorem hasNonnegativeWeights_rational_iff {n : ℕ}
    (F : RationalPolynomial n) (w : Fin n → ℤ) :
    HasNonnegativeWeights F w ↔ HasNonnegativeMonomialWeights F w := Iff.rfl

theorem monomialWeight_add {n : ℕ} (w : Fin n → ℤ)
    (d e : Fin n →₀ ℕ) :
    monomialWeight w (d + e) = monomialWeight w d + monomialWeight w e := by
  simp [monomialWeight, Nat.cast_add, add_mul, Finset.sum_add_distrib]

theorem monomialWeight_single {n : ℕ} (w : Fin n → ℤ) (i : Fin n) (a : ℕ) :
    monomialWeight w (Finsupp.single i a) = a * w i := by
  classical
  simp [monomialWeight, Finsupp.single_apply]

theorem cubicExpansionTerm_eq_monomial
    {K : Type*} [CommRing K] {n : ℕ}
    (F : MvPolynomial (Fin n) K) (i j k : Fin n) :
    cubicExpansionTerm F i j k =
      monomial (Finsupp.single i 1 + Finsupp.single j 1 + Finsupp.single k 1)
        (thirdPartialCoefficient F i j k) := by
  simp only [cubicExpansionTerm, X, C_apply, monomial_mul, zero_add, mul_one]

theorem hasNonnegativeWeights_sum
    {K ι : Type*} [CommRing K] {n : ℕ}
    (s : Finset ι) (P : ι → MvPolynomial (Fin n) K) (w : Fin n → ℤ)
    (hP : ∀ i ∈ s, HasNonnegativeWeights (P i) w) :
    HasNonnegativeWeights (∑ i ∈ s, P i) w := by
  classical
  intro d hd
  obtain ⟨i, hi, hdi⟩ := Finset.mem_biUnion.mp (MvPolynomial.support_sum hd)
  exact hP i hi d hdi

theorem hasNonnegativeWeights_smul
    {K : Type*} [CommRing K] {n : ℕ}
    (a : K) (P : MvPolynomial (Fin n) K) (w : Fin n → ℤ)
    (hP : HasNonnegativeWeights P w) : HasNonnegativeWeights (a • P) w := by
  intro d hd
  exact hP d (MvPolynomial.support_smul hd)

/-- Every actual support monomial has nonnegative weight when every
nonzero coefficient of the ordered polarization tensor does. -/
theorem nonnegativeWeights_of_thirdPartials
    {K : Type*} [Field K] [CharZero K] {n : ℕ}
    (F : MvPolynomial (Fin n) K) (hF : F.IsHomogeneous 3)
    (w : Fin n → ℤ)
    (hT : ∀ i j k, thirdPartialCoefficient F i j k ≠ 0 →
      0 ≤ w i + w j + w k) : HasNonnegativeWeights F w := by
  classical
  rw [cubic_third_partial_expansion F hF]
  apply hasNonnegativeWeights_smul
  apply hasNonnegativeWeights_sum
  intro i hi
  apply hasNonnegativeWeights_sum
  intro j hj
  apply hasNonnegativeWeights_sum
  intro k hk
  rw [cubicExpansionTerm_eq_monomial]
  intro d hd
  have hcoeff : thirdPartialCoefficient F i j k ≠ 0 := by
    intro hz
    simp [hz] at hd
  have hd' := Finset.mem_singleton.mp (MvPolynomial.support_monomial_subset hd)
  subst d
  simpa [monomialWeight_add, monomialWeight_single] using hT i j k hcoeff

/-- Integer centering preserves integrality and makes total weight zero. -/
def centeredWeights {n : ℕ} (w : Fin n → ℤ) : Fin n → ℤ :=
  fun i => (n : ℤ) * w i - ∑ j, w j

theorem sum_centeredWeights {n : ℕ} (w : Fin n → ℤ) :
    ∑ i, centeredWeights w i = 0 := by
  simp [centeredWeights, Finset.sum_sub_distrib, ← Finset.mul_sum]

theorem monomialWeight_centeredWeights {n : ℕ}
    (w : Fin n → ℤ) (d : Fin n →₀ ℕ) :
    monomialWeight (centeredWeights w) d =
      (n : ℤ) * monomialWeight w d - (d.degree : ℤ) * ∑ j, w j := by
  unfold monomialWeight centeredWeights
  simp only [mul_sub, Finset.sum_sub_distrib]
  rw [← Finset.sum_mul, Finsupp.degree_eq_sum, Nat.cast_sum]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring

/-- A homogeneous cubic with nonnegative support weights and negative
total variable weight has strictly positive centered support weights. -/
theorem positive_centeredWeights_of_negative_sum
    {K : Type*} [CommRing K] {n : ℕ}
    (F : MvPolynomial (Fin n) K) (hF : F.IsHomogeneous 3)
    (w : Fin n → ℤ) (hW : HasNonnegativeWeights F w)
    (hnegative : ∑ i, w i < 0) : HasPositiveWeights F (centeredWeights w) := by
  intro d hd
  have hdegree : d.degree = 3 := by
    rw [Finsupp.degree_eq_weight_one]
    exact hF (Finsupp.mem_support_iff.mp hd)
  rw [monomialWeight_centeredWeights, hdegree]
  have hprod : 0 ≤ (n : ℤ) * monomialWeight w d :=
    mul_nonneg (Nat.cast_nonneg n) (hW d hd)
  norm_num at *
  omega

/-- Complete centering conclusion for a cubic, with its support certified
by the actual trilinear coefficient tensor. -/
theorem exists_zero_sum_positive_weights_of_thirdPartials
    {K : Type*} [Field K] [CharZero K] {n : ℕ}
    (F : MvPolynomial (Fin n) K) (hF : F.IsHomogeneous 3)
    (w : Fin n → ℤ)
    (hT : ∀ i j k, thirdPartialCoefficient F i j k ≠ 0 →
      0 ≤ w i + w j + w k)
    (hnegative : ∑ i, w i < 0) :
    ∃ w' : Fin n → ℤ, (∑ i, w' i) = 0 ∧ HasPositiveWeights F w' :=
  ⟨centeredWeights w, sum_centeredWeights w,
    positive_centeredWeights_of_negative_sum F hF w
      (nonnegativeWeights_of_thirdPartials F hF w hT) hnegative⟩

theorem positiveWeights_nontrivial
    {K : Type*} [CommRing K] {n : ℕ}
    (F : MvPolynomial (Fin n) K) (hF : F ≠ 0)
    (w : Fin n → ℤ) (hpositive : HasPositiveWeights F w) : w ≠ 0 := by
  intro hw
  obtain ⟨d, hd⟩ := MvPolynomial.support_nonempty.mpr hF
  have hp := hpositive d hd
  simp [hw, monomialWeight] at hp

/-- The centered positive weighting is nontrivial for a nonzero cubic,
so it also has the nontriviality required of the destabilizing subgroup. -/
theorem exists_nontrivial_zero_sum_positive_weights_of_thirdPartials
    {K : Type*} [Field K] [CharZero K] {n : ℕ}
    (F : MvPolynomial (Fin n) K) (hF : F.IsHomogeneous 3) (hne : F ≠ 0)
    (w : Fin n → ℤ)
    (hT : ∀ i j k, thirdPartialCoefficient F i j k ≠ 0 →
      0 ≤ w i + w j + w k)
    (hnegative : ∑ i, w i < 0) :
    ∃ w' : Fin n → ℤ, w' ≠ 0 ∧ (∑ i, w' i) = 0 ∧ HasPositiveWeights F w' := by
  obtain ⟨w', hsum, hpos⟩ :=
    exists_zero_sum_positive_weights_of_thirdPartials F hF w hT hnegative
  exact ⟨w', positiveWeights_nontrivial F hne w' hpos, hsum, hpos⟩

end HessianTheorem11
