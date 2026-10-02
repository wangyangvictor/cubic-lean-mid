import TranslatedDepthSeven.BoundedDistinguishedFinImageInternal
import TranslatedDepthSeven.JacobianCertificatePolynomialHeight

/-!
# Integral rows under the distinguished bounded shear

This is the literal integer coefficient calculation for the normalization
induction. No ideal, Hilbert polynomial or geometric assertion enters the
row norm estimate.
-/

namespace TranslatedDepthSeven
noncomputable section
open MvPolynomial Matrix
open scoped BigOperators
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 300000

/-- Pull an integral row through `X0, X(i+2)-z_i X1`. -/
def distinguishedIntegerRowPullback {s n : ℕ}
    (A : Matrix (Fin s) (Fin (n + 1)) ℤ) (z : Fin n → ℕ) :
    Matrix (Fin s) (Fin (n + 2)) ℤ :=
  fun i ↦ Fin.cases (A i 0)
    (Fin.cases (-(∑ j, A i j.succ * (z j : ℤ))) (fun j ↦ A i j.succ))

theorem distinguishedIntegerRowPullback_rowNorm_le
    {s n D : ℕ} (A : Matrix (Fin s) (Fin (n + 1)) ℤ)
    (z : Fin n → ℕ) (hz : ∀ j, z j ≤ D) (i : Fin s) :
    ∑ j, (distinguishedIntegerRowPullback A z i j).natAbs ≤
      (D + 1) * ∑ j, (A i j).natAbs := by
  have hsum : (∑ j : Fin n, A i j.succ * (z j : ℤ)).natAbs ≤
      D * ∑ j : Fin n, (A i j.succ).natAbs := by
    calc
      _ ≤ ∑ j : Fin n, (A i j.succ * (z j : ℤ)).natAbs :=
        int_natAbs_sum_le_sum_natAbs Finset.univ _
      _ = ∑ j : Fin n, (A i j.succ).natAbs * z j := by
        simp only [Int.natAbs_mul, Int.natAbs_natCast]
      _ ≤ ∑ j : Fin n, (A i j.succ).natAbs * D :=
        Finset.sum_le_sum (fun j _ ↦ Nat.mul_le_mul_left _ (hz j))
      _ = D * ∑ j : Fin n, (A i j.succ).natAbs := by rw [← Finset.sum_mul, Nat.mul_comm]
  simp only [distinguishedIntegerRowPullback, Fin.sum_univ_succ,
    Fin.cases_zero, Fin.cases_succ, Int.natAbs_neg]
  nlinarith [Nat.zero_le (D * (A i 0).natAbs)]

theorem distinguishedIntegerRowPullback_firstRow
    {s n : ℕ} (A : Matrix (Fin (s + 1)) (Fin (n + 1)) ℤ)
    (z : Fin n → ℕ)
    (hfirst : ∀ j, A 0 j = if j = 0 then 1 else 0) :
    ∀ j, distinguishedIntegerRowPullback A z 0 j = if j = 0 then 1 else 0 := by
  intro j
  refine Fin.cases ?_ (fun k ↦ ?_) j
  · simp [distinguishedIntegerRowPullback, hfirst]
  · refine Fin.cases ?_ (fun l ↦ ?_) k
    · change -(∑ j : Fin n, A 0 j.succ * (z j : ℤ)) = 0
      simp [hfirst]
    · simp [distinguishedIntegerRowPullback, hfirst]

theorem indexedMatrixRowLinearPolynomial_distinguishedIntegerRowPullback
    {K : Type*} [Field K] {s n : ℕ}
    (A : Matrix (Fin s) (Fin (n + 1)) ℤ) (z : Fin n → ℕ) (i : Fin s) :
    indexedMatrixRowLinearPolynomial
      ((distinguishedIntegerRowPullback A z).map (Int.castRingHom K)) i =
      aeval (distinguishedFinEliminationForms (K := K) z)
        (indexedMatrixRowLinearPolynomial (A.map (Int.castRingHom K)) i) := by
  change (∑ j, C ((distinguishedIntegerRowPullback A z i j : ℤ) : K) * X j) =
    aeval (distinguishedFinEliminationForms (K := K) z)
      (∑ j, C ((A i j : ℤ) : K) * X j)
  simp only [Fin.sum_univ_succ,
    distinguishedIntegerRowPullback, Fin.cases_zero, Fin.cases_succ,
    map_add, map_sum, map_mul, MvPolynomial.aeval_C, MvPolynomial.aeval_X,
    distinguishedFinEliminationForms,
    Int.cast_neg, Int.cast_sum, Int.cast_mul, Int.cast_natCast, map_neg,
    MvPolynomial.algebraMap_eq]
  have h01 : (0 : Fin (n + 1)).succ = (1 : Fin (n + 2)) := by ext; simp
  rw [h01]
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib]
  simp_rw [← mul_assoc]
  rw [← Finset.sum_mul]
  ring

end
end TranslatedDepthSeven
