import HessianTheorem11.NormalQuadrics

/-! Semistability weight checks in any finite indexed actual basis. -/
noncomputable section
namespace HessianTheorem11
open MvPolynomial Module
variable {K ι : Type*} [Field K] [CharZero K] [Fintype ι] {n : ℕ}

theorem WeightSemistable.nonnegative_weight_sum_of_basis_tensor
    {F : MvPolynomial (Fin n) K} (hsemi : WeightSemistable F) (hF : F.IsHomogeneous 3)
    (b : Basis ι K (Fin n → K)) (w : ι → ℤ)
    (hT : ∀ i j k, polarization F (b i) (b j) (b k) ≠ 0 → 0 ≤ w i+w j+w k) :
    0 ≤ ∑ i, w i := by
  classical
  have hc : Fintype.card ι = n := by
    simpa using (finrank_eq_card_basis b).symm
  let e : ι ≃ Fin n := (Fintype.equivFin ι).trans (finCongr hc)
  let c := b.reindex e
  have hsum : 0 ≤ ∑ i : Fin n, w (e.symm i) := by
    apply hsemi.nonnegative_weight_sum_of_thirdPartials hF (basisMatrix c)
      (basisMatrix_injective c)
    intro i j k hne
    change coeff 0 (pderiv k (pderiv j (pderiv i
      (PolynomialRestriction.restrict (basisMatrix c) F)))) ≠ 0 at hne
    rw [polarization_in_coordinates F hF] at hne
    apply hT (e.symm i) (e.symm j) (e.symm k)
    simpa only [c, Basis.reindex_apply] using hne
  rwa [e.symm.sum_comp w] at hsum

end HessianTheorem11
