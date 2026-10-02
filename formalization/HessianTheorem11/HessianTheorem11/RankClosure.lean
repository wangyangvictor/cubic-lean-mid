import HessianTheorem11.GenericRankBridge
import HessianTheorem11.AffineGeometry

/-! Extending an actual rank bound from an irreducible set to its Zariski
closure, using only the general open-minor rank theorem already in use. -/
noncomputable section
namespace HessianTheorem11
open MvPolynomial

theorem polynomialMatrix_rank_le_on_closure
    (MR : GenericMatrixRankInput)
    {σ : Type} [Fintype σ] {a b : ℕ}
    (Z : Set (σ → GeometricField)) (hirred : GeometricallyIrreducible Z)
    (M : Matrix (Fin a) (Fin b) (MvPolynomial σ GeometricField)) (r : ℕ)
    (hbound : ∀ x ∈ Z, (M.map (eval x)).rank ≤ r) :
    ∀ x ∈ geometricClosure Z, (M.map (eval x)).rank ≤ r := by
  let I := vanishingIdeal GeometricField Z
  letI : I.IsPrime := hirred
  obtain ⟨q, hq, hgeneric⟩ := MR.principal_open I M
  obtain ⟨y, hy, hyq⟩ : ∃ y ∈ Z, eval y q ≠ 0 := by
    by_contra h
    push_neg at h
    exact hq h
  have hyI : y ∈ zeroLocus GeometricField I := subset_geometricClosure Z hy
  have hr : genericMatrixRank I M ≤ r := by
    rw [← hgeneric y hyI hyq]
    exact hbound y hy
  intro x hx
  exact (MR.specialization_le I M x hx).trans hr

end HessianTheorem11
