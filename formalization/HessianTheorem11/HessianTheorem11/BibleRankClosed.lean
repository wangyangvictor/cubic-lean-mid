import HessianTheorem11.NormalPencil
import HessianTheorem11.PolynomialSchurVanishing
import HessianTheorem11.AffineGeometry

/-! Rank sublevel sets of actual polynomial matrices are closed. The proof
uses row and column elimination and determinants, with no geometric input. -/
noncomputable section
namespace HessianTheorem11.BibleLowRank
open MvPolynomial Matrix

theorem polynomialMatrix_rank_locus_closed
    {σ : Type*} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι (MvPolynomial σ GeometricField)) (r : ℕ) :
    AlgebraicallyClosedSet {x : σ → GeometricField | (M.map (eval x)).rank ≤ r} := by
  classical
  apply Set.Subset.antisymm ?_ (subset_geometricClosure _)
  intro x hx
  by_contra hr
  obtain ⟨P,Q,D,hP,hQ,hdiag⟩ :=
    NormalPencil.exists_det_one_diagonal_residue (RingHom.id GeometricField)
      Function.surjective_id (M.map (eval x))
  change P * M.map (eval x) * Q = diagonal D at hdiag
  have hPunit : IsUnit P.det := by rw [hP]; exact isUnit_one
  have hQunit : IsUnit Q.det := by rw [hQ]; exact isUnit_one
  have hrank : (diagonal D).rank = (M.map (eval x)).rank := by
    rw [← hdiag, rank_mul_eq_left_of_isUnit_det _ _ hQunit,
      rank_mul_eq_right_of_isUnit_det _ _ hPunit]
  let S := {i : ι // D i ≠ 0}
  have hs : r < Fintype.card S := by
    rw [rank_diagonal] at hrank
    exact lt_of_not_ge (hrank ▸ hr)
  let N : Matrix ι ι (MvPolynomial σ GeometricField) := P.map C * M * Q.map C
  let p : MvPolynomial σ GeometricField := (N.submatrix (Subtype.val : S → ι) Subtype.val).det
  have heval (y : σ → GeometricField) :
      eval y p = ((P * M.map (eval y) * Q).submatrix
        (Subtype.val : S → ι) Subtype.val).det := by
    rw [show eval y p = (eval y) ((N.submatrix (Subtype.val : S → ι) Subtype.val).det) by rfl,
      RingHom.map_det]
    congr 1
    ext i j
    simp [N, Matrix.submatrix_apply, Matrix.mul_apply]
  have hp : p ∈ vanishingIdeal GeometricField
      {y : σ → GeometricField | (M.map (eval y)).rank ≤ r} := by
    intro y hy
    change eval y p = 0
    rw [heval]
    apply PolynomialSchurVanishing.det_eq_zero_of_rank_lt
    have hsub := PolynomialSchurVanishing.rank_submatrix_le
      (P * M.map (eval y) * Q) (Subtype.val : S → ι) (Subtype.val : S → ι)
    rw [rank_mul_eq_left_of_isUnit_det _ _ hQunit,
      rank_mul_eq_right_of_isUnit_det _ _ hPunit] at hsub
    exact (hsub.trans hy).trans_lt hs
  have hz := hx p hp
  change eval x p = 0 at hz
  rw [heval, hdiag] at hz
  have hd : (diagonal D).submatrix (Subtype.val : S → ι) Subtype.val =
      diagonal (fun i : S => D i) := by
    ext i j
    simp [diagonal_apply, Subtype.val_inj]
  rw [hd, det_diagonal] at hz
  exact (Finset.prod_ne_zero_iff.mpr (fun i _ => i.property)) hz

end HessianTheorem11.BibleLowRank
