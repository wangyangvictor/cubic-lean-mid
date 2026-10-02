import HessianTheorem11.RadialPureCube
import HessianTheorem11.MatrixSingleRank
import HessianTheorem11.RankGapVanishing

/-! The actual Hessian of a split pure cube gains one rank away from its
zero coordinate. On an irreducible base attaining the complementary rank,
the common rank bound therefore forces that coordinate to vanish everywhere. -/

noncomputable section
namespace HessianTheorem11
open MvPolynomial Matrix Module
variable {K : Type*} [Field K] [CharZero K] {n : ℕ}

theorem hessian_eraseCoordinate_row (G : MvPolynomial (Fin n) K) (c : Fin n)
    (x : Fin n → K) (j : Fin n) : hessian (eraseCoordinate c G) x c j = 0 := by
  simp [hessian, hessianPolynomial]

theorem hessian_eraseCoordinate_col (G : MvPolynomial (Fin n) K) (c : Fin n)
    (x : Fin n → K) (i : Fin n) : hessian (eraseCoordinate c G) x i c = 0 := by
  have hs := congrArg (fun M : Matrix (Fin n) (Fin n) K => M i c)
    (hessian_symmetric (eraseCoordinate c G) x)
  exact hs.symm.trans (hessian_eraseCoordinate_row G c x i)

theorem hessian_add_pure_cube (G : MvPolynomial (Fin n) K) (c : Fin n)
    (κ : K) (x : Fin n → K) :
    hessian (G + C κ * X c ^ 3) x = hessian G x + Matrix.single c c (6 * κ * x c) := by
  classical
  ext i j
  simp only [hessian, hessianPolynomial, map_add, Matrix.add_apply]
  congr 1
  have hthree (k : Fin n) : pderiv k (3 : MvPolynomial (Fin n) K) = 0 := by
    exact (pderiv k).map_natCast 3
  by_cases hi : i = c <;> by_cases hj : j = c <;>
    simp [hi, hj, pderiv_C_mul, pderiv_pow, pderiv_mul, Pi.single_apply,
      hthree, Matrix.single, eq_comm]
  all_goals (try tauto)
  all_goals ring

theorem hessian_rank_gap_of_pure_cube
    (G : MvPolynomial (Fin n) K) (c : Fin n) (κ : K)
    (hsplit : G = eraseCoordinate c G + C κ * X c ^ 3)
    (hκ : κ ≠ 0) (x : Fin n → K) (hxc : x c ≠ 0) :
    (hessian (eraseCoordinate c G) x).rank < (hessian G x).rank := by
  have hH : hessian G x = hessian (eraseCoordinate c G) x +
      Matrix.single c c (6 * κ * x c) := by
    conv_lhs => rw [hsplit]
    exact hessian_add_pure_cube _ c κ x
  rw [hH]
  exact rank_lt_add_single _ c _ (hessian_eraseCoordinate_row G c x)
    (hessian_eraseCoordinate_col G c x) (mul_ne_zero (mul_ne_zero (by norm_num) hκ) hxc)

/-- The exceptional pure-cube coordinate vanishes on the entire actual
irreducible rank-bounded base. -/
theorem pure_cube_coordinate_vanishes_on_base
    (MR : GenericMatrixRankInput) (G : GeometricPolynomial n) (c : Fin n)
    (κ : GeometricField) (hsplit : G = eraseCoordinate c G + C κ * X c ^ 3)
    (hκ : κ ≠ 0) (Z : Set (GeometricPoint n)) (hZ : GeometricallyIrreducible Z)
    (r : ℕ) (hbound : ∀ x ∈ Z, (hessian G x).rank ≤ r)
    (hattained : ∃ x ∈ Z, x c = 0 ∧ r ≤ (hessian G x).rank) :
    ∀ x ∈ Z, x c = 0 := by
  suffices hv : ∀ x ∈ Z, eval x (X c : GeometricPolynomial n) = 0 by
    simpa only [eval_X] using hv
  apply polynomial_vanishes_of_rank_gap MR Z hZ (hessianPolynomial G)
    (hessianPolynomial (eraseCoordinate c G)) (X c) r hbound
  · obtain ⟨x, hx, hxc, hr⟩ := hattained
    refine ⟨x, hx, ?_⟩
    have hH : hessian G x = hessian (eraseCoordinate c G) x := by
      conv_lhs => rw [hsplit]
      rw [hessian_add_pure_cube, hxc]
      simp
    change r ≤ (hessian (eraseCoordinate c G) x).rank
    rwa [← hH]
  · intro x hx hxc
    change (hessian (eraseCoordinate c G) x).rank < (hessian G x).rank
    exact hessian_rank_gap_of_pure_cube G c κ hsplit hκ x (by simpa using hxc)

end HessianTheorem11
