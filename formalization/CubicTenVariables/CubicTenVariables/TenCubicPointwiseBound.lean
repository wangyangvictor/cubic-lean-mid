import CubicTenVariables.CubicShiftedBoxBound
import CubicTenVariables.CubicDifferencingOptimization
import CubicTenVariables.PrimeSumAdapter

/-! Epsilon-free complete cubic sum estimates in ten variables, proved by
finite differencing and the already proved Davenport Hessian-rank counts.
The hypotheses are the literal homogeneous cubic and absence of a nonzero
integer zero. Bernert's singular-series theorem is not an input. -/

set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.TenCubicPointwiseBound
open MvPolynomial
open scoped BigOperators

/-- The bound is uniform in every positive modulus and every unit scalar. -/
theorem exists_unit_bound (F : MvPolynomial (Fin 10) ℤ) (hF : F.IsHomogeneous 3)
    (hzero : ¬ HasIntegerZero F) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (q : ℕ) [NeZero q] (a : (ZMod q)ˣ),
      ‖∑ x : Fin 10 → ZMod q,
        ZMod.stdAddChar ((a : ZMod q) * eval₂ (Int.castRingHom (ZMod q)) x F)‖ ≤
        C * (q : ℝ)^(25/3 : ℝ) := by
  obtain ⟨A,hA,hbox⟩ := CubicShiftedBoxBound.exists_bound F hF hzero
  refine ⟨32*A+1, by linarith, ?_⟩
  intro q _ a
  apply CubicDifferencingOptimization.bound_of_box_inequality
    (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)) hA (norm_nonneg _)
  intro B hB
  exact hbox q B hB a

/-- The same estimate for the actual integer-representative scalar sum.
The coprimality hypothesis is the original `(a,q)=1` condition. -/
theorem exists_scalar_bound (F : MvPolynomial (Fin 10) ℤ) (hF : F.IsHomogeneous 3)
    (hzero : ¬ HasIntegerZero F) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (q : ℕ), 0 < q → ∀ a : Fin q,
      Nat.Coprime a.val q →
      ‖∑ x : Fin 10 → Fin q, residueExponential q (completeSumPhase F a x 0)‖ ≤
        C * (q : ℝ)^(25/3 : ℝ) := by
  obtain ⟨C,hC,hbound⟩ := exists_unit_bound F hF hzero
  refine ⟨C,hC,?_⟩
  intro q hq a ha
  letI : NeZero q := ⟨hq.ne'⟩
  obtain ⟨u,hu⟩ := (ZMod.isUnit_iff_coprime a.val q).mpr ha
  have heq : (∑ x : Fin 10 → Fin q,
      residueExponential q (completeSumPhase F a x 0)) =
      ∑ x : Fin 10 → ZMod q,
        ZMod.stdAddChar ((u : ZMod q) * eval₂ (Int.castRingHom (ZMod q)) x F) := by
    apply Fintype.sum_equiv (PrimeSumAdapter.vectorResidueEquiv q 10) _ _
    intro x
    rw [PrimeSumAdapter.residueExponential_completeSumPhase, hu]
    simp only [Pi.zero_apply, Int.cast_zero, dotProduct, zero_mul, Finset.sum_const_zero, add_zero,
      PrimeSumAdapter.vectorResidueEquiv_apply, eval₂_eq_eval_map]
  rw [heq]
  exact hbound q u

/-- Summing the scalar estimate over at most `q` coprime coefficients gives
the literal aggregate bound `S_q(0) ≪ q^(28/3)`. -/
theorem exists_complete_bound (F : MvPolynomial (Fin 10) ℤ) (hF : F.IsHomogeneous 3)
    (hzero : ¬ HasIntegerZero F) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ q : ℕ, 0 < q →
      ‖completeCubicSum F q 0‖ ≤ C * (q : ℝ)^(28/3 : ℝ) := by
  classical
  obtain ⟨C,hC,hbound⟩ := exists_scalar_bound F hF hzero
  refine ⟨C,hC,?_⟩
  intro q hq
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  calc
    _ ≤ ∑ a : Fin q, ‖if Nat.Coprime a.val q then
        ∑ x : Fin 10 → Fin q, residueExponential q (completeSumPhase F a x 0)
        else 0‖ := norm_sum_le _ _
    _ ≤ ∑ _a : Fin q, C * (q : ℝ)^(25/3 : ℝ) := by
      apply Finset.sum_le_sum
      intro a _
      split_ifs with ha
      · exact hbound q hq a ha
      · simp only [norm_zero]
        positivity
    _ = C * (q : ℝ)^(28/3 : ℝ) := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      calc
        _ = C * ((q : ℝ)^(1 : ℝ) * (q : ℝ)^(25/3 : ℝ)) := by rw [Real.rpow_one]; ring
        _ = _ := by rw [← Real.rpow_add hq0]; norm_num

end CubicTenVariables.TenCubicPointwiseBound
