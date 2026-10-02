import CubicTenVariables.FixedLeadingSurfaceLineDirectionSum

/-!
# Counting a line family including singleton occurrences

Only active lines have direction height bounded by 2B. The other line
occurrences cost at most one point each; they are kept as an explicit
family-cardinality term. No height cutoff is asserted for inactive lines.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section

namespace CubicTenVariables.FixedLeadingSurfaceLineFamilySum
open MvPolynomial TranslatedDepthSeven Published
open FixedLeadingSurfaceLineDirectionSum FixedLeadingSurfaceLineDirectionSumNumerical
open scoped BigOperators

local instance : DecidableEq (Projectivization ℚ (Fin 3 → ℚ)) := Classical.decEq _

theorem line_points_sum_le_card_add_curve_bound
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (points : ι → Finset (IntVector 3)) (base h : ι → IntVector 3)
    (hp : ∀ l, PrimitiveDirection (h l))
    (I : Ideal (MvPolynomial (Fin 3) ℚ)) (M B : ℕ) (C ε : ℝ)
    (hB : 1 ≤ B) (hC : 0 ≤ C) (hε : 0 < ε)
    (hline : ∀ l, ∀ x ∈ points l, ∃ a : ℚ, ∀ i,
      ((x i - base l i : ℤ) : ℚ) = a * (h l i : ℚ))
    (hbox : ∀ l, ∀ x ∈ points l, ∀ i, |x i| ≤ (B : ℤ))
    (hvanish : ∀ l, ∀ f ∈ I, eval (directionClass (h l) (hp l)).rep f = 0)
    (hmultiple : ∀ P : Projectivization ℚ (Fin 3 → ℚ),
      (Finset.univ.filter fun l => directionClass (h l) (hp l) = P).card ≤ M)
    (hcurve : ∀ R : ℕ, 1 ≤ R →
      (rationalProjectivePoints I (R : ℝ)).Finite ∧
      ((rationalProjectivePoints I (R : ℝ)).ncard : ℝ) ≤ C * (R : ℝ) ^ (1 + ε / 2)) :
    (∑ l, ((points l).card : ℝ)) ≤ (Fintype.card ι : ℝ) +
      (4 * M * C * (1 + pSeriesConstant (ε / 2)) * (2 : ℝ) ^ ε) *
        (B : ℝ) ^ (1 + ε) := by
  classical
  let A := {l : ι // 2 ≤ (points l).card}
  let N := {l : ι // ¬ 2 ≤ (points l).card}
  have hM : ∀ P : Projectivization ℚ (Fin 3 → ℚ),
      (Finset.univ.filter fun l : A => directionClass (h l.val) (hp l.val) = P).card ≤ M := by
    intro P
    apply le_trans _ (hmultiple P)
    apply Finset.card_le_card_of_injOn (fun l : A => l.val)
    · intro l hl
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hl).2⟩
    · exact Subtype.val_injective.injOn
  have hactive := active_line_points_sum_le_target_exponent
    (fun l : A => points l.val) (fun l : A => base l.val) (fun l : A => h l.val)
    (fun l => hp l.val) I M B C ε hB hC hε (fun l => l.property)
    (fun l => hline l.val) (fun l => hbox l.val) (fun l => hvanish l.val) hM hcurve
  have hinactive : (∑ l : N, ((points l.val).card : ℝ)) ≤ (Fintype.card ι : ℝ) := by
    calc
      _ ≤ ∑ _l : N, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro l _
        exact_mod_cast (show (points l.val).card ≤ 1 by have := l.property; omega)
      _ = (Fintype.card N : ℝ) := by simp
      _ ≤ (Fintype.card ι : ℝ) := by
        exact_mod_cast Fintype.card_le_of_injective (fun l : N => l.val) Subtype.val_injective
  have hsplit := Fintype.sum_subtype_add_sum_subtype
    (fun l : ι => 2 ≤ (points l).card) (fun l : ι => ((points l).card : ℝ))
  change (∑ l : A, ((points l.val).card : ℝ)) +
    (∑ l : N, ((points l.val).card : ℝ)) = _ at hsplit
  linarith

end CubicTenVariables.FixedLeadingSurfaceLineFamilySum
