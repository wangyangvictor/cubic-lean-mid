import TranslatedDepthSeven.BoundedLinearPrimitiveElementInternal
import Mathlib.Data.Fin.Tuple.Basic

/-!
# One degree-uniform integral primitive coordinate

In an extension of degree at most D, successive two-generator choices use
natural coefficients at most D squared. The resulting coefficients of a
linear combination of n displayed generators are at most (D squared+1)^n.
They are therefore genuinely integral and independent of the coefficient
heights of the extension or its equations.
-/

namespace TranslatedDepthSeven
noncomputable section
open IntermediateField
set_option maxHeartbeats 2500000
set_option synthInstance.maxHeartbeats 300000

universe u v

/-- Every finite displayed family in a finite separable extension has a
primitive linear combination with uniformly bounded natural coefficients. -/
theorem exists_bounded_nat_linearCombination_primitive_element
    (K : Type u) {E : Type v}
    [Field K] [CharZero K] [Field E] [Algebra K E]
    [Algebra.IsSeparable K E] [FiniteDimensional K E]
    (D : ℕ) (hD : Module.finrank K E ≤ D) (n : ℕ) (x : Fin n → E) :
    ∃ c : Fin n → ℕ, (∀ i, c i ≤ (D * D + 1) ^ n) ∧
      K⟮∑ i, (c i : K) • x i⟯ = IntermediateField.adjoin K (Set.range x) := by
  classical
  induction n with
  | zero =>
      refine ⟨fun i ↦ Fin.elim0 i, ?_, ?_⟩
      · intro i
        exact Fin.elim0 i
      · simp
  | succ n ih =>
      obtain ⟨c, hc, hprimitive⟩ := ih (Fin.tail x)
      let beta := ∑ i, (c i : K) • x i.succ
      have hbeta : K⟮beta⟯ = IntermediateField.adjoin K (Set.range (Fin.tail x)) :=
        hprimitive
      obtain ⟨a, ha, hpair⟩ := exists_bounded_nat_linear_primitive_element_pair K (x 0) beta
      have haD : a ≤ D * D := ha.trans
        (Nat.mul_le_mul ((minpoly.natDegree_le (x 0)).trans hD)
          ((minpoly.natDegree_le beta).trans hD))
      let c' : Fin (n + 1) → ℕ := Fin.cases 1 (fun i ↦ a * c i)
      have hsum : (∑ i, (c' i : K) • x i) = x 0 + (a : K) • beta := by
        rw [Fin.sum_univ_succ]
        simp only [c', Fin.cases_zero, Fin.cases_succ, Nat.cast_one, one_smul,
          Nat.cast_mul, mul_smul]
        rw [Finset.smul_sum]
      refine ⟨c', ?_, ?_⟩
      · intro i
        refine Fin.cases ?_ (fun j ↦ ?_) i
        · change 1 ≤ (D * D + 1) ^ (n + 1)
          exact Nat.one_le_pow _ _ (by omega)
        · change a * c j ≤ (D * D + 1) ^ (n + 1)
          calc
            a * c j ≤ (D * D + 1) * (D * D + 1) ^ n :=
              Nat.mul_le_mul (haD.trans (Nat.le_succ _)) (hc j)
            _ = (D * D + 1) ^ (n + 1) := by rw [pow_succ]; exact Nat.mul_comm _ _
      · rw [hsum, ← hpair, Fin.range_fin_succ]
        calc
          K⟮x 0, beta⟯ = IntermediateField.adjoin K
              (Set.insert (x 0) (K⟮beta⟯ : Set E)) :=
            (IntermediateField.adjoin_insert_adjoin (F := K)
              (S := ({beta} : Set E)) (x 0)).symm
          _ = IntermediateField.adjoin K
              (Set.insert (x 0)
                (IntermediateField.adjoin K (Set.range (Fin.tail x)) : Set E)) := by
            rw [hbeta]
          _ = IntermediateField.adjoin K (Set.insert (x 0) (Set.range (Fin.tail x))) :=
            IntermediateField.adjoin_insert_adjoin (F := K)
              (S := Set.range (Fin.tail x)) (x 0)

end
end TranslatedDepthSeven
