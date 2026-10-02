import TranslatedDepthSeven.IntegerGridAvoidance

/-!
# A fixed natural-number grid over every characteristic-zero field

Only total degree, not coefficient height or a common denominator, controls
the grid needed to find a nonzero value. This permits degree-bounded
equations over a rational-function field or an algebraic extension to be
used with a fixed integral list of candidate coefficients.
-/

namespace TranslatedDepthSeven
noncomputable section
open MvPolynomial

theorem exists_nonzero_eval_on_boundedNatGrid_over_field
    {K : Type*} [Field K] [CharZero K] {N D : ℕ}
    (f : MvPolynomial (Fin N) K) (hf : f ≠ 0) (hdegree : f.totalDegree ≤ D) :
    ∃ x : Fin N → ℕ, (∀ i, x i ≤ D) ∧ MvPolynomial.eval (fun i ↦ (x i : K)) f ≠ 0 := by
  classical
  let S : Finset K := (Finset.range (D + 1)).image (fun j : ℕ ↦ (j : K))
  have hScard : S.card = D + 1 := by
    dsimp only [S]
    rw [Finset.card_image_of_injective _ Nat.cast_injective, Finset.card_range]
  have hexists : ∃ y ∈ Fintype.piFinset (fun _ : Fin N ↦ S), MvPolynomial.eval y f ≠ 0 := by
    by_contra h
    push_neg at h
    have hfilter : (Fintype.piFinset (fun _ : Fin N ↦ S)).filter
        (fun y ↦ MvPolynomial.eval y f = 0) = Fintype.piFinset (fun _ : Fin N ↦ S) := by
      ext y
      simp only [Finset.mem_filter]
      exact ⟨And.left, fun hy ↦ ⟨hy, h y hy⟩⟩
    have hsz := MvPolynomial.schwartz_zippel_totalDegree hf S
    rw [hfilter, Fintype.card_piFinset, hScard] at hsz
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, Nat.cast_pow] at hsz
    have hpos : (0 : ℚ≥0) < (D + 1 : ℕ) ^ N := by positivity
    rw [div_self (ne_of_gt hpos)] at hsz
    have hfrac : (f.totalDegree : ℚ≥0) / (D + 1 : ℕ) ≤
        (D : ℚ≥0) / (D + 1 : ℕ) :=
      div_le_div_of_nonneg_right (by exact_mod_cast hdegree) (by positivity)
    have hlt : (D : ℚ≥0) / (D + 1 : ℕ) < 1 := by
      apply (div_lt_one (by positivity)).mpr
      exact_mod_cast Nat.lt_succ_self D
    exact (hsz.trans hfrac).not_gt hlt
  obtain ⟨y, hy, hne⟩ := hexists
  have hchoice (i : Fin N) : ∃ a : ℕ, a ∈ Finset.range (D + 1) ∧ (a : K) = y i :=
    Finset.mem_image.mp (Fintype.mem_piFinset.mp hy i)
  choose x hx hxy using hchoice
  refine ⟨x, fun i ↦ Nat.le_of_lt_succ (Finset.mem_range.mp (hx i)), ?_⟩
  simpa only [funext hxy] using hne

end
end TranslatedDepthSeven
