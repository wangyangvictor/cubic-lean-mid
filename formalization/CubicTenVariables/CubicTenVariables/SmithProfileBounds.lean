import CubicTenVariables.SmithProfileNumerics

/-!
# Uniform ten-variable bounds for every profile length

The finite certificates are extended here by sums over arbitrary lengths.
The three Phi bounds, and their corresponding D bounds, concern the literal
finite maximum defined in SmithProfileNumerics. They assert no estimate for
actual matrix profiles until the separate geometric/counting arguments are supplied.
-/

noncomputable section
namespace CubicTenVariables.SmithProfileBounds
open SmithProfileNumerics
open scoped BigOperators

private theorem total_eq_head_tail {a : ℕ} (c : Profile (a+1)) :
    (∑ i ∈ Finset.range (a+1), (entry c i : ℚ)) =
      (entry c 0 : ℚ) + ∑ i ∈ Finset.range a, (entry c (i+1) : ℚ) := by
  simpa [add_comm] using Finset.sum_range_succ' (fun i => (entry c i : ℚ)) a

private theorem easy_le {a : ℕ} (c : Profile (a+1)) :
    easyCost c ≤ 9*(a : ℚ) + gamma (entry c 0) := by
  simp only [easyCost, Nat.add_sub_cancel]
  split_ifs
  · rfl
  · linarith [gamma_nonneg (entry c 0)]

private theorem transition_le {a : ℕ} (c : Profile (a+1)) :
    transitionCost c ≤ (a : ℚ)*eta (entry c 0) +
      ∑ i ∈ Finset.range a, (entry c (i+1) : ℚ) := by
  unfold transitionCost
  simp only [Nat.add_sub_cancel]
  calc
    _ ≤ ∑ i ∈ Finset.range a, (eta (entry c 0) + (entry c (i+1) : ℚ)) := by
      apply Finset.sum_le_sum
      intro i hi
      have hi' : i < a := Finset.mem_range.mp hi
      exact transition_envelope _ _ _
        (entry_mono c (Nat.zero_le i) (by omega))
        (entry_mono c (Nat.le_succ i) (by omega)) (by have := entry_lt_eleven c (i+1); omega)
    _ = _ := by simp [Finset.sum_add_distrib]

private theorem score_le_easy {a : ℕ} (c : Profile a) (t : ℕ) :
    score c t ≤ delta (entry c 0) + easyCost c - penalty c t := by
  unfold score
  linarith [min_le_left (easyCost c) (transitionCost c)]

private theorem score_le_average {a : ℕ} (c : Profile a) (t : ℕ) :
    score c t ≤ delta (entry c 0) + (easyCost c + transitionCost c)/2 - penalty c t := by
  unfold score
  linarith [min_le_left (easyCost c) (transitionCost c),
    min_le_right (easyCost c) (transitionCost c)]

private theorem penalty_same {a : ℕ} (c : Profile a) :
    penalty c a = (1/2 : ℚ) * ∑ i ∈ Finset.range a, (entry c i : ℚ) := by
  unfold penalty
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  simp [penaltyWeight, Finset.mem_range.mp hi]

private theorem penalty_up {a : ℕ} (c : Profile (a+1)) :
    penalty c (a+2) = (1/2 : ℚ) * (∑ i ∈ Finset.range (a+1), (entry c i : ℚ)) +
      (1/2 : ℚ) * (entry c a : ℚ) := by
  have hw (i : ℕ) (hi : i < a) : penaltyWeight (a+1) (a+2) i = 1/2 := by
    have ht : ¬a+2 ≤ a+1 := by omega
    have hiZ : (i : ℤ) < 2*(a+1 : ℕ)-(a+2 : ℕ) := by omega
    simp only [penaltyWeight, if_neg ht, if_pos hiZ]
  have hlast : penaltyWeight (a+1) (a+2) a = 1 := by
    have ht : ¬a+2 ≤ a+1 := by omega
    have hiZ : ¬(a : ℤ) < 2*(a+1 : ℕ)-(a+2 : ℕ) := by omega
    simp only [penaltyWeight, if_neg ht, if_neg hiZ]
  unfold penalty
  rw [Finset.sum_range_succ, Finset.sum_range_succ, hlast]
  have hs : (∑ i ∈ Finset.range a, penaltyWeight (a+1) (a+2) i * (entry c i : ℚ)) =
      (1/2 : ℚ) * ∑ i ∈ Finset.range a, (entry c i : ℚ) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun i hi => by rw [hw i (Finset.mem_range.mp hi)])
  rw [hs]
  ring

private theorem penalty_down {e : ℕ} (c : Profile (e+1)) :
    penalty c e = (1/2 : ℚ) * ∑ i ∈ Finset.range e, (entry c i : ℚ) := by
  unfold penalty
  rw [Finset.sum_range_succ]
  have hlast : penaltyWeight (e+1) e e = 0 := by simp [penaltyWeight]
  rw [hlast, zero_mul, add_zero, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  simp [penaltyWeight, Finset.mem_range.mp hi]

/-- Arbitrary-length diagonal profile bound; no finite bound on a is imposed. -/
theorem score_diag_le (a : ℕ) (c : Profile (a+1)) : score c (a+1) ≤ 7*(a : ℚ)+5 := by
  have hs := score_le_average c (a+1)
  have he := easy_le c
  have ht := transition_le c
  rw [penalty_same, total_eq_head_tail] at hs
  have hc := certificate_one (entry c 0) (by have := entry_lt_eleven c 0; omega)
  have heta : (a : ℚ)*eta (entry c 0) ≤ (a : ℚ)*5 :=
    mul_le_mul_of_nonneg_left (eta_le_five _) (Nat.cast_nonneg a)
  linarith

/-- Arbitrary-length neighboring profile bound, using the extra last-coordinate penalty. -/
theorem score_up_le (a : ℕ) (c : Profile (a+1)) : score c (a+2) ≤ 7*(a : ℚ)+2 := by
  have hs := score_le_average c (a+2)
  have he := easy_le c
  have ht := transition_le c
  rw [penalty_up, total_eq_head_tail] at hs
  have hc := certificate_two (entry c 0) (by have := entry_lt_eleven c 0; omega)
  have hm : (entry c 0 : ℚ) ≤ entry c a := by
    exact_mod_cast entry_mono c (Nat.zero_le a) (Nat.lt_succ_self a)
  have heta : (a : ℚ)*eta (entry c 0) ≤ (a : ℚ)*5 :=
    mul_le_mul_of_nonneg_left (eta_le_five _) (Nat.cast_nonneg a)
  linarith

private theorem transition_down_le (b : ℕ) (c : Profile (b+3)) :
    transitionCost c ≤ (b+1 : ℕ)*eta (entry c 0) +
      (∑ i ∈ Finset.range (b+1), (entry c (i+1) : ℚ)) + 10 := by
  unfold transitionCost
  have ha : b+3-1 = (b+1)+1 := by omega
  rw [ha, Finset.sum_range_succ]
  have he : (∑ i ∈ Finset.range (b+1), tau (entry c i + entry c (i+1))) ≤
      (b+1 : ℕ)*eta (entry c 0) + ∑ i ∈ Finset.range (b+1), (entry c (i+1) : ℚ) := by
    calc
      _ ≤ ∑ i ∈ Finset.range (b+1), (eta (entry c 0) + (entry c (i+1) : ℚ)) := by
        apply Finset.sum_le_sum
        intro i hi
        have hi' : i < b+1 := Finset.mem_range.mp hi
        exact transition_envelope _ _ _
          (entry_mono c (Nat.zero_le i) (by omega))
          (entry_mono c (Nat.le_succ i) (by omega))
          (by have := entry_lt_eleven c (i+1); omega)
      _ = _ := by simp [Finset.sum_add_distrib]
  exact add_le_add he (tau_le_ten _)

private theorem score_down_large_le (b : ℕ) (c : Profile (b+3)) :
    score c (b+2) ≤ 7*(b+2 : ℕ)+7 := by
  have hs := score_le_average c (b+2)
  have he := easy_le (a := b+2) c
  have ht := transition_down_le b c
  have hp : penalty c (b+2) = (1/2 : ℚ)*
      ((entry c 0 : ℚ) + ∑ i ∈ Finset.range (b+1), (entry c (i+1) : ℚ)) := by
    rw [penalty_down]
    rw [Finset.sum_range_succ']
    ring
  rw [hp] at hs
  have hc := certificate_three (entry c 0) (by have := entry_lt_eleven c 0; omega)
  have heta : (b : ℚ)*eta (entry c 0) ≤ (b : ℚ)*5 :=
    mul_le_mul_of_nonneg_left (eta_le_five _) (Nat.cast_nonneg b)
  push_cast at he ht ⊢
  nlinarith

private theorem score_down_one_le (c : Profile 2) : score c 1 ≤ 14 := by
  have hs := score_le_easy c 1
  have he := easy_le (a := 1) c
  have hp : penalty c 1 = (1/2 : ℚ)*(entry c 0 : ℚ) := by
    rw [penalty_down]
    simp
  have hc := certificate_four (entry c 0) (by have := entry_lt_eleven c 0; omega)
  rw [hp] at hs
  norm_num at he
  linarith

/-- The third neighboring profile bound, uniformly for every positive e. -/
theorem score_down_le (e : ℕ) (he : 1 ≤ e) (c : Profile (e+1)) :
    score c e ≤ 7*(e : ℚ)+7 := by
  obtain rfl | he2 := eq_or_lt_of_le he
  · norm_num
    exact score_down_one_le c
  · obtain ⟨b, rfl⟩ : ∃ b, e = b+2 := ⟨e-2, by omega⟩
    simpa using score_down_large_le b c

/-- Phi(e,e) ≤ 7e−2 for all e≥1, as a bound on the actual finite maximum. -/
theorem phi_diag_le (e : ℕ) (he : 1 ≤ e) : phi e e ≤ 7*(e : ℚ)-2 := by
  obtain ⟨a, rfl⟩ : ∃ a, e = a+1 := ⟨e-1, by omega⟩
  apply phi_le
  intro c
  have h := score_diag_le a c
  push_cast
  linarith

/-- Phi(e,e+1) ≤ 7e−5 for every positive e. -/
theorem phi_up_le (e : ℕ) (he : 1 ≤ e) : phi e (e+1) ≤ 7*(e : ℚ)-5 := by
  obtain ⟨a, rfl⟩ : ∃ a, e = a+1 := ⟨e-1, by omega⟩
  apply phi_le
  intro c
  have h := score_up_le a c
  push_cast
  linarith

/-- Phi(e+1,e) ≤ 7e+7 for every positive e. -/
theorem phi_down_le (e : ℕ) (he : 1 ≤ e) : phi (e+1) e ≤ 7*(e : ℚ)+7 :=
  phi_le _ _ _ (score_down_le e he)

theorem localD_diag_le (e : ℕ) (he : 1 ≤ e) : localD e e ≤ 30*(e : ℚ)-2 := by
  unfold localD
  linarith [phi_diag_le e he]

theorem localD_up_le (e : ℕ) (he : 1 ≤ e) : localD e (e+1) ≤ 30*(e : ℚ)+6 := by
  unfold localD
  have h := phi_up_le e he
  push_cast
  linarith

theorem localD_down_le (e : ℕ) (he : 1 ≤ e) : localD (e+1) e ≤ 30*(e : ℚ)+19 := by
  unfold localD
  have h := phi_down_le e he
  push_cast
  linarith

end CubicTenVariables.SmithProfileBounds
