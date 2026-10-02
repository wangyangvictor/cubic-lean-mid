import CubicTenVariables.ComplementMergedSieve

/-! Monotonicity of the literal complementary sieve profile: increasing
scales decreases the profile, and increasing the progression parameter
increases it. The exact finite dimension and progression tables satisfy
all required exponent signs. -/
set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.ComplementSieveProfileMono
open StratifiedSieveData ComplementMergedSieve
open scoped BigOperators

/-- Every denominator exponent is nonnegative under these explicit
conditions on the dimension sequence and progression exponent. -/
theorem profile_le {s : ℕ} (d : Fin s → ℕ) (hd : Antitone d)
    (α : ℝ) (hα : 0 ≤ α) (hfirst : ∀ i, (d i : ℝ)+1 ≤ α)
    (R S : Fin s → ℝ) (hR : ∀ i, 1 ≤ R i) (hRS : ∀ i, R i ≤ S i)
    (T U : ℝ) (hT : 0 ≤ T) (hTU : T ≤ U) :
    profile d S T α ≤ profile d R U α := by
  have hRpos (i) : 0 < R i := zero_lt_one.trans_le (hR i)
  have hSpos (i) : 0 < S i := (hRpos i).trans_le (hRS i)
  have hU : 0 ≤ U := hT.trans hTU
  have hn : T^α ≤ U^α := Real.rpow_le_rpow hT hTU hα
  have hdp : 0 < ∏ i, (R i)^(α-(d i : ℝ)-1) :=
    Finset.prod_pos (fun i _ => Real.rpow_pos_of_pos (hRpos i) _)
  have hds : 0 < ∏ i, (S i)^(α-(d i : ℝ)-1) :=
    Finset.prod_pos (fun i _ => Real.rpow_pos_of_pos (hSpos i) _)
  have hdle : (∏ i, (R i)^(α-(d i : ℝ)-1)) ≤ ∏ i, (S i)^(α-(d i : ℝ)-1) :=
    Finset.prod_le_prod (fun i _ => Real.rpow_nonneg (hRpos i).le _)
      (fun i _ => Real.rpow_le_rpow (hRpos i).le (hRS i) (by linarith [hfirst i]))
  have hfirstTerm : T^α/(∏ i, (S i)^(α-(d i : ℝ)-1)) ≤
      U^α/(∏ i, (R i)^(α-(d i : ℝ)-1)) := by
    calc
      _ ≤ U^α/(∏ i, (S i)^(α-(d i : ℝ)-1)) := div_le_div_of_nonneg_right hn hds.le
      _ ≤ _ := div_le_div_of_nonneg_left (Real.rpow_nonneg hU _) hdp hdle
  have htail (j : Fin s) : T^((d j : ℝ)+1)/
      (∏ i, if j < i then (S i)^((d j : ℝ)-(d i : ℝ)) else 1) ≤
      U^((d j : ℝ)+1)/(∏ i, if j < i then (R i)^((d j : ℝ)-(d i : ℝ)) else 1) := by
    have hp : 0 < ∏ i, if j < i then (R i)^((d j : ℝ)-(d i : ℝ)) else 1 := by
      apply Finset.prod_pos
      intro i _
      split_ifs
      · exact Real.rpow_pos_of_pos (hRpos i) _
      · exact zero_lt_one
    have hs : 0 < ∏ i, if j < i then (S i)^((d j : ℝ)-(d i : ℝ)) else 1 := by
      apply Finset.prod_pos
      intro i _
      split_ifs
      · exact Real.rpow_pos_of_pos (hSpos i) _
      · exact zero_lt_one
    have hden : (∏ i, if j < i then (R i)^((d j : ℝ)-(d i : ℝ)) else 1) ≤
        ∏ i, if j < i then (S i)^((d j : ℝ)-(d i : ℝ)) else 1 := by
      apply Finset.prod_le_prod
      · intro i _
        split_ifs
        · exact Real.rpow_nonneg (hRpos i).le _
        · exact zero_le_one
      · intro i _
        split_ifs with hji
        · have hdi : (d i : ℝ) ≤ d j := by exact_mod_cast hd hji.le
          exact Real.rpow_le_rpow (hRpos i).le (hRS i) (sub_nonneg.mpr hdi)
        · exact le_rfl
    calc
      _ ≤ U^((d j : ℝ)+1)/(∏ i, if j < i then (S i)^((d j : ℝ)-(d i : ℝ)) else 1) :=
        div_le_div_of_nonneg_right (Real.rpow_le_rpow hT hTU (by positivity)) hs.le
      _ ≤ _ := div_le_div_of_nonneg_left (Real.rpow_nonneg hU _) hp hden
  unfold profile
  exact add_le_add (add_le_add le_rfl hfirstTerm) (Finset.sum_le_sum (fun j _ => htail j))

theorem dimensionProfile_antitone (i : Fin 5) : Antitone (dimensionProfile i) := by
  have hh : ∀ i : Fin 5, Antitone (dimensionProfile i) := by decide
  exact hh i

theorem progression_ge_dimension (i : Fin 5) (k : Fin (5-i.val)) :
    dimensionProfile i k+1 ≤ ComplementProgressionCounts.profile i := by
  have hh : ∀ (i : Fin 5) (k : Fin (5-i.val)),
      dimensionProfile i k+1 ≤ ComplementProgressionCounts.profile i := by decide
  exact hh i k

/-- The exact five complement profiles, with the source parameter 1+T. -/
theorem complement_profile_le (i : Fin 5) (R S : Fin (5-i.val) → ℝ)
    (hR : ∀ k, 1 ≤ R k) (hRS : ∀ k, R k ≤ S k)
    (T : ℝ) (hT : 0 ≤ T) :
    profile (dimensionProfile i) S T (ComplementProgressionCounts.profile i : ℝ) ≤
      profile (dimensionProfile i) R (1+T) (ComplementProgressionCounts.profile i : ℝ) := by
  apply profile_le _ (dimensionProfile_antitone i) _ (Nat.cast_nonneg _)
    (fun k => by exact_mod_cast progression_ge_dimension i k) R S hR hRS T (1+T) hT
  linarith

end CubicTenVariables.ComplementSieveProfileMono
