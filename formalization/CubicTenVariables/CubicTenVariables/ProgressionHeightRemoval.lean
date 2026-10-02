import CubicTenVariables.AmbientProgressionCount
import CubicTenVariables.StratifiedSieveData

/-! Remove the progression modulus from the height loss in the actual
point-count estimates. For a modulus larger than the box radius the ambient
progression count is bounded absolutely. This supplies the exact hypothesis
of the stratified sieve, uniformly in the progression modulus. -/

set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.ProgressionHeightRemoval
open ConeComponentProgressionCount SimultaneousResidueCount StratifiedSieveData

/-- A progression count with height `2+norm(u)+L+m` implies the sieve's
height `L+norm(u)`, with no dependence on the varying modulus in its constant. -/
theorem exists_bound {n : ℕ} (P : Set (Fin n → ℚ)) (k : ℕ)
    (ε : ℝ) (hε : 0 < ε)
    (hcount : ∃ C : ℝ, 1 ≤ C ∧ ∀ (u : Fin n → ℝ) (L : ℝ), 0 ≤ L →
      ∀ m : ℕ, 0 < m → ∀ b : Fin n → ℤ,
        ((points P u L m b).card : ℝ) ≤
          C*(2+‖u‖+L+(m : ℝ))^ε*(1+L/(m : ℝ))^k) :
    ∃ A : ℝ, 1 ≤ A ∧
      ProgressionBound {x : Fin n → ℤ | (fun i => (x i : ℚ)) ∈ P} (k : ℝ) ε A := by
  classical
  obtain ⟨C,hC,hcount⟩ := hcount
  let A : ℝ := 1+C*(4 : ℝ)^ε+(8 : ℝ)^n
  have hC0 : 0 ≤ C := zero_le_one.trans hC
  have hfour : 0 ≤ (4 : ℝ)^ε := by positivity
  have height_constant : 0 ≤ C*(4 : ℝ)^ε := mul_nonneg hC0 hfour
  have ambient_constant : 0 ≤ (8 : ℝ)^n := by positivity
  have hA : 1 ≤ A := by dsimp [A]; linarith
  have height_ge (u : Fin n → ℝ) (L : ℝ) (hL : 1 ≤ L) : 1 ≤ L+‖u‖ :=
    by linarith [norm_nonneg u]
  refine ⟨A,hA,?_⟩
  intro u L hL m hm b S hmem hbox hres
  have hL0 : 0 ≤ L := zero_le_one.trans hL
  have hm0 : 0 < (m : ℝ) := by exact_mod_cast hm
  have hT : 1 ≤ 1+L/(m : ℝ) := by linarith [div_nonneg hL0 hm0.le]
  have hH := height_ge u L hL
  have hsub : S ⊆ points P u L m b := by
    intro x hx
    exact (mem_points P u L m b x).mpr ⟨hbox x hx,hres x hx,hmem x hx⟩
  have hcard : (S.card : ℝ) ≤ ((points P u L m b).card : ℝ) := by
    exact_mod_cast Finset.card_le_card hsub
  rw [Real.rpow_natCast]
  by_cases hsmall : (m : ℝ) ≤ L
  · have hh : 2+‖u‖+L+(m : ℝ) ≤ 4*(L+‖u‖) := by
      linarith [norm_nonneg u]
    have hscale : (2+‖u‖+L+(m : ℝ))^ε ≤ (4 : ℝ)^ε*(L+‖u‖)^ε := by
      rw [← Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 4) (by linarith : 0 ≤ L+‖u‖)]
      exact Real.rpow_le_rpow (by positivity) hh hε.le
    calc
      _ ≤ C*(2+‖u‖+L+(m : ℝ))^ε*(1+L/(m : ℝ))^k :=
        hcard.trans (hcount u L hL0 m hm b)
      _ ≤ C*((4 : ℝ)^ε*(L+‖u‖)^ε)*(1+L/(m : ℝ))^k := by gcongr
      _ = (C*(4 : ℝ)^ε)*(L+‖u‖)^ε*(1+L/(m : ℝ))^k := by ring
      _ ≤ A*(L+‖u‖)^ε*(1+L/(m : ℝ))^k := by
        apply mul_le_mul_of_nonneg_right
        · apply mul_le_mul_of_nonneg_right
          · dsimp [A]; linarith
          · positivity
        · positivity
  · have hdiv : L/(m : ℝ) ≤ 1 := (div_le_one hm0).mpr (le_of_not_ge hsmall)
    have hbounded : ((points P u L m b).card : ℝ) ≤ (8 : ℝ)^n := by
      calc
        _ ≤ (4 : ℝ)^n*(1+L/(m : ℝ))^n := AmbientProgressionCount.card_le P u L hL0 m hm b
        _ ≤ (4 : ℝ)^n*(2 : ℝ)^n := by gcongr; linarith
        _ = _ := by rw [← mul_pow]; norm_num
    have hp : 1 ≤ (L+‖u‖)^ε := Real.one_le_rpow hH hε.le
    have ht : 1 ≤ (1+L/(m : ℝ))^k := one_le_pow₀ hT
    have hA8 : (8 : ℝ)^n ≤ A := by dsimp [A]; linarith
    calc
      _ ≤ (8 : ℝ)^n := hcard.trans hbounded
      _ ≤ A := hA8
      _ ≤ A*(L+‖u‖)^ε := le_mul_of_one_le_right (by dsimp [A]; positivity) hp
      _ ≤ _ := le_mul_of_one_le_right (by dsimp [A]; positivity) ht

/-- The family of actual point-count estimates discharges the complete
progression hypothesis, including arbitrary finite subsets and moduli. -/
theorem progressionHypothesis {n : ℕ} (P : Set (Fin n → ℚ)) (k : ℕ)
    (hcount : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 1 ≤ C ∧
      ∀ (u : Fin n → ℝ) (L : ℝ), 0 ≤ L → ∀ m : ℕ, 0 < m →
      ∀ b : Fin n → ℤ, ((points P u L m b).card : ℝ) ≤
        C*(2+‖u‖+L+(m : ℝ))^ε*(1+L/(m : ℝ))^k) :
    ProgressionHypothesis {x : Fin n → ℤ | (fun i => (x i : ℚ)) ∈ P} (k : ℝ) :=
  fun ε hε => exists_bound P k ε hε (hcount ε hε)

/-- The ordinary dimension counts are also admissible sieve progression
bounds, with the harmless positive height power inserted internally. -/
theorem of_uniform_bound {n : ℕ} (P : Set (Fin n → ℚ)) (k : ℕ)
    (hcount : ∃ C : ℝ, 1 ≤ C ∧ ∀ (u : Fin n → ℝ) (L : ℝ), 0 ≤ L →
      ∀ m : ℕ, 0 < m → ∀ b : Fin n → ℤ,
        ((points P u L m b).card : ℝ) ≤ C*(1+L/(m : ℝ))^k) :
    ProgressionHypothesis {x : Fin n → ℤ | (fun i => (x i : ℚ)) ∈ P} (k : ℝ) := by
  obtain ⟨C,hC,hcount⟩ := hcount
  apply progressionHypothesis P k
  intro ε hε
  refine ⟨C,hC,?_⟩
  intro u L hL m hm b
  have hH : 1 ≤ 2+‖u‖+L+(m : ℝ) := by
    linarith [norm_nonneg u,(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
  calc
    _ ≤ C*(1+L/(m : ℝ))^k := hcount u L hL m hm b
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (le_mul_of_one_le_right (zero_le_one.trans hC) (Real.one_le_rpow hH hε.le))
      (by positivity)

/-- Removing frequencies preserves the sieve progression hypothesis. -/
theorem mono {n : ℕ} {U V : Set (Fin n → ℤ)} {α : ℝ}
    (hUV : U ⊆ V) (hV : ProgressionHypothesis V α) : ProgressionHypothesis U α := by
  intro ε hε
  obtain ⟨A,hA,hcount⟩ := hV ε hε
  refine ⟨A,hA,?_⟩
  intro u L hL m hm b S hS hbox hres
  exact hcount u L hL m hm b S (fun x hx => hUV (hS x hx)) hbox hres

/-- The U3 piece includes an incoming open as well as a promoted part;
a finite union with the same exponent retains one uniform constant. -/
theorem union {n : ℕ} {U V : Set (Fin n → ℤ)} {α : ℝ}
    (hU : ProgressionHypothesis U α) (hV : ProgressionHypothesis V α) :
    ProgressionHypothesis (U ∪ V) α := by
  classical
  intro ε hε
  obtain ⟨A,hA,hcountU⟩ := hU ε hε
  obtain ⟨B,hB,hcountV⟩ := hV ε hε
  refine ⟨A+B,by linarith,?_⟩
  intro u L hL m hm b S hS hbox hres
  let SU := S.filter fun x => x ∈ U
  let SV := S.filter fun x => x ∈ V
  have hsub : S ⊆ SU ∪ SV := by
    intro x hx
    rcases hS x hx with hu | hv
    · exact Finset.mem_union.mpr (Or.inl (Finset.mem_filter.mpr ⟨hx,hu⟩))
    · exact Finset.mem_union.mpr (Or.inr (Finset.mem_filter.mpr ⟨hx,hv⟩))
  have hc : (S.card : ℝ) ≤ (SU.card : ℝ)+(SV.card : ℝ) := by
    exact_mod_cast (Finset.card_le_card hsub).trans (Finset.card_union_le SU SV)
  have hcu := hcountU u L hL m hm b SU
    (fun x hx => (Finset.mem_filter.mp hx).2)
    (fun x hx => hbox x (Finset.mem_filter.mp hx).1)
    (fun x hx => hres x (Finset.mem_filter.mp hx).1)
  have hcv := hcountV u L hL m hm b SV
    (fun x hx => (Finset.mem_filter.mp hx).2)
    (fun x hx => hbox x (Finset.mem_filter.mp hx).1)
    (fun x hx => hres x (Finset.mem_filter.mp hx).1)
  calc
    _ ≤ (SU.card : ℝ)+(SV.card : ℝ) := hc
    _ ≤ A*(L+‖u‖)^ε*(1+L/(m : ℝ))^α+B*(L+‖u‖)^ε*(1+L/(m : ℝ))^α := add_le_add hcu hcv
    _ = _ := by ring

end CubicTenVariables.ProgressionHeightRemoval
