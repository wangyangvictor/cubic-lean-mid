import CubicTenVariables.CompleteSumFrequencyTail

/-! The manuscript's least numerical depths for the literal prime and
prime-square complete sums. One common constant is fixed first. The supplied
coarse estimates give witnesses of depth six; monotonicity identifies the
least-depth inequalities with the actual norm thresholds. No residue
periodicity of the prime-square depth is asserted. -/

set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.NumericalPrimeDepth
open MvPolynomial

/-- Explicit all-prime coarse bounds with one constant. This is arithmetic
data to be supplied by the proved pointwise estimates, not a literature input. -/
structure CoarseBounds (F : MvPolynomial (Fin 10) ℤ) (C : ℝ) : Prop where
  constant_pos : 1 ≤ C
  prime : ∀ (p : ℕ) [Fact p.Prime] (v : Fin 10 → ℤ),
    ‖completeCubicSum F p v‖ ≤ C * (p : ℝ)^((17 : ℝ)/2)
  square : ∀ (p : ℕ) [Fact p.Prime] (v : Fin 10 → ℤ),
    ‖completeCubicSum F (p^2) v‖ ≤ C * (p : ℝ)^17

variable {F : MvPolynomial (Fin 10) ℤ} {C : ℝ}

private theorem prime_threshold_exists (h : CoarseBounds F C)
    (p : ℕ) [Fact p.Prime] (v : Fin 10 → ℤ) :
    ∃ j : ℕ, ‖completeCubicSum F p v‖ ≤ C * (p : ℝ)^((11+(j : ℝ))/2) := by
  refine ⟨6,?_⟩
  have he : (11+(6 : ℝ))/2 = (17 : ℝ)/2 := by norm_num
  simpa only [Nat.cast_ofNat, he] using h.prime p v

private theorem square_threshold_exists (h : CoarseBounds F C)
    (p : ℕ) [Fact p.Prime] (v : Fin 10 → ℤ) :
    ∃ j : ℕ, ‖completeCubicSum F (p^2) v‖ ≤ C * (p : ℝ)^(11+j) :=
  ⟨6,h.square p v⟩

/-- Least exponent increment for the actual prime sum. -/
def primeDepth (h : CoarseBounds F C) (p : ℕ) [Fact p.Prime]
    (v : Fin 10 → ℤ) : ℕ := Nat.find (prime_threshold_exists h p v)

/-- Least exponent increment for the actual prime-square sum at the
specified integer frequency. It is not defined using its reduction modulo p. -/
def squareDepth (h : CoarseBounds F C) (p : ℕ) [Fact p.Prime]
    (v : Fin 10 → ℤ) : ℕ := Nat.find (square_threshold_exists h p v)

theorem prime_bound (h : CoarseBounds F C) (p : ℕ) [Fact p.Prime]
    (v : Fin 10 → ℤ) :
    ‖completeCubicSum F p v‖ ≤ C * (p : ℝ)^((11+(primeDepth h p v : ℝ))/2) :=
  Nat.find_spec (prime_threshold_exists h p v)

theorem square_bound (h : CoarseBounds F C) (p : ℕ) [Fact p.Prime]
    (v : Fin 10 → ℤ) :
    ‖completeCubicSum F (p^2) v‖ ≤ C * (p : ℝ)^(11+squareDepth h p v) :=
  Nat.find_spec (square_threshold_exists h p v)

theorem primeDepth_le_six (h : CoarseBounds F C) (p : ℕ) [Fact p.Prime]
    (v : Fin 10 → ℤ) : primeDepth h p v ≤ 6 := by
  apply Nat.find_min'
  have he : (11+(6 : ℝ))/2 = (17 : ℝ)/2 := by norm_num
  simpa only [Nat.cast_ofNat, he] using h.prime p v

theorem squareDepth_le_six (h : CoarseBounds F C) (p : ℕ) [Fact p.Prime]
    (v : Fin 10 → ℤ) : squareDepth h p v ≤ 6 :=
  Nat.find_min' (square_threshold_exists h p v) (h.square p v)

/-- The exact least-depth characterization, including depth zero. -/
theorem primeDepth_le_iff (h : CoarseBounds F C) (p : ℕ) [hp : Fact p.Prime]
    (v : Fin 10 → ℤ) (j : ℕ) :
    primeDepth h p v ≤ j ↔
      ‖completeCubicSum F p v‖ ≤ C * (p : ℝ)^((11+(j : ℝ))/2) := by
  constructor
  · intro hj
    have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.out.one_lt.le
    have hjR : (primeDepth h p v : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
    have he : (11+(primeDepth h p v : ℝ))/2 ≤ (11+(j : ℝ))/2 := by
      linarith
    exact (prime_bound h p v).trans
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hp1 he)
        (zero_le_one.trans h.constant_pos))
  · exact Nat.find_min' (prime_threshold_exists h p v)

/-- The prime-square threshold is compared at the original integer v. -/
theorem squareDepth_le_iff (h : CoarseBounds F C) (p : ℕ) [hp : Fact p.Prime]
    (v : Fin 10 → ℤ) (j : ℕ) :
    squareDepth h p v ≤ j ↔
      ‖completeCubicSum F (p^2) v‖ ≤ C * (p : ℝ)^(11+j) := by
  constructor
  · intro hj
    have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.out.one_lt.le
    exact (square_bound h p v).trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hp1 (Nat.add_le_add_left hj 11))
        (zero_le_one.trans h.constant_pos))
  · exact Nat.find_min' (square_threshold_exists h p v)

theorem primeDepth_ge_succ_iff (h : CoarseBounds F C) (p : ℕ) [Fact p.Prime]
    (v : Fin 10 → ℤ) (j : ℕ) :
    j+1 ≤ primeDepth h p v ↔
      ¬ ‖completeCubicSum F p v‖ ≤ C * (p : ℝ)^((11+(j : ℝ))/2) := by
  rw [← primeDepth_le_iff h p v j]
  omega

theorem squareDepth_ge_succ_iff (h : CoarseBounds F C) (p : ℕ) [Fact p.Prime]
    (v : Fin 10 → ℤ) (j : ℕ) :
    j+1 ≤ squareDepth h p v ↔
      ¬ ‖completeCubicSum F (p^2) v‖ ≤ C * (p : ℝ)^(11+j) := by
  rw [← squareDepth_le_iff h p v j]
  omega

/-- Actual prime norm certificates imply divisibility at excessive depth.
The certificate's constant may be smaller than the fixed common constant. -/
theorem prime_certificate (h : CoarseBounds F C) (v : Fin 10 → ℤ)
    (Δ j : ℕ) (A : ℝ) (hAC : A ≤ C)
    (hcertificate : ∀ (p : ℕ) [Fact p.Prime], ¬ p ∣ Δ →
      ‖completeCubicSum F p v‖ ≤ A * (p : ℝ)^((11+(j : ℝ))/2)) :
    ∀ (p : ℕ) [Fact p.Prime], j+1 ≤ primeDepth h p v → p ∣ Δ := by
  intro p _ hdepth
  by_contra hp
  apply (primeDepth_ge_succ_iff h p v j).mp hdepth
  exact (hcertificate p hp).trans
    (mul_le_mul_of_nonneg_right hAC (Real.rpow_nonneg (Nat.cast_nonneg p) _))

/-- The corresponding implication for the actual prime-square sums.
No claim about equality of depths at congruent frequencies is used. -/
theorem square_certificate (h : CoarseBounds F C) (v : Fin 10 → ℤ)
    (Δ j : ℕ) (A : ℝ) (hAC : A ≤ C)
    (hcertificate : ∀ (p : ℕ) [Fact p.Prime], ¬ p ∣ Δ →
      ‖completeCubicSum F (p^2) v‖ ≤ A * (p : ℝ)^(11+j)) :
    ∀ (p : ℕ) [Fact p.Prime], j+1 ≤ squareDepth h p v → p ∣ Δ := by
  intro p _ hdepth
  by_contra hp
  apply (squareDepth_ge_succ_iff h p v j).mp hdepth
  exact (hcertificate p hp).trans
    (mul_le_mul_of_nonneg_right hAC (pow_nonneg (Nat.cast_nonneg p) _))

end CubicTenVariables.NumericalPrimeDepth
