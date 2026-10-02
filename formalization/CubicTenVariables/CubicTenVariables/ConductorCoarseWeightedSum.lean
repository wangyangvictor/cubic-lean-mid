import CubicTenVariables.ConductorCoarseGcdSum
import CubicTenVariables.PrimeConstantEpsilonBound
import CubicTenVariables.PolynomialHeightDivisorBound

/-! Absorption of the distinct-prime-factor weight and the exceptional
integer's divisor count in the elementary coarse modulus sum. -/

set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.ConductorCoarseWeightedSum
open scoped BigOperators

/-- The constant is uniform in both cutoffs, the positive exceptional
integer, and every finite family of positive modulus pairs. -/
theorem exists_bound (C : ℝ) (hC : 1 ≤ C) (ε : ℝ) (hε : 0 < ε) :
    ∃ M : ℝ, 1 ≤ M ∧ ∀ D H : ℝ, 1 ≤ D → 1 ≤ H →
      ∀ c : ℕ, 1 ≤ c → (c : ℝ) ≤ H → ∀ Q : Finset (ℕ × ℕ),
        (∀ x ∈ Q, 1 ≤ x.1 ∧ 1 ≤ x.2 ∧
          (x.1 : ℝ)*(x.2 : ℝ)^2 ≤ 2*D) →
        (∑ x ∈ Q, C^(x.1.primeFactors.card+x.2.primeFactors.card)*
          (x.1 : ℝ)^8*(x.2 : ℝ)^17*(Nat.gcd x.1 c : ℝ)) ≤
          M*(D*H)^ε*D^9 := by
  obtain ⟨A,hA,hprime⟩ := PrimeConstantEpsilonBound.exists_two_factor_bound
    C hC (ε/2) (by linarith)
  obtain ⟨R,hR,hsum⟩ := ConductorCoarseGcdSum.exists_bound (ε/2) (by linarith)
  obtain ⟨B,hB,hdiv⟩ := PolynomialHeightDivisorBound.exists_bound 1 le_rfl 1 ε hε
  let M : ℝ := A*(2 : ℝ)^(ε/2)*R*B
  refine ⟨max 1 M,le_max_left _ _,?_⟩
  intro D H hD hH c hc hcH Q hQ
  have hD0 : 0 < D := zero_lt_one.trans_le hD
  have hH0 : 0 < H := zero_lt_one.trans_le hH
  let g : ℕ × ℕ → ℝ := fun x =>
    (x.1 : ℝ)^8*(x.2 : ℝ)^17*(Nat.gcd x.1 c : ℝ)
  have hg (x : ℕ × ℕ) : 0 ≤ g x := by dsimp [g]; positivity
  have hweight (x : ℕ × ℕ) (hx : x ∈ Q) :
      C^(x.1.primeFactors.card+x.2.primeFactors.card) ≤ A*(2*D)^(ε/2) := by
    have hb1 : (1 : ℝ) ≤ x.2 := by exact_mod_cast (hQ x hx).2.1
    have hab : ((x.1*x.2 : ℕ) : ℝ) ≤ 2*D := by
      rw [Nat.cast_mul]
      have hbb : (x.2 : ℝ) ≤ (x.2 : ℝ)^2 := by nlinarith
      exact (mul_le_mul_of_nonneg_left hbb (Nat.cast_nonneg x.1)).trans (hQ x hx).2.2
    exact (hprime x.1 x.2 (hQ x hx).1 (hQ x hx).2.1).trans
      (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (Nat.cast_nonneg _) hab (by linarith)) (by linarith))
  have hdivc : (c.divisors.card : ℝ) ≤ B*H^ε :=
    hdiv H hH c hc (by simpa only [one_mul,pow_one] using hcH)
  have he : (A*(2*D)^(ε/2))*(R*D^(9+ε/2)*(B*H^ε)) =
      M*(D*H)^ε*D^9 := by
    rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hD0.le,
      Real.mul_rpow hD0.le hH0.le,
      Real.rpow_add hD0,Real.rpow_ofNat]
    have hd : D^(ε/2)*D^(ε/2) = D^ε := by
      rw [← Real.rpow_add hD0]
      congr 1
      ring
    calc
      _ = (A*(2 : ℝ)^(ε/2)*R*B)*
          (D^(ε/2)*D^(ε/2))*H^ε*D^9 := by ring
      _ = _ := by rw [hd]; dsimp [M]; ring
  calc
    _ = ∑ x ∈ Q, C^(x.1.primeFactors.card+x.2.primeFactors.card)*g x := by
      apply Finset.sum_congr rfl
      intro x _
      dsimp [g]
      ring
    _ ≤ ∑ x ∈ Q, (A*(2*D)^(ε/2))*g x :=
      Finset.sum_le_sum (fun x hx => mul_le_mul_of_nonneg_right (hweight x hx) (hg x))
    _ = (A*(2*D)^(ε/2))*∑ x ∈ Q, g x := (Finset.mul_sum ..).symm
    _ ≤ (A*(2*D)^(ε/2))*(R*D^(9+ε/2)*(c.divisors.card : ℝ)) :=
      mul_le_mul_of_nonneg_left (hsum D hD c hc Q hQ) (by positivity)
    _ ≤ (A*(2*D)^(ε/2))*(R*D^(9+ε/2)*(B*H^ε)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hdivc (by positivity)) (by positivity)
    _ = M*(D*H)^ε*D^9 := he
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_right 1 M) (by positivity)) (by positivity)

end CubicTenVariables.ConductorCoarseWeightedSum
