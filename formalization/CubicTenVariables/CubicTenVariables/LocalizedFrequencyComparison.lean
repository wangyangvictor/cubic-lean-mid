import CubicTenVariables.LocalizedSums
import CubicTenVariables.CompleteSumFrequencyTail
import CubicTenVariables.DyadicFrequencyError

/-! Literal localized coefficients and denominators for the remaining
nonzero-frequency reduction. No comparison with the unlocalized complete
sum is assumed. The bounds here are elementary and hold for every residue
restriction, not only the particular local smooth neighborhoods. -/
set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.LocalizedFrequencyComparison
open MvPolynomial
open scoped BigOperators
variable {n : ℕ}

/-- The actual localized denominator lies within a fixed factor of q. -/
theorem denominator_bounds (q W : ℕ) (hq : 0 < q) (hW : 0 < W) :
    q ≤ Nat.lcm q W ∧ Nat.lcm q W ≤ W*q :=
  ⟨Nat.le_lcm_left q hW,by simpa only [Nat.mul_comm] using Nat.lcm_le_mul hq hW⟩

/-- The two characters have absolute value one, even though their moduli
are different. There are q outer terms and lcm(q,W)^n inner terms. -/
theorem trivial_bound (F : MvPolynomial (Fin n) ℤ) (q W : ℕ)
    (hq : 0 < q) (hW : 0 < W) (Ω : Set (Fin n → ZMod W)) (v : Fin n → ℤ) :
    ‖localizedCompleteCubicSum F q W Ω v‖ ≤ (q:ℝ)*(Nat.lcm q W:ℝ)^n := by
  classical
  letI : NeZero q := ⟨hq.ne'⟩
  letI : NeZero (Nat.lcm q W) := ⟨(Nat.lcm_pos hq hW).ne'⟩
  unfold localizedCompleteCubicSum
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ _a : Fin q, (Nat.lcm q W:ℝ)^n := by
      apply Finset.sum_le_sum
      intro a _
      split_ifs with ha
      · apply (norm_sum_le _ _).trans
        calc
          _ ≤ ∑ _x : Fin n → Fin (Nat.lcm q W), (1:ℝ) := by
            apply Finset.sum_le_sum
            intro x _
            split_ifs
            · simp only [norm_mul,PrimeSumAdapter.residueExponential_eq_stdAddChar,
                QuadraticGaussBound.norm_stdAddChar,mul_one]
              exact le_rfl
            · simp only [norm_zero,zero_le_one]
          _ = _ := by simp
      · simp
    _ = _ := by simp

/-- Polynomial growth in q with a constant depending only on fixed W.
This is the growth hypothesis needed for summable frequency tails. -/
theorem growth_bound (F : MvPolynomial (Fin n) ℤ) (q W : ℕ)
    (hq : 0 < q) (hW : 0 < W) (Ω : Set (Fin n → ZMod W)) (v : Fin n → ℤ) :
    ‖localizedCompleteCubicSum F q W Ω v‖ ≤ (W:ℝ)^n*(q:ℝ)^(n+1) := by
  have hden : (Nat.lcm q W:ℝ) ≤ (W:ℝ)*(q:ℝ) := by
    exact_mod_cast (denominator_bounds q W hq hW).2
  calc
    _ ≤ (q:ℝ)*(Nat.lcm q W:ℝ)^n := trivial_bound F q W hq hW Ω v
    _ ≤ (q:ℝ)*((W:ℝ)*(q:ℝ))^n := by gcongr
    _ = _ := by rw [mul_pow,pow_succ]; ring

/-- The true frequency is precisely the ordinary integral frequency with
the denominator replaced by lcm(q,W). -/
theorem frequency_eq (q W : ℕ) (v : Fin n → ℤ) :
    localizedFrequency q W v = (Nat.lcm q W:ℝ)⁻¹ • (fun i => (v i:ℝ)) := by
  ext i
  simp only [localizedFrequency,Pi.smul_apply,smul_eq_mul,div_eq_mul_inv,mul_comm]

/-- Elementary threshold adapter: all localized denominators in the
dyadic circle-method range are at most P² for sufficiently large P. -/
theorem denominator_le_square (P R : ℝ) (q W : ℕ) (hq : 0 < q) (hW : 0 < W)
    (hP : (2*(W:ℝ))^2 ≤ P) (hqR : (q:ℝ) ≤ 2*R)
    (hRP : R ≤ P^((3:ℝ)/2)) : (Nat.lcm q W:ℝ) ≤ P^2 := by
  have hW0 : (0:ℝ) < W := by exact_mod_cast hW
  have hP0 : 0 < P := lt_of_lt_of_le (by positivity) hP
  have hs : 2*(W:ℝ) ≤ P^((1:ℝ)/2) := by
    have hh := Real.sqrt_le_sqrt hP
    simpa only [Real.sqrt_sq (by positivity : 0 ≤ 2*(W:ℝ)),Real.sqrt_eq_rpow] using hh
  calc
    (Nat.lcm q W:ℝ) ≤ (W:ℝ)*(q:ℝ) := by exact_mod_cast (denominator_bounds q W hq hW).2
    _ ≤ (W:ℝ)*(2*R) := mul_le_mul_of_nonneg_left hqR hW0.le
    _ ≤ (W:ℝ)*(2*P^((3:ℝ)/2)) := by gcongr
    _ = (2*(W:ℝ))*P^((3:ℝ)/2) := by ring
    _ ≤ P^((1:ℝ)/2)*P^((3:ℝ)/2) := mul_le_mul_of_nonneg_right hs (by positivity)
    _ = P^2 := by rw [← Real.rpow_add hP0]; norm_num

/-- The localized dyadic error retains the actual lcm normalization and
frequency. Its convergence and final bound remain separate proof obligations. -/
def error (F : MvPolynomial (Fin n) ℤ) (W : ℕ) (Ω : Set (Fin n → ZMod W))
    (w : (Fin n → ℝ) → ℝ) (P R φ : ℝ) : ℝ :=
  ∑ q ∈ DyadicFrequencyError.moduli R, ((Nat.lcm q W:ℝ)^n)⁻¹ *
    ∑' v : Fin n → ℤ, if v=0 then 0 else
      ‖localizedCompleteCubicSum F q W Ω v‖*
        DyadicFrequencyError.frequencyMass F w P φ (Nat.lcm q W) v

/-- Trivial localization recovers the already studied actual dyadic error. -/
@[simp] theorem error_univ_one (F : MvPolynomial (Fin n) ℤ)
    (w : (Fin n → ℝ) → ℝ) (P R φ : ℝ) :
    error F 1 Set.univ w P R φ = DyadicFrequencyError.error F w P R φ := by
  simp only [error,Nat.lcm_one_right,localizedCompleteCubicSum_univ_one,
    DyadicFrequencyError.error,DyadicFrequencyError.term]

end CubicTenVariables.LocalizedFrequencyComparison
