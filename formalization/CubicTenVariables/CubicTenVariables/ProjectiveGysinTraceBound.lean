import CubicTenVariables.ProjectiveFourierIdentity
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-! Finite numerical consequences of explicit trace formula, weight and
high-degree cancellation data. The complex numbers below are supplied data;
this module constructs no cohomology groups or Gysin morphisms and asserts
no literature result. The conclusions concern the actual projective counts
and the actual Fourier and complete sums already defined in the project. -/

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace CubicTenVariables.ProjectiveGysinTraceBound

open MvPolynomial ProjectiveFourierIdentity
open scoped BigOperators

/-- Alternating trace through degrees `0,...,N-1`. -/
def alternatingSum (t : ℕ → ℂ) (N : ℕ) : ℂ :=
  ∑ k ∈ Finset.range N, (-1 : ℂ)^k * t k

/-- The trace after a degree-two shift and a Tate twist of weight two. -/
def shiftedTrace (q : ℝ) (t : ℕ → ℂ) (k : ℕ) : ℂ :=
  if 2 ≤ k then (q : ℂ) * t (k-2) else 0

def shiftedRank (b : ℕ → ℕ) (k : ℕ) : ℕ :=
  if 2 ≤ k then b (k-2) else 0

theorem alternatingSum_shiftedTrace (q : ℝ) (t : ℕ → ℂ) (N : ℕ) :
    alternatingSum (shiftedTrace q t) (N+2) = (q : ℂ) * alternatingSum t N := by
  unfold alternatingSum
  rw [show N+2 = 2+N by omega, Finset.sum_range_add]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, shiftedTrace]
  simp only [show ¬ 2 ≤ 0 by omega, show ¬ 2 ≤ 1 by omega,
    if_false, mul_zero, add_zero, zero_add]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [if_pos (by omega), show 2+k-2 = k by omega, pow_add]
  norm_num
  ring

theorem sum_shiftedRank (b : ℕ → ℕ) (N : ℕ) :
    ∑ k ∈ Finset.range (N+2), shiftedRank b k = ∑ k ∈ Finset.range N, b k := by
  rw [show N+2 = 2+N by omega, Finset.sum_range_add]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, shiftedRank]
  simp only [show ¬ 2 ≤ 0 by omega, show ¬ 2 ≤ 1 by omega,
    if_false, add_zero, zero_add]
  apply Finset.sum_congr rfl
  intro k hk
  simp

/-- Multiplication by q changes the bound at degree k-2 into the bound at k. -/
theorem shiftedTrace_weight (q : ℝ) (hq : 1 ≤ q) (t : ℕ → ℂ)
    (b : ℕ → ℕ) (hw : ∀ k, ‖t k‖ ≤ (b k : ℝ) * q^((k : ℝ)/2))
    (k : ℕ) :
    ‖shiftedTrace q t k‖ ≤ (shiftedRank b k : ℝ) * q^((k : ℝ)/2) := by
  have hq0 : 0 < q := by linarith
  by_cases hk : 2 ≤ k
  · simp only [shiftedTrace, shiftedRank, if_pos hk, norm_mul,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hq0.le]
    calc
      q * ‖t (k-2)‖ ≤ q * ((b (k-2) : ℝ) * q^(((k-2 : ℕ) : ℝ)/2)) :=
        mul_le_mul_of_nonneg_left (hw _) hq0.le
      _ = (b (k-2) : ℝ) * q^((k : ℝ)/2) := by
        rw [Nat.cast_sub hk]
        push_cast
        have he : (k : ℝ)/2 = 1 + ((k : ℝ)-2)/2 := by ring
        rw [he, Real.rpow_add hq0, Real.rpow_one]
        ring
  · simp [shiftedTrace, shiftedRank, hk]

/-- Only the displayed finite degree range is used in the cancellation.
The two total rank bounds may be any supplied real numbers. -/
theorem alternating_difference_bound
    (q BX BH : ℝ) (hq : 1 ≤ q) (N threshold : ℕ) (hthreshold : 2 ≤ threshold)
    (tX tH : ℕ → ℂ) (bX bH : ℕ → ℕ)
    (hX : ∀ k, ‖tX k‖ ≤ (bX k : ℝ) * q^((k : ℝ)/2))
    (hH : ∀ k, ‖tH k‖ ≤ (bH k : ℝ) * q^((k : ℝ)/2))
    (hBX : (∑ k ∈ Finset.range (N+2), (bX k : ℝ)) ≤ BX)
    (hBH : (∑ k ∈ Finset.range N, (bH k : ℝ)) ≤ BH)
    (hcancel : ∀ k ∈ Finset.range (N+2), threshold < k →
      tX k = (q : ℂ) * tH (k-2)) :
    ‖(q : ℂ) * alternatingSum tH N - alternatingSum tX (N+2)‖ ≤
      (BX+BH) * q^((threshold : ℝ)/2) := by
  classical
  have hq0 : 0 < q := by linarith
  have hw := shiftedTrace_weight q hq tH bH hH
  have hb (k : ℕ) (hk : k ∈ Finset.range (N+2)) :
      ‖shiftedTrace q tH k - tX k‖ ≤
        ((bX k : ℝ) + (shiftedRank bH k : ℝ)) * q^((threshold : ℝ)/2) := by
    by_cases ht : k ≤ threshold
    · have hp : q^((k : ℝ)/2) ≤ q^((threshold : ℝ)/2) :=
        Real.rpow_le_rpow_of_exponent_le hq
          (div_le_div_of_nonneg_right (by exact_mod_cast ht) (by norm_num))
      calc
        _ ≤ ‖shiftedTrace q tH k‖ + ‖tX k‖ := norm_sub_le _ _
        _ ≤ (shiftedRank bH k : ℝ) * q^((k : ℝ)/2) +
            (bX k : ℝ) * q^((k : ℝ)/2) := add_le_add (hw k) (hX k)
        _ = ((bX k : ℝ) + (shiftedRank bH k : ℝ)) * q^((k : ℝ)/2) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hp (by positivity)
    · have hc := hcancel k hk (by omega)
      have hk2 : 2 ≤ k := by omega
      rw [shiftedTrace, if_pos hk2, ← hc, sub_self, norm_zero]
      positivity
  rw [← alternatingSum_shiftedTrace q tH N]
  unfold alternatingSum
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ k ∈ Finset.range (N+2),
        ‖(-1 : ℂ)^k * shiftedTrace q tH k - (-1 : ℂ)^k * tX k‖ :=
      norm_sum_le _ _
    _ = ∑ k ∈ Finset.range (N+2), ‖shiftedTrace q tH k - tX k‖ := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [← mul_sub, norm_mul, norm_pow]
      simp
    _ ≤ ∑ k ∈ Finset.range (N+2),
        ((bX k : ℝ) + (shiftedRank bH k : ℝ)) * q^((threshold : ℝ)/2) :=
      Finset.sum_le_sum hb
    _ = ((∑ k ∈ Finset.range (N+2), (bX k : ℝ)) +
        (∑ k ∈ Finset.range N, (bH k : ℝ))) * q^((threshold : ℝ)/2) := by
      rw [← Finset.sum_mul, Finset.sum_add_distrib]
      congr 2
      exact_mod_cast sum_shiftedRank bH N
    _ ≤ _ := mul_le_mul_of_nonneg_right (add_le_add hBX hBH) (Real.rpow_nonneg hq0.le _)

/-- Generic numerical trace-formula consequence. `NX` and `NH` are ordinary
natural point counts, and both alternating trace identities are premises. -/
theorem projective_counts_bound
    (q BX BH : ℝ) (hq : 1 ≤ q) (NX NH N threshold : ℕ)
    (hthreshold : 2 ≤ threshold) (tX tH : ℕ → ℂ) (bX bH : ℕ → ℕ)
    (hcountX : (NX : ℂ) = alternatingSum tX (N+2))
    (hcountH : (NH : ℂ) = alternatingSum tH N)
    (hX : ∀ k, ‖tX k‖ ≤ (bX k : ℝ) * q^((k : ℝ)/2))
    (hH : ∀ k, ‖tH k‖ ≤ (bH k : ℝ) * q^((k : ℝ)/2))
    (hBX : (∑ k ∈ Finset.range (N+2), (bX k : ℝ)) ≤ BX)
    (hBH : (∑ k ∈ Finset.range N, (bH k : ℝ)) ≤ BH)
    (hcancel : ∀ k ∈ Finset.range (N+2), threshold < k →
      tX k = (q : ℂ) * tH (k-2)) :
    ‖1 + (q : ℂ)*(NH : ℂ) - (NX : ℂ)‖ ≤
      (1+BX+BH) * q^((threshold : ℝ)/2) := by
  have hb := alternating_difference_bound q BX BH hq N threshold hthreshold
    tX tH bX bH hX hH hBX hBH hcancel
  have hone : 1 ≤ q^((threshold : ℝ)/2) := Real.one_le_rpow hq (by positivity)
  rw [hcountX, hcountH, add_sub_assoc]
  calc
    _ ≤ ‖(1 : ℂ)‖ + ‖(q : ℂ)*alternatingSum tH N - alternatingSum tX (N+2)‖ :=
      norm_add_le _ _
    _ ≤ 1 + (BX+BH)*q^((threshold : ℝ)/2) := by simpa using add_le_add_left hb 1
    _ ≤ q^((threshold : ℝ)/2) + (BX+BH)*q^((threshold : ℝ)/2) := by linarith
    _ = _ := by ring

/-- The supplied trace data now represent the actual quotient-projective
point counts. This conclusion is the literal normalized Fourier sum, for
every finite field and every nontrivial additive character. -/
theorem normalizedFourierSum_bound {K : Type*} [Field K] [Fintype K]
    {n d : ℕ} (ψ : AddChar K ℂ) (hψ : ψ ≠ 1)
    (F : MvPolynomial (Fin n) K) (hF : F.IsHomogeneous d) (hd : 0 < d)
    (v : Fin n → K) (hv : v ≠ 0) (BX BH : ℝ) (N threshold : ℕ)
    (hthreshold : 2 ≤ threshold) (tX tH : ℕ → ℂ) (bX bH : ℕ → ℕ)
    (hcountX : (Nat.card (zeroPoints F) : ℂ) = alternatingSum tX (N+2))
    (hcountH : (Nat.card (sectionPoints F v) : ℂ) = alternatingSum tH N)
    (hX : ∀ k, ‖tX k‖ ≤ (bX k : ℝ) * (Fintype.card K : ℝ)^((k : ℝ)/2))
    (hH : ∀ k, ‖tH k‖ ≤ (bH k : ℝ) * (Fintype.card K : ℝ)^((k : ℝ)/2))
    (hBX : (∑ k ∈ Finset.range (N+2), (bX k : ℝ)) ≤ BX)
    (hBH : (∑ k ∈ Finset.range N, (bH k : ℝ)) ≤ BH)
    (hcancel : ∀ k ∈ Finset.range (N+2), threshold < k →
      tX k = (Fintype.card K : ℂ) * tH (k-2)) :
    ‖normalizedFourierSum ψ F v‖ ≤
      (1+BX+BH) * (Fintype.card K : ℝ)^((threshold : ℝ)/2) := by
  rw [normalizedFourierSum_eq_projective_counts ψ hψ F hF hd v hv]
  have hq : (1 : ℝ) ≤ Fintype.card K := by exact_mod_cast Fintype.card_pos (α := K)
  simpa only [Complex.ofReal_natCast] using
    projective_counts_bound (Fintype.card K) BX BH hq
      (Nat.card (zeroPoints F)) (Nat.card (sectionPoints F v)) N threshold
      hthreshold tX tH bX bH hcountX hcountH hX hH hBX hBH
      (by simpa only [Complex.ofReal_natCast] using hcancel)

/-- The prime complete sum gains exactly one power of p. The nonzero
frequency condition is imposed after reduction modulo p. -/
theorem completeCubicSum_bound {n d : ℕ}
    (F : MvPolynomial (Fin n) ℤ) (hF : F.IsHomogeneous d) (hd : 0 < d)
    (p : ℕ) [Fact p.Prime] (v : Fin n → ℤ)
    (hv : (fun i => (v i : ZMod p)) ≠ 0) (BX BH : ℝ) (N threshold : ℕ)
    (hthreshold : 2 ≤ threshold) (tX tH : ℕ → ℂ) (bX bH : ℕ → ℕ)
    (hcountX : (Nat.card (zeroPoints (map (Int.castRingHom (ZMod p)) F)) : ℂ) =
      alternatingSum tX (N+2))
    (hcountH : (Nat.card (sectionPoints (map (Int.castRingHom (ZMod p)) F)
      (fun i => (v i : ZMod p))) : ℂ) = alternatingSum tH N)
    (hX : ∀ k, ‖tX k‖ ≤ (bX k : ℝ) * (p : ℝ)^((k : ℝ)/2))
    (hH : ∀ k, ‖tH k‖ ≤ (bH k : ℝ) * (p : ℝ)^((k : ℝ)/2))
    (hBX : (∑ k ∈ Finset.range (N+2), (bX k : ℝ)) ≤ BX)
    (hBH : (∑ k ∈ Finset.range N, (bH k : ℝ)) ≤ BH)
    (hcancel : ∀ k ∈ Finset.range (N+2), threshold < k →
      tX k = (p : ℂ) * tH (k-2)) :
    ‖completeCubicSum F p v‖ ≤
      (1+BX+BH) * (p : ℝ)^((threshold : ℝ)/2+1) := by
  have hp : (1 : ℝ) ≤ p := by exact_mod_cast (Fact.out : p.Prime).one_lt.le
  have hp0 : (0 : ℝ) < p := by linarith
  have hb := projective_counts_bound (p : ℝ) BX BH hp
    (Nat.card (zeroPoints (map (Int.castRingHom (ZMod p)) F)))
    (Nat.card (sectionPoints (map (Int.castRingHom (ZMod p)) F)
      (fun i => (v i : ZMod p)))) N threshold hthreshold
    tX tH bX bH hcountX hcountH hX hH hBX hBH
    (by simpa only [Complex.ofReal_natCast] using hcancel)
  rw [completeCubicSum_eq_projective_counts F hF hd p v hv, norm_mul]
  have hnorm : ‖(p : ℂ)‖ = (p : ℝ) := by simp
  rw [hnorm]
  calc
    _ ≤ (p : ℝ) * ((1+BX+BH) * (p : ℝ)^((threshold : ℝ)/2)) :=
      mul_le_mul_of_nonneg_left (by simpa only [Complex.ofReal_natCast] using hb) hp0.le
    _ = _ := by rw [Real.rpow_add hp0, Real.rpow_one]; ring

/-- Literal ten-variable threshold 9+e, with trace arrays through degree 16
for X and through degree 14 for its hyperplane section. -/
theorem normalizedFourierSum_bound_ten {K : Type*} [Field K] [Fintype K]
    (ψ : AddChar K ℂ) (hψ : ψ ≠ 1) (F : MvPolynomial (Fin 10) K)
    (hF : F.IsHomogeneous 3) (v : Fin 10 → K) (hv : v ≠ 0)
    (BX BH : ℝ) (e : ℕ) (tX tH : ℕ → ℂ) (bX bH : ℕ → ℕ)
    (hcountX : (Nat.card (zeroPoints F) : ℂ) = alternatingSum tX 17)
    (hcountH : (Nat.card (sectionPoints F v) : ℂ) = alternatingSum tH 15)
    (hX : ∀ k, ‖tX k‖ ≤ (bX k : ℝ) * (Fintype.card K : ℝ)^((k : ℝ)/2))
    (hH : ∀ k, ‖tH k‖ ≤ (bH k : ℝ) * (Fintype.card K : ℝ)^((k : ℝ)/2))
    (hBX : (∑ k ∈ Finset.range 17, (bX k : ℝ)) ≤ BX)
    (hBH : (∑ k ∈ Finset.range 15, (bH k : ℝ)) ≤ BH)
    (hcancel : ∀ k ∈ Finset.range 17, 9+e < k →
      tX k = (Fintype.card K : ℂ) * tH (k-2)) :
    ‖normalizedFourierSum ψ F v‖ ≤
      (1+BX+BH) * (Fintype.card K : ℝ)^((9+(e : ℝ))/2) := by
  simpa only [Nat.cast_add, Nat.cast_ofNat] using
    normalizedFourierSum_bound ψ hψ F hF (by norm_num) v hv BX BH 15 (9+e)
      (by omega) tX tH bX bH hcountX hcountH hX hH hBX hBH hcancel

/-- The manuscript's prime exponent (11+e)/2 for the actual ten-variable
complete cubic sum. This does not supply the trace/cancellation data. -/
theorem completeCubicSum_bound_ten
    (F : MvPolynomial (Fin 10) ℤ) (hF : F.IsHomogeneous 3)
    (p : ℕ) [Fact p.Prime] (v : Fin 10 → ℤ)
    (hv : (fun i => (v i : ZMod p)) ≠ 0) (BX BH : ℝ) (e : ℕ)
    (tX tH : ℕ → ℂ) (bX bH : ℕ → ℕ)
    (hcountX : (Nat.card (zeroPoints (map (Int.castRingHom (ZMod p)) F)) : ℂ) =
      alternatingSum tX 17)
    (hcountH : (Nat.card (sectionPoints (map (Int.castRingHom (ZMod p)) F)
      (fun i => (v i : ZMod p))) : ℂ) = alternatingSum tH 15)
    (hX : ∀ k, ‖tX k‖ ≤ (bX k : ℝ) * (p : ℝ)^((k : ℝ)/2))
    (hH : ∀ k, ‖tH k‖ ≤ (bH k : ℝ) * (p : ℝ)^((k : ℝ)/2))
    (hBX : (∑ k ∈ Finset.range 17, (bX k : ℝ)) ≤ BX)
    (hBH : (∑ k ∈ Finset.range 15, (bH k : ℝ)) ≤ BH)
    (hcancel : ∀ k ∈ Finset.range 17, 9+e < k → tX k = (p : ℂ) * tH (k-2)) :
    ‖completeCubicSum F p v‖ ≤ (1+BX+BH) * (p : ℝ)^((11+(e : ℝ))/2) := by
  have hb := completeCubicSum_bound F hF (by norm_num) p v hv BX BH 15 (9+e)
    (by omega) tX tH bX bH hcountX hcountH hX hH hBX hBH hcancel
  have he : ((9+e : ℕ) : ℝ)/2+1 = (11+(e : ℝ))/2 := by push_cast; ring
  rw [he] at hb
  exact hb

end CubicTenVariables.ProjectiveGysinTraceBound
