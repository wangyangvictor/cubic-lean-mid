import CubicTenVariables.PrimePowerRamanujan
import CubicTenVariables.PrimePowerRootReduction

/-!
# Exact prime-power root densities and the actual ordinary singular series

The complete sum is the difference of two literal root counts. Normalizing
and telescoping gives a finite identity, without a convergence assumption.
-/

noncomputable section
namespace CubicTenVariables.PrimePowerRootSeriesIdentity
open MvPolynomial
open scoped BigOperators

/-- The unrestricted literal polynomial root count modulo a prime power. -/
def rootCount {n : ℕ} (F : MvPolynomial (Fin n) ℤ)
    (p s : ℕ) [Fact p.Prime] : ℕ :=
  (Finset.univ.filter fun z : Fin n → ZMod (p^s) =>
    eval₂ (Int.castRingHom (ZMod (p^s))) z F = 0).card

@[simp] theorem rootCount_zero {n : ℕ} (F : MvPolynomial (Fin n) ℤ)
    (p : ℕ) [Fact p.Prime] : rootCount F p 0 = 1 :=
  PrimePowerRootReduction.card_roots_level_zero F p

private theorem sum_indicator_const {α : Type*} [Fintype α]
    (P : α → Prop) [DecidablePred P] (c : ℂ) :
    (∑ x, if P x then c else 0) = c * ∑ x, if P x then (1 : ℂ) else 0 := by
  simp only [Finset.mul_sum, mul_ite, mul_one, mul_zero]

/-- Primitive scalar orthogonality gives the exact one-step difference
of full root counts, with the p^n vector-reduction factor included. -/
theorem completeCubicSum_prime_power {n : ℕ} (F : MvPolynomial (Fin n) ℤ)
    (p s : ℕ) [Fact p.Prime] :
    completeCubicSum F (p^(s+1)) 0 =
      (p : ℂ)^(s+1) * (rootCount F p (s+1) : ℂ) -
      (p : ℂ)^(s+n) * (rootCount F p s : ℂ) := by
  classical
  have hswap : completeCubicSum F (p^(s+1)) 0 =
      ∑ x : Fin n → Fin (p^(s+1)), ∑ a : Fin (p^(s+1)),
        if Nat.Coprime a.val (p^(s+1)) then
          residueExponential (p^(s+1)) ((a.val : ℤ)*eval (fun i => ((x i).val : ℤ)) F)
        else 0 := by
    unfold completeCubicSum
    simp only [completeSumPhase, Pi.zero_apply, zero_mul, Finset.sum_const_zero, add_zero]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a ha
    rw [Finset.sum_ite_irrel]
    simp only [Finset.sum_const_zero]
  rw [hswap]
  simp_rw [PrimePowerRamanujan.sum_primitive_scalar]
  rw [Finset.sum_sub_distrib, sum_indicator_const _ ((p : ℂ)^(s+1)),
    sum_indicator_const _ ((p : ℂ)^s)]
  have hhigh := PrimePowerRootReduction.sum_dvd_eval_eq F p (le_refl (s+1))
  have hlow := PrimePowerRootReduction.sum_dvd_eval_eq F p (Nat.le_succ s)
  simp only [Nat.sub_self, zero_mul, pow_zero, one_mul, Nat.cast_pow] at hhigh
  simp only [Nat.succ_eq_add_one, Nat.add_sub_cancel_left, one_mul, Nat.cast_pow] at hlow
  rw [hhigh, hlow]
  simp only [rootCount]
  rw [← mul_assoc, ← pow_add]

/-- The normalization used by the manuscript produces a difference of
successive root densities. The restriction n>=1 is explicit. -/
theorem singularSeriesTerm_prime_power {n : ℕ} (F : MvPolynomial (Fin n) ℤ)
    (hn : 1 ≤ n) (p s : ℕ) [Fact p.Prime] :
    singularSeriesTerm F (p^(s+1)) =
      (rootCount F p (s+1) : ℂ)/(p : ℂ)^((s+1)*(n-1)) -
      (rootCount F p s : ℂ)/(p : ℂ)^(s*(n-1)) := by
  have hp : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  have hpC : (p : ℂ) ≠ 0 := by exact_mod_cast hp
  rw [singularSeriesTerm, if_neg (pow_ne_zero _ hp), completeCubicSum_prime_power]
  simp only [Nat.cast_pow]
  have he1 : (s+1)*n = (s+1)+(s+1)*(n-1) := by
    have := Nat.sub_add_cancel hn
    nlinarith
  have he2 : (s+1)*n = (s+n)+s*(n-1) := by
    have := Nat.sub_add_cancel hn
    nlinarith
  have hpow1 : ((p : ℂ)^(s+1))^n = (p : ℂ)^(s+1)*(p : ℂ)^((s+1)*(n-1)) := by
    rw [← pow_mul, ← pow_add, he1]
  have hpow2 : ((p : ℂ)^(s+1))^n = (p : ℂ)^(s+n)*(p : ℂ)^(s*(n-1)) := by
    rw [← pow_mul, ← pow_add, he2]
  rw [sub_div]
  congr 1
  · rw [hpow1, mul_div_mul_left _ _ (pow_ne_zero _ hpC)]
  · rw [hpow2, mul_div_mul_left _ _ (pow_ne_zero _ hpC)]

/-- An unconditional finite identity between a literal root density and
the actual singular-series terms at all powers of the same prime. -/
theorem root_density_eq_sum {n : ℕ} (F : MvPolynomial (Fin n) ℤ)
    (hn : 1 ≤ n) (p : ℕ) [Fact p.Prime] (s : ℕ) :
    (rootCount F p s : ℂ)/(p : ℂ)^(s*(n-1)) =
      ∑ h ∈ Finset.range (s+1), singularSeriesTerm F (p^h) := by
  induction s with
  | zero => simp
  | succ s ih =>
    rw [Finset.sum_range_succ, ← ih, singularSeriesTerm_prime_power F hn]
    ring

end CubicTenVariables.PrimePowerRootSeriesIdentity
