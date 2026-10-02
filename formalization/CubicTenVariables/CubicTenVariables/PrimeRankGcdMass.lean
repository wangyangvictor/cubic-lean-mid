import CubicTenVariables.OnCubicRankCountsTen
import CubicTenVariables.CubicFiniteFieldMass
import CubicTenVariables.PrimeFrogZeroMass

/-!
# Rank-conditioned prime gcd mass

One constant bounds both the actual on-cubic exact-rank counts and their
literal two-gcd weighted masses. The initial rank counts and gradient-zero
count are proved dependencies; no point-count or literature premise remains.
-/

noncomputable section
namespace CubicTenVariables.PrimeRankGcdMass
open MvPolynomial HessianTheorem11 OnCubicRankCountsTen PrimeFrogZeroMass
open scoped BigOperators

/-- The source's additional prime exponent in the easy Hessian lift bound. -/
def gammaNat (r : ℕ) : ℕ :=
  (if deltaNat r ≤ 5 then 1 else 0) + (if r = 0 then 1 else 0)

theorem gammaNat_eq_gamma (r : ℕ) (hr : r ≤ 10) :
    (gammaNat r : ℚ) = SmithProfileNumerics.gamma r := by
  interval_cases r <;>
    norm_num [gammaNat, deltaNat, SmithProfileNumerics.gamma, SmithProfileNumerics.delta]

variable {n : ℕ}

/-- Actual reduced cubic roots of one exact Hessian rank. -/
def exactRankRoots (F : MvPolynomial (Fin n) ℤ) (p r : ℕ) [Fact p.Prime] :
    Finset (Fin n → ZMod p) := by
  classical
  exact Finset.univ.filter fun x =>
    eval₂ (Int.castRingHom (ZMod p)) x F = 0 ∧
      (hessian (map (Int.castRingHom (ZMod p)) F) x).rank = r

@[simp] theorem mem_exactRankRoots (F : MvPolynomial (Fin n) ℤ)
    (p r : ℕ) [Fact p.Prime] (x : Fin n → ZMod p) :
    x ∈ exactRankRoots F p r ↔
      eval₂ (Int.castRingHom (ZMod p)) x F = 0 ∧
        (hessian (map (Int.castRingHom (ZMod p)) F) x).rank = r := by
  classical
  simp only [exactRankRoots, Finset.mem_filter, Finset.mem_univ, true_and]

theorem card_exactRankRoots_eq (F : MvPolynomial (Fin n) ℤ)
    (p r : ℕ) [Fact p.Prime] :
    (exactRankRoots F p r).card =
      Nat.card {x : Fin n → ZMod p // eval₂ (Int.castRingHom (ZMod p)) x F = 0 ∧
        (hessian (map (Int.castRingHom (ZMod p)) F) x).rank = r} := by
  classical
  simp only [exactRankRoots, Nat.card_eq_fintype_card, Fintype.card_subtype]

/-- Positive rank excludes the origin in every characteristic. -/
theorem ne_zero_of_mem_exactRankRoots (F : MvPolynomial (Fin n) ℤ)
    (hF : F.IsHomogeneous 3) (p r : ℕ) [Fact p.Prime] (hr : 0 < r)
    {x : Fin n → ZMod p} (hx : x ∈ exactRankRoots F p r) : x ≠ 0 := by
  intro hz
  have h := (mem_exactRankRoots F p r x).mp hx
  rw [hz, hessian_zero (hF.map _), Matrix.rank_zero] at h
  omega

/-- Both prime gcd factors are at most p, without any condition on x. -/
theorem rootWeight_le_sq (F : MvPolynomial (Fin n) ℤ)
    (p : ℕ) [Fact p.Prime] (x : Fin n → ZMod p) :
    rootWeight F p x ≤ p^2 := by
  rw [rootWeight_eq F p Fact.out x]
  have hp := (Fact.out : p.Prime).one_le
  split_ifs <;> simp_all only [mul_one, one_mul, pow_two] <;> nlinarith

/-- Away from the origin only the gradient gcd can cost a factor p. -/
theorem rootWeight_le_prime_of_ne_zero (F : MvPolynomial (Fin n) ℤ)
    (p : ℕ) [Fact p.Prime] (x : Fin n → ZMod p) (hx : x ≠ 0) :
    rootWeight F p x ≤ p := by
  rw [rootWeight_eq F p Fact.out x, if_neg hx, mul_one]
  split_ifs
  · exact le_rfl
  · exact (Fact.out : p.Prime).one_le

theorem sum_rootWeight_le_card_mul_sq (F : MvPolynomial (Fin n) ℤ)
    (p r : ℕ) [Fact p.Prime] :
    (∑ x ∈ exactRankRoots F p r, rootWeight F p x) ≤
      (exactRankRoots F p r).card*p^2 := by
  calc
    _ ≤ ∑ _x ∈ exactRankRoots F p r, p^2 :=
      Finset.sum_le_sum fun x _ => rootWeight_le_sq F p x
    _ = _ := by simp

theorem sum_rootWeight_le_card_mul_prime (F : MvPolynomial (Fin n) ℤ)
    (hF : F.IsHomogeneous 3) (p r : ℕ) [Fact p.Prime] (hr : 0 < r) :
    (∑ x ∈ exactRankRoots F p r, rootWeight F p x) ≤
      (exactRankRoots F p r).card*p := by
  calc
    _ ≤ ∑ _x ∈ exactRankRoots F p r, p :=
      Finset.sum_le_sum fun x hx => rootWeight_le_prime_of_ne_zero F p x
        (ne_zero_of_mem_exactRankRoots F hF p r hr hx)
    _ = _ := by simp

/-- At positive rank the excess weighted mass is controlled by the full
actual gradient-zero count, including all exceptional primes. -/
theorem sum_rootWeight_le_card_add_gradient (F : MvPolynomial (Fin n) ℤ)
    (hF : F.IsHomogeneous 3) (p r : ℕ) [Fact p.Prime] (hr : 0 < r) :
    (∑ x ∈ exactRankRoots F p r, rootWeight F p x) ≤
      (exactRankRoots F p r).card +
        p * (Finset.univ.filter (fun x : Fin n → ZMod p =>
          ∀ i, eval₂ (Int.castRingHom (ZMod p)) x (pderiv i F) = 0)).card := by
  classical
  let S := exactRankRoots F p r
  let G := fun x : Fin n → ZMod p =>
    ∀ i, eval₂ (Int.castRingHom (ZMod p)) x (pderiv i F) = 0
  have hgrad : (∑ x ∈ S, if G x then p else 0) ≤
      p * (Finset.univ.filter G).card := by
    calc
      _ ≤ ∑ x : Fin n → ZMod p, if G x then p else 0 :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (by intros; omega)
      _ = _ := by
        rw [← Finset.sum_filter]
        simp [Nat.mul_comm]
  have hpoint : (∑ x ∈ S, rootWeight F p x) ≤
      ∑ x ∈ S, (1 + if G x then p else 0) := by
    apply Finset.sum_le_sum
    intro x hx
    have hn := ne_zero_of_mem_exactRankRoots F hF p r hr hx
    simpa only [if_neg hn, add_zero] using rootWeight_le F p Fact.out x
  simp only [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, mul_one] at hpoint
  exact hpoint.trans (Nat.add_le_add_left hgrad S.card)

/-- The same constant controls the unweighted and gcd-weighted exact-rank
sets. Its choice precedes every prime and rank label. -/
theorem exists_uniform_bounds
    (F : MvPolynomial (Fin 10) ℤ) (hF : F.IsHomogeneous 3)
    (hA : Anisotropic (map (Int.castRingHom ℚ) F)) :
    ∃ B : ℕ, 1 ≤ B ∧ ∀ (p : ℕ) [Fact p.Prime], ∀ r : ℕ, r ≤ 10 →
      (exactRankRoots F p r).card ≤ B*p^(deltaNat r) ∧
      (∑ x ∈ exactRankRoots F p r, rootWeight F p x) ≤
        B*p^(deltaNat r + gammaNat r) := by
  classical
  obtain ⟨C,hC,hcount⟩ := exists_uniform_exact_rank_profile F hF hA
  obtain ⟨G,_hG,hgrad⟩ := CubicFiniteFieldMass.exists_uniform_gradient_zero_bound F hF hA
  refine ⟨C+G, by omega, ?_⟩
  intro p hp r hr
  have hc : (exactRankRoots F p r).card ≤ C*p^(deltaNat r) := by
    rw [card_exactRankRoots_eq]
    exact hcount p r hr
  have hCG : C ≤ C+G := by omega
  constructor
  · exact hc.trans (Nat.mul_le_mul_right _ hCG)
  by_cases hr0 : r = 0
  · subst r
    have hc0 : (exactRankRoots F p 0).card ≤ C := by simpa [deltaNat] using hc
    calc
      _ ≤ (exactRankRoots F p 0).card*p^2 := sum_rootWeight_le_card_mul_sq F p 0
      _ ≤ C*p^2 := Nat.mul_le_mul_right (p^2) hc0
      _ ≤ (C+G)*p^2 := Nat.mul_le_mul_right (p^2) hCG
      _ = (C+G)*p^(deltaNat 0 + gammaNat 0) := by norm_num [deltaNat, gammaNat]
  have hrpos : 0 < r := by omega
  by_cases hr3 : r ≤ 3
  · have hg : gammaNat r = 1 := by
      interval_cases r <;> norm_num [gammaNat, deltaNat] at *
    calc
      _ ≤ (exactRankRoots F p r).card*p := sum_rootWeight_le_card_mul_prime F hF p r hrpos
      _ ≤ (C*p^(deltaNat r))*p := Nat.mul_le_mul_right p hc
      _ = C*p^(deltaNat r + gammaNat r) := by rw [hg, pow_add, pow_one]; ring
      _ ≤ _ := Nat.mul_le_mul_right _ hCG
  · have hd : 6 ≤ deltaNat r := by
      have hr4 : 4 ≤ r := by omega
      interval_cases r <;> norm_num [deltaNat]
    have hg : gammaNat r = 0 := by
      simp only [gammaNat, if_neg (by omega : ¬ deltaNat r ≤ 5), if_neg hr0, zero_add]
    have hG : (Finset.univ.filter (fun x : Fin 10 → ZMod p =>
        ∀ i, eval₂ (Int.castRingHom (ZMod p)) x (pderiv i F) = 0)).card ≤ G*p^5 := by
      simpa only [Nat.card_eq_fintype_card, Fintype.card_subtype,
        HessianTheorem11.gradient, _root_.funext_iff, Pi.zero_apply,
        pderiv_map, eval_map] using hgrad p hp.out
    calc
      _ ≤ (exactRankRoots F p r).card +
          p * (Finset.univ.filter (fun x : Fin 10 → ZMod p =>
            ∀ i, eval₂ (Int.castRingHom (ZMod p)) x (pderiv i F) = 0)).card :=
        sum_rootWeight_le_card_add_gradient F hF p r hrpos
      _ ≤ C*p^(deltaNat r) + p*(G*p^5) :=
        Nat.add_le_add hc (Nat.mul_le_mul_left p hG)
      _ = C*p^(deltaNat r) + G*p^6 := by ring
      _ ≤ C*p^(deltaNat r) + G*p^(deltaNat r) :=
        Nat.add_le_add_left (Nat.mul_le_mul_left G (Nat.pow_le_pow_right hp.out.one_le hd)) _
      _ = (C+G)*p^(deltaNat r + gammaNat r) := by rw [hg, add_zero]; ring

/-- The source rank-specific prime gcd mass with no count or literature input. -/
theorem exists_uniform_bound
    (F : MvPolynomial (Fin 10) ℤ) (hF : F.IsHomogeneous 3)
    (hA : Anisotropic (map (Int.castRingHom ℚ) F)) :
    ∃ B : ℕ, 1 ≤ B ∧ ∀ (p : ℕ) [Fact p.Prime], ∀ r : ℕ, r ≤ 10 →
      (∑ x ∈ exactRankRoots F p r, rootWeight F p x) ≤
        B*p^(deltaNat r + gammaNat r) := by
  obtain ⟨B,hB,hb⟩ := exists_uniform_bounds F hF hA
  exact ⟨B,hB,fun p _ r hr => (hb p r hr).2⟩

/-- An unweighted version with the same literal exact-rank set. -/
theorem exists_uniform_card_bound
    (F : MvPolynomial (Fin 10) ℤ) (hF : F.IsHomogeneous 3)
    (hA : Anisotropic (map (Int.castRingHom ℚ) F)) :
    ∃ B : ℕ, 1 ≤ B ∧ ∀ (p : ℕ) [Fact p.Prime], ∀ r : ℕ, r ≤ 10 →
      (exactRankRoots F p r).card ≤ B*p^(deltaNat r) := by
  obtain ⟨B,hB,hb⟩ := exists_uniform_bounds F hF hA
  exact ⟨B,hB,fun p _ r hr => (hb p r hr).1⟩

end CubicTenVariables.PrimeRankGcdMass
