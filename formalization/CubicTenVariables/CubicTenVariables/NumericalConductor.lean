import CubicTenVariables.NumericalPrimeDepth
import CubicTenVariables.CompleteSumMultiplicativity
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-! The literal numerical conductor, formed from the least depths of the
actual prime and prime-square sums at the same integer frequency. The gcd
majorant uses only divisibility certificates for positive numerical depth;
it makes no assertion that prime-square depth is periodic modulo the prime. -/

set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.NumericalConductor
open MvPolynomial Finset
open NumericalPrimeDepth

variable {F : MvPolynomial (Fin 10) ℤ} {C : ℝ}

/-- Totalization for finite products: nonprime indices have depth zero. -/
def primeDepth (h : CoarseBounds F C) (p : ℕ) (v : Fin 10 → ℤ) : ℕ :=
  if hp : p.Prime then @NumericalPrimeDepth.primeDepth F C h p ⟨hp⟩ v else 0

/-- The square depth still concerns the actual integer frequency. -/
def squareDepth (h : CoarseBounds F C) (p : ℕ) (v : Fin 10 → ℤ) : ℕ :=
  if hp : p.Prime then @NumericalPrimeDepth.squareDepth F C h p ⟨hp⟩ v else 0

@[simp] theorem primeDepth_of_prime (h : CoarseBounds F C) (p : ℕ)
    [hp : Fact p.Prime] (v : Fin 10 → ℤ) :
    primeDepth h p v = NumericalPrimeDepth.primeDepth h p v := by
  simp [primeDepth, hp.out]

@[simp] theorem squareDepth_of_prime (h : CoarseBounds F C) (p : ℕ)
    [hp : Fact p.Prime] (v : Fin 10 → ℤ) :
    squareDepth h p v = NumericalPrimeDepth.squareDepth h p v := by
  simp [squareDepth, hp.out]

def primeWeight (h : CoarseBounds F C) (p : ℕ) (v : Fin 10 → ℤ) : ℝ :=
  if 2 ≤ primeDepth h p v then (p : ℝ)^((primeDepth h p v : ℝ)/2-1) else 1

def squareWeight (h : CoarseBounds F C) (p : ℕ) (v : Fin 10 → ℤ) : ℝ :=
  if 2 ≤ squareDepth h p v then (p : ℝ)^((squareDepth h p v : ℝ)-2) else 1

/-- Manuscript K for d = a b²; its arithmetic estimates below explicitly
require that a and b are coprime and squarefree. -/
def K (h : CoarseBounds F C) (a b : ℕ) (v : Fin 10 → ℤ) : ℝ :=
  (∏ p ∈ a.primeFactors, primeWeight h p v) *
    (∏ p ∈ b.primeFactors, squareWeight h p v)

theorem K_eq_filtered_products (h : CoarseBounds F C) (a b : ℕ)
    (v : Fin 10 → ℤ) :
    K h a b v =
      (∏ p ∈ a.primeFactors with 2 ≤ primeDepth h p v,
        (p : ℝ)^((primeDepth h p v : ℝ)/2-1)) *
      (∏ p ∈ b.primeFactors with 2 ≤ squareDepth h p v,
        (p : ℝ)^((squareDepth h p v : ℝ)-2)) := by
  simp only [K, primeWeight, squareWeight, Finset.prod_filter]

theorem one_le_primeWeight (h : CoarseBounds F C) (p : ℕ) (v : Fin 10 → ℤ) :
    1 ≤ primeWeight h p v := by
  unfold primeWeight
  split_ifs with hd
  · have hp : p.Prime := by
      by_contra hp
      simp [primeDepth, hp] at hd
    have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_lt.le
    have hdR : (2 : ℝ) ≤ primeDepth h p v := by exact_mod_cast hd
    exact Real.one_le_rpow hp1 (by linarith)
  · exact le_rfl

theorem one_le_squareWeight (h : CoarseBounds F C) (p : ℕ) (v : Fin 10 → ℤ) :
    1 ≤ squareWeight h p v := by
  unfold squareWeight
  split_ifs with hd
  · have hp : p.Prime := by
      by_contra hp
      simp [squareDepth, hp] at hd
    have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_lt.le
    have hdR : (2 : ℝ) ≤ squareDepth h p v := by exact_mod_cast hd
    exact Real.one_le_rpow hp1 (by linarith)
  · exact le_rfl

theorem one_le_K (h : CoarseBounds F C) (a b : ℕ) (v : Fin 10 → ℤ) :
    1 ≤ K h a b v := by
  have hp : 1 ≤ ∏ p ∈ a.primeFactors, primeWeight h p v := by
    simpa using Finset.prod_le_prod (fun p (_ : p ∈ a.primeFactors) => (zero_le_one : (0:ℝ) ≤ 1))
      (fun p (_ : p ∈ a.primeFactors) => one_le_primeWeight h p v)
  have hs : 1 ≤ ∏ p ∈ b.primeFactors, squareWeight h p v := by
    simpa using Finset.prod_le_prod (fun p (_ : p ∈ b.primeFactors) => (zero_le_one : (0:ℝ) ≤ 1))
      (fun p (_ : p ∈ b.primeFactors) => one_le_squareWeight h p v)
  exact le_trans (by norm_num : (1:ℝ) ≤ 1*1)
    (mul_le_mul hp hs zero_le_one (zero_le_one.trans hp))

theorem K_pos (h : CoarseBounds F C) (a b : ℕ) (v : Fin 10 → ℤ) :
    0 < K h a b v := zero_lt_one.trans_le (one_le_K h a b v)

private theorem prime_local_bound (h : CoarseBounds F C) (p : ℕ)
    [hp : Fact p.Prime] (v : Fin 10 → ℤ) :
    ‖completeCubicSum F p v‖ ≤
      (C * (p : ℝ)^((11 : ℝ)/2) *
        (if 1 ≤ primeDepth h p v then (p : ℝ) else 1)) * primeWeight h p v := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.out.pos
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.out.one_lt.le
  have hC : 0 ≤ C := zero_le_one.trans h.constant_pos
  have hb := NumericalPrimeDepth.prime_bound h p v
  rw [← primeDepth_of_prime h p v] at hb
  by_cases hd : 2 ≤ primeDepth h p v
  · have hd1 : 1 ≤ primeDepth h p v := by omega
    have he : (11+(primeDepth h p v : ℝ))/2 =
        (11 : ℝ)/2 + 1 + ((primeDepth h p v : ℝ)/2-1) := by ring
    rw [he, Real.rpow_add hp0, Real.rpow_add hp0, Real.rpow_one] at hb
    simpa only [primeWeight, if_pos hd, if_pos hd1, mul_assoc] using hb
  · by_cases hd1 : 1 ≤ primeDepth h p v
    · have he : primeDepth h p v = 1 := by omega
      have hpow : (p : ℝ)^((11+(primeDepth h p v : ℝ))/2) ≤
          (p : ℝ)^((11 : ℝ)/2+1) :=
        Real.rpow_le_rpow_of_exponent_le hp1 (by simp only [he, Nat.cast_one]; norm_num)
      have hbound := hb.trans (mul_le_mul_of_nonneg_left hpow hC)
      simpa only [primeWeight, if_neg hd, if_pos hd1, Real.rpow_add hp0,
        Real.rpow_one, mul_one, mul_assoc] using hbound
    · have he : primeDepth h p v = 0 := by omega
      rw [primeWeight, if_neg hd, if_neg hd1, mul_one, mul_one]
      simpa only [he, Nat.cast_zero, add_zero] using hb

private theorem square_local_bound (h : CoarseBounds F C) (p : ℕ)
    [hp : Fact p.Prime] (v : Fin 10 → ℤ) :
    ‖completeCubicSum F (p^2) v‖ ≤
      (C * (p : ℝ)^11 *
        (if 1 ≤ squareDepth h p v then (p : ℝ)^2 else 1)) * squareWeight h p v := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.out.pos
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.out.one_lt.le
  have hC : 0 ≤ C := zero_le_one.trans h.constant_pos
  have hb := NumericalPrimeDepth.square_bound h p v
  rw [← squareDepth_of_prime h p v] at hb
  have hb' : ‖completeCubicSum F (p^2) v‖ ≤
      C * (p : ℝ)^(11+(squareDepth h p v : ℝ)) := by
    rw [← Real.rpow_natCast] at hb
    simpa only [Nat.cast_add, Nat.cast_ofNat] using hb
  by_cases hd : 2 ≤ squareDepth h p v
  · have hd1 : 1 ≤ squareDepth h p v := by omega
    have he : 11+(squareDepth h p v : ℝ) =
        (11 : ℝ) + 2 + ((squareDepth h p v : ℝ)-2) := by ring
    rw [he, Real.rpow_add hp0, Real.rpow_add hp0] at hb'
    simpa only [squareWeight, if_pos hd, if_pos hd1, Real.rpow_natCast, Real.rpow_ofNat,
      mul_assoc] using hb'
  · by_cases hd1 : 1 ≤ squareDepth h p v
    · have he : squareDepth h p v = 1 := by omega
      have hpow : (p : ℝ)^(11+(squareDepth h p v : ℝ)) ≤
          (p : ℝ)^((11 : ℝ)+2) :=
        Real.rpow_le_rpow_of_exponent_le hp1 (by simp only [he, Nat.cast_one]; norm_num)
      have hbound := hb'.trans (mul_le_mul_of_nonneg_left hpow hC)
      simpa only [squareWeight, if_neg hd, if_pos hd1, Real.rpow_add hp0,
        Real.rpow_natCast, Real.rpow_ofNat, mul_one, mul_assoc] using hbound
    · have he : squareDepth h p v = 0 := by omega
      rw [squareWeight, if_neg hd, if_neg hd1, mul_one, mul_one]
      simpa only [he, Nat.cast_zero, add_zero, Real.rpow_ofNat] using hb'

private theorem exceptional_product_le_gcd (a Δ : ℕ) (ha : a ≠ 0)
    (E : ℕ → Prop) [DecidablePred E]
    (hE : ∀ p ∈ a.primeFactors, E p → p ∣ Δ) :
    (∏ p ∈ a.primeFactors, if E p then (p : ℝ) else 1) ≤ (a.gcd Δ : ℝ) := by
  have hg : a.gcd Δ ≠ 0 := (Nat.gcd_pos_of_pos_left Δ (Nat.pos_of_ne_zero ha)).ne'
  have hsub : a.primeFactors.filter E ⊆ (a.gcd Δ).primeFactors := by
    intro p hp
    obtain ⟨hp,he⟩ := Finset.mem_filter.mp hp
    exact (Nat.prime_of_mem_primeFactors hp).mem_primeFactors
      (Nat.dvd_gcd (Nat.dvd_of_mem_primeFactors hp) (hE p hp he)) hg
  have hd : (∏ p ∈ a.primeFactors.filter E, p) ∣ a.gcd Δ :=
    (Finset.prod_dvd_prod_of_subset _ _ (fun p : ℕ => p) hsub).trans
      (Nat.prod_primeFactors_dvd (a.gcd Δ))
  have hle := Nat.le_of_dvd (Nat.pos_of_ne_zero hg) hd
  rw [← Finset.prod_filter]
  rw [← Nat.cast_prod]
  exact_mod_cast hle

private theorem prime_product_bound (h : CoarseBounds F C) (a : ℕ)
    (ha : Squarefree a) (v : Fin 10 → ℤ) (Δ : ℕ)
    (hΔ : ∀ (p : ℕ) [Fact p.Prime],
      1 ≤ NumericalPrimeDepth.primeDepth h p v → p ∣ Δ) :
    (∏ p ∈ a.primeFactors, ‖completeCubicSum F p v‖) ≤
      (C^a.primeFactors.card * (a : ℝ)^((11 : ℝ)/2) * (a.gcd Δ : ℝ)) *
        (∏ p ∈ a.primeFactors, primeWeight h p v) := by
  have hlocal : ∀ p ∈ a.primeFactors, ‖completeCubicSum F p v‖ ≤
      (C * (p : ℝ)^((11 : ℝ)/2) *
        (if 1 ≤ primeDepth h p v then (p : ℝ) else 1)) * primeWeight h p v := by
    intro p hp
    letI : Fact p.Prime := ⟨Nat.prime_of_mem_primeFactors hp⟩
    exact prime_local_bound h p v
  have hprod := Finset.prod_le_prod (fun p _ => norm_nonneg (completeCubicSum F p v)) hlocal
  have hbase : (∏ p ∈ a.primeFactors, (p : ℝ)^((11 : ℝ)/2)) =
      (a : ℝ)^((11 : ℝ)/2) := by
    rw [Real.finset_prod_rpow _ _ (fun p _ => Nat.cast_nonneg p)]
    congr 1
    rw [← Nat.cast_prod, Nat.prod_primeFactors_of_squarefree ha]
  have hexc : (∏ p ∈ a.primeFactors,
      if 1 ≤ primeDepth h p v then (p : ℝ) else 1) ≤ (a.gcd Δ : ℝ) := by
    apply exceptional_product_le_gcd a Δ ha.ne_zero
    intro p hp he
    letI : Fact p.Prime := ⟨Nat.prime_of_mem_primeFactors hp⟩
    exact hΔ p (by simpa using he)
  simp only [Finset.prod_mul_distrib, Finset.prod_const, hbase] at hprod
  have hC : 0 ≤ C := zero_le_one.trans h.constant_pos
  have hw : 0 ≤ ∏ p ∈ a.primeFactors, primeWeight h p v :=
    Finset.prod_nonneg (fun p _ => zero_le_one.trans (one_le_primeWeight h p v))
  apply hprod.trans
  gcongr

private theorem square_product_bound (h : CoarseBounds F C) (b : ℕ)
    (hb : Squarefree b) (v : Fin 10 → ℤ) (Θ : ℕ)
    (hΘ : ∀ (p : ℕ) [Fact p.Prime],
      1 ≤ NumericalPrimeDepth.squareDepth h p v → p ∣ Θ) :
    (∏ p ∈ b.primeFactors, ‖completeCubicSum F (p^2) v‖) ≤
      (C^b.primeFactors.card * (b : ℝ)^11 * (b.gcd Θ : ℝ)^2) *
        (∏ p ∈ b.primeFactors, squareWeight h p v) := by
  have hlocal : ∀ p ∈ b.primeFactors, ‖completeCubicSum F (p^2) v‖ ≤
      (C * (p : ℝ)^11 *
        (if 1 ≤ squareDepth h p v then (p : ℝ)^2 else 1)) * squareWeight h p v := by
    intro p hp
    letI : Fact p.Prime := ⟨Nat.prime_of_mem_primeFactors hp⟩
    exact square_local_bound h p v
  have hprod := Finset.prod_le_prod (fun p _ => norm_nonneg (completeCubicSum F (p^2) v)) hlocal
  have hbase : (∏ p ∈ b.primeFactors, (p : ℝ)^11) = (b : ℝ)^11 := by
    rw [Finset.prod_pow]
    congr 1
    rw [← Nat.cast_prod, Nat.prod_primeFactors_of_squarefree hb]
  have hexc : (∏ p ∈ b.primeFactors,
      if 1 ≤ squareDepth h p v then (p : ℝ) else 1) ≤ (b.gcd Θ : ℝ) := by
    apply exceptional_product_le_gcd b Θ hb.ne_zero
    intro p hp he
    letI : Fact p.Prime := ⟨Nat.prime_of_mem_primeFactors hp⟩
    exact hΘ p (by simpa using he)
  have hsquare : (∏ p ∈ b.primeFactors,
      if 1 ≤ squareDepth h p v then (p : ℝ)^2 else 1) =
      (∏ p ∈ b.primeFactors, if 1 ≤ squareDepth h p v then (p : ℝ) else 1)^2 := by
    rw [← Finset.prod_pow]
    apply Finset.prod_congr rfl
    intro p _
    split_ifs <;> simp
  simp only [Finset.prod_mul_distrib, Finset.prod_const, hbase, hsquare] at hprod
  have hC : 0 ≤ C := zero_le_one.trans h.constant_pos
  have hw : 0 ≤ ∏ p ∈ b.primeFactors, squareWeight h p v :=
    Finset.prod_nonneg (fun p _ => zero_le_one.trans (one_le_squareWeight h p v))
  apply hprod.trans
  gcongr

/-- Actual complete sums divided by manuscript K are majorized by two finite
gcds. The only frequency-specific premises are positive-depth divisibility. -/
theorem norm_div_K_le_gcd (h : CoarseBounds F C) (hF : F.IsHomogeneous 3)
    (a b : ℕ) (ha : Squarefree a) (hb : Squarefree b) (hab : a.Coprime b)
    (v : Fin 10 → ℤ) (Δ Θ : ℕ)
    (hΔ : ∀ (p : ℕ) [Fact p.Prime],
      1 ≤ NumericalPrimeDepth.primeDepth h p v → p ∣ Δ)
    (hΘ : ∀ (p : ℕ) [Fact p.Prime],
      1 ≤ NumericalPrimeDepth.squareDepth h p v → p ∣ Θ) :
    ‖completeCubicSum F (a*b^2) v‖ / K h a b v ≤
      C^(a.primeFactors.card+b.primeFactors.card) *
        (a : ℝ)^((11 : ℝ)/2) * (b : ℝ)^11 *
        (a.gcd Δ : ℝ) * (b.gcd Θ : ℝ)^2 := by
  apply (div_le_iff₀ (K_pos h a b v)).mpr
  rw [CompleteSumMultiplicativity.norm_squarefree_pair_product F hF a b ha hb hab v]
  have hp := prime_product_bound h a ha v Δ hΔ
  have hs := square_product_bound h b hb v Θ hΘ
  calc
    _ ≤ ((C^a.primeFactors.card * (a : ℝ)^((11 : ℝ)/2) * (a.gcd Δ : ℝ)) *
        (∏ p ∈ a.primeFactors, primeWeight h p v)) *
        ((C^b.primeFactors.card * (b : ℝ)^11 * (b.gcd Θ : ℝ)^2) *
        (∏ p ∈ b.primeFactors, squareWeight h p v)) := by
      exact mul_le_mul hp hs (Finset.prod_nonneg fun p _ => norm_nonneg _)
        ((Finset.prod_nonneg fun p _ => norm_nonneg _).trans hp)
    _ = _ := by rw [K, pow_add]; ring

end CubicTenVariables.NumericalConductor
