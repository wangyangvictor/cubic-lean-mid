import CubicTenVariables.PolynomialResidueCRT
import CubicTenVariables.SmoothResidueIteration
import Mathlib.Data.Nat.Factorization.Induction

/-!
# Exact prime-power factorization of constrained polynomial root counts

The count is the cardinality of the actual root subtype with its canonical
residue map. Natural cardinality makes the definition independent of a
nonzero-modulus typeclass; the finite-filter adapter is literal whenever
the modulus is positive. No degree or geometric hypothesis is used.
-/

noncomputable section
namespace CubicTenVariables.PolynomialRootPrimeFactorization
open MvPolynomial
open scoped BigOperators

variable {n : ℕ}

/-- Actual polynomial roots modulo c in the integral class k modulo d. -/
def count (F : MvPolynomial (Fin n) ℤ) (k : Fin n → ℤ)
    (c d : ℕ) (hd : d ∣ c) : ℕ :=
  Nat.card {z : Fin n → ZMod c //
    eval₂ (Int.castRingHom (ZMod c)) z F = 0 ∧
      ∀ i, ZMod.castHom hd (ZMod d) (z i) = (k i : ZMod d)}

/-- The natural-cardinality definition is exactly the usual finite filter. -/
theorem count_eq_card (F : MvPolynomial (Fin n) ℤ) (k : Fin n → ℤ)
    (c d : ℕ) [NeZero c] (hd : d ∣ c) :
    count F k c d hd =
      (Finset.univ.filter fun z : Fin n → ZMod c =>
        eval₂ (Int.castRingHom (ZMod c)) z F = 0 ∧
          ∀ i, ZMod.castHom hd (ZMod d) (z i) = (k i : ZMod d)).card := by
  classical
  simp only [count, Nat.card_eq_fintype_card, Fintype.card_subtype]

/-- The unique vector modulo one satisfies both predicates. -/
@[simp] theorem count_one (F : MvPolynomial (Fin n) ℤ) (k : Fin n → ℤ) :
    count F k 1 1 (dvd_refl 1) = 1 := by
  rw [count_eq_card]
  have hz (z : Fin n → ZMod 1) :
      eval₂ (Int.castRingHom (ZMod 1)) z F = 0 ∧
        ∀ i, ZMod.castHom (dvd_refl 1) (ZMod 1) (z i) = (k i : ZMod 1) := by
    constructor
    · exact Subsingleton.elim _ _
    · intro i
      exact Subsingleton.elim _ _
  simp only [hz, implies_true, and_self, Finset.filter_true, Finset.card_univ, Fintype.card_fun,
    Fintype.card_fin, ZMod.card, one_pow]

/-- The count modulo a coprime product factors exactly. -/
theorem count_mul (F : MvPolynomial (Fin n) ℤ) (k : Fin n → ℤ)
    {c₁ c₂ d₁ d₂ : ℕ} [NeZero c₁] [NeZero c₂]
    (hc : c₁.Coprime c₂) (hd₁ : d₁ ∣ c₁) (hd₂ : d₂ ∣ c₂) :
    count F k (c₁*c₂) (d₁*d₂) (Nat.mul_dvd_mul hd₁ hd₂) =
      count F k c₁ d₁ hd₁ * count F k c₂ d₂ hd₂ := by
  rw [count_eq_card, count_eq_card, count_eq_card]
  exact PolynomialResidueCRT.card_zeros_in_residue_class_mul F k hc hd₁ hd₂

/-- Fixing d gives a multiplicative count with smaller modulus gcd(c,d). -/
theorem count_gcd_mul (F : MvPolynomial (Fin n) ℤ) (k : Fin n → ℤ)
    (d a b : ℕ) (hab : a.Coprime b) :
    count F k (a*b) ((a*b).gcd d) (Nat.gcd_dvd_left _ _) =
      count F k a (a.gcd d) (Nat.gcd_dvd_left _ _) *
        count F k b (b.gcd d) (Nat.gcd_dvd_left _ _) := by
  by_cases ha : a = 0
  · subst a
    have hb : b = 1 := by simpa [Nat.Coprime] using hab
    subst b
    simp
  by_cases hb : b = 0
  · subst b
    have ha' : a = 1 := by simpa [Nat.Coprime] using hab
    subst a
    simp
  letI : NeZero a := ⟨ha⟩
  letI : NeZero b := ⟨hb⟩
  simpa only [← hab.mul_gcd d] using
    count_mul F k hab (Nat.gcd_dvd_left a d) (Nat.gcd_dvd_left b d)

/-- Exact prime-power product for every positive constrained modulus. -/
theorem count_eq_prod_primeFactors (F : MvPolynomial (Fin n) ℤ) (k : Fin n → ℤ)
    (c d : ℕ) (hc : c ≠ 0) (hd : d ∣ c) :
    count F k c d hd =
      ∏ p ∈ c.primeFactors,
        count F k (p ^ c.factorization p) ((p ^ c.factorization p).gcd d)
          (Nat.gcd_dvd_left _ _) := by
  have h := Nat.multiplicative_factorization
    (fun a => count F k a (a.gcd d) (Nat.gcd_dvd_left _ _))
    (count_gcd_mul F k d) (by simp) hc
  simpa only [Nat.gcd_eq_right_iff_dvd.mpr hd,
    Nat.prod_factorization_eq_prod_primeFactors] using h

/-- Reduction to modulus one imposes no condition. -/
theorem count_residue_one (F : MvPolynomial (Fin n) ℤ) (k : Fin n → ℤ)
    (c : ℕ) [NeZero c] :
    count F k c 1 (one_dvd c) =
      (Finset.univ.filter fun z : Fin n → ZMod c =>
        eval₂ (Int.castRingHom (ZMod c)) z F = 0).card := by
  rw [count_eq_card]
  congr 1
  ext z
  have hz (i : Fin n) : ZMod.castHom (one_dvd c) (ZMod 1) (z i) = (k i : ZMod 1) :=
    Subsingleton.elim _ _
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨fun h => h.1, fun h => ⟨h, hz⟩⟩

/-- Prescribing the entire modulus gives one root when the center is a root. -/
theorem count_full_residue (F : MvPolynomial (Fin n) ℤ) (k : Fin n → ℤ)
    (c : ℕ) [NeZero c] (hk : (c : ℤ) ∣ eval k F) :
    count F k c c (dvd_refl c) = 1 := by
  classical
  rw [count_eq_card]
  have hmap : ZMod.castHom (dvd_refl c) (ZMod c) = RingHom.id (ZMod c) :=
    Subsingleton.elim _ _
  have hk' : eval₂ (Int.castRingHom (ZMod c)) (fun i => (k i : ZMod c)) F = 0 := by
    rw [← SmoothResidueLifting.cast_eval_int, ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact hk
  have hf : (Finset.univ.filter fun z : Fin n → ZMod c =>
      eval₂ (Int.castRingHom (ZMod c)) z F = 0 ∧
        ∀ i, ZMod.castHom (dvd_refl c) (ZMod c) (z i) = (k i : ZMod c)) =
      {fun i => (k i : ZMod c)} := by
    ext z
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton,
      hmap, RingHom.id_apply]
    constructor
    · exact fun hz => funext hz.2
    · rintro rfl
      exact ⟨hk', fun _ => rfl⟩
  rw [hf, Finset.card_singleton]

/-- The prime-residue count is exactly the existing lifting API's filter. -/
theorem count_prime_class (F : MvPolynomial (Fin n) ℤ) (k : Fin n → ℤ)
    (p : ℕ) [Fact p.Prime] (r : ℕ) (hr : 1 ≤ r) :
    count F k (p^r) p (dvd_pow_self p (by omega)) =
      (Finset.univ.filter fun z : Fin n → ZMod (p^r) =>
        (∀ i, SmoothResidueIteration.toPrime p r hr (z i) = (k i : ZMod p)) ∧
          eval₂ (Int.castRingHom (ZMod (p^r))) z F = 0).card := by
  rw [count_eq_card]
  have hmap : ZMod.castHom (dvd_pow_self p (by omega)) (ZMod p) =
      SmoothResidueIteration.toPrime p r hr := Subsingleton.elim _ _
  simp only [hmap, and_comm]

end CubicTenVariables.PolynomialRootPrimeFactorization
