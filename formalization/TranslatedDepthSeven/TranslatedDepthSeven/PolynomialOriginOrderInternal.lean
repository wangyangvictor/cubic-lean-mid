import TranslatedDepthSeven.TruncatedPolynomialJets
import Mathlib.RingTheory.MvPowerSeries.NoZeroDivisors

/-!
# Multiplicativity of order at the polynomial origin

The power-series order gives a short proof that two polynomial classes
of orders below `a` and `b` cannot have product zero modulo the
`(a+b)`-th power of the origin ideal.
-/

namespace TranslatedDepthSeven

noncomputable section

open MvPolynomial

set_option maxHeartbeats 1000000

theorem mem_originIdeal_pow_iff_order
    {K : Type*} [Field K] {σ : Type*}
    (f : MvPolynomial σ K) (a : ℕ) :
    f ∈ RingHom.ker (constantCoeff : MvPolynomial σ K →+* K) ^ a ↔
      (a : ℕ∞) ≤ (f : MvPowerSeries σ K).order := by
  rw [pow_ker_constantCoeff_eq_totalDegreeAtLeastIdeal,
    mem_totalDegreeAtLeastIdeal_iff]
  constructor
  · intro h
    apply MvPowerSeries.nat_le_order
    intro s hs
    rw [MvPolynomial.coeff_coe]
    by_contra hne
    exact (not_le_of_gt hs) (h s (MvPolynomial.mem_support_iff.mpr hne))
  · intro h s hs
    have hne : MvPowerSeries.coeff s (f : MvPowerSeries σ K) ≠ 0 := by
      simpa only [MvPolynomial.coeff_coe] using MvPolynomial.mem_support_iff.mp hs
    have hle := h.trans (MvPowerSeries.order_le hne)
    exact_mod_cast hle

theorem mul_notMem_originIdeal_pow_add
    {K : Type*} [Field K] {σ : Type*}
    (f g : MvPolynomial σ K) (a b : ℕ)
    (hf : f ∉ RingHom.ker (constantCoeff : MvPolynomial σ K →+* K) ^ a)
    (hg : g ∉ RingHom.ker (constantCoeff : MvPolynomial σ K →+* K) ^ b) :
    f * g ∉ RingHom.ker (constantCoeff : MvPolynomial σ K →+* K) ^ (a + b) := by
  rw [mem_originIdeal_pow_iff_order] at hf hg ⊢
  rw [MvPolynomial.coe_mul, MvPowerSeries.order_mul, Nat.cast_add]
  have hf' : (f : MvPowerSeries σ K).order < (a : ℕ∞) := lt_of_not_ge hf
  have hg' : (g : MvPowerSeries σ K).order < (b : ℕ∞) := lt_of_not_ge hg
  apply not_le_of_gt
  calc
    (f : MvPowerSeries σ K).order + (g : MvPowerSeries σ K).order ≤
        (f : MvPowerSeries σ K).order + (b : ℕ∞) := add_le_add le_rfl hg'.le
    _ < (a : ℕ∞) + (b : ℕ∞) :=
      (ENat.add_lt_add_iff_right (n := (f : MvPowerSeries σ K).order)
        (m := (a : ℕ∞)) (k := (b : ℕ∞)) (by simp)).mpr hf'

end

end TranslatedDepthSeven
