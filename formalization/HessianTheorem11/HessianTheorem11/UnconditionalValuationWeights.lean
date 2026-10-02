import HessianTheorem11.UnconditionalValuationSpecialLinear
import HessianTheorem11.UnconditionalOrderedWeights
import Mathlib.Algebra.Order.Group.Units
import Mathlib.Algebra.Group.TypeTags.Hom

/-! Ordered valuation weights and the actual weak/strict residue support test.
Integral coefficients surviving modulo the maximal ideal are units, so they
do not alter the valuation of any diagonal character. -/
noncomputable section
namespace HessianTheorem11.UnconditionalValuationWeights
open Finset
variable {K : Type*} [Field K] (V : ValuationSubring K)

abbrev WeightGroup := Additive V.ValueGroupˣ

def additiveValuation : Additive Kˣ →+ WeightGroup V :=
  ((invMonoidHom : V.ValueGroupˣ →* V.ValueGroupˣ).comp
    (Units.map V.valuation.toMonoidHom)).toAdditive

def weight (x : Kˣ) : WeightGroup V := additiveValuation V (Additive.ofMul x)

@[simp] theorem weight_one : weight V (1 : Kˣ) = 0 :=
  (additiveValuation V).map_zero

@[simp] theorem weight_mul (x y : Kˣ) : weight V (x*y) = weight V x + weight V y :=
  (additiveValuation V).map_add _ _

@[simp] theorem weight_zpow (x : Kˣ) (k : ℤ) : weight V (x^k) = k • weight V x :=
  (additiveValuation V).map_zsmul _ _

theorem weight_prod {ι : Type*} (s : Finset ι) (x : ι → Kˣ) :
    weight V (∏ i ∈ s, x i) = ∑ i ∈ s, weight V (x i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => simp [Finset.prod_insert,Finset.sum_insert,hi,ih]

theorem weight_character {n : ℕ} (x : Fin n → Kˣ) (a : Fin n → ℤ) :
    weight V (∏ i, x i ^ a i) =
      UnconditionalOrderedWeights.value a (fun i => weight V (x i)) := by
  rw [weight_prod]
  simp only [weight_zpow,UnconditionalOrderedWeights.value]

theorem sum_weight_eq_zero {n : ℕ} (x : Fin n → Kˣ) (hx : ∏ i, x i = 1) :
    ∑ i, weight V (x i) = 0 := by
  rw [←weight_prod,hx,weight_one]

theorem nonneg_weight_iff (x : Kˣ) : 0 ≤ weight V x ↔ (x : K) ∈ V := by
  change (1 : V.ValueGroupˣ) ≤ (Units.map V.valuation.toMonoidHom x)⁻¹ ↔ _
  rw [one_le_inv']
  change V.valuation (x : K) ≤ 1 ↔ _
  exact V.valuation_le_one_iff _

theorem positive_weight_iff (x : Kˣ) : 0 < weight V x ↔ V.valuation (x : K) < 1 := by
  change (1 : V.ValueGroupˣ) < (Units.map V.valuation.toMonoidHom x)⁻¹ ↔ _
  rw [one_lt_inv']
  rfl

/-- A coefficient surviving in the residue field does not affect whether
its product with a diagonal character is integral. -/
theorem nonneg_weight_of_integral_product (c : V)
    (hc : c ∉ IsLocalRing.maximalIdeal V) (x : Kˣ)
    (hcx : (c : K) * (x : K) ∈ V) : 0 ≤ weight V x := by
  apply (nonneg_weight_iff V x).mpr
  apply V.mem_of_valuation_le_one
  have hu : IsUnit c := (IsLocalRing.notMem_maximalIdeal).mp hc
  have hv := (V.valuation_le_one_iff _).mpr hcx
  simpa only [map_mul,(V.valuation_eq_one_iff c).mp hu,one_mul] using hv

/-- Strict reduction to zero makes the diagonal character strictly positive,
provided the unscaled integral coefficient survives in the residue field. -/
theorem positive_weight_of_maximal_product (c z : V)
    (hc : c ∉ IsLocalRing.maximalIdeal V) (hz : z ∈ IsLocalRing.maximalIdeal V)
    (x : Kˣ) (he : (z : K) = (c : K) * (x : K)) : 0 < weight V x := by
  apply (positive_weight_iff V x).mpr
  have hu : IsUnit c := (IsLocalRing.notMem_maximalIdeal).mp hc
  have hv := (V.valuation_lt_one_iff z).mp hz
  rw [he,map_mul,(V.valuation_eq_one_iff c).mp hu,one_mul] at hv
  exact hv

theorem character_nonnegative {n : ℕ} (x : Fin n → Kˣ) (a : Fin n → ℤ)
    (c : V) (hc : c ∉ IsLocalRing.maximalIdeal V)
    (hcx : (c : K) * ((∏ i, x i ^ a i : Kˣ) : K) ∈ V) :
    0 ≤ UnconditionalOrderedWeights.value a (fun i => weight V (x i)) := by
  rw [←weight_character]
  exact nonneg_weight_of_integral_product V c hc _ hcx

theorem character_positive {n : ℕ} (x : Fin n → Kˣ) (a : Fin n → ℤ)
    (c z : V) (hc : c ∉ IsLocalRing.maximalIdeal V)
    (hz : z ∈ IsLocalRing.maximalIdeal V)
    (he : (z : K) = (c : K) * ((∏ i, x i ^ a i : Kˣ) : K)) :
    0 < UnconditionalOrderedWeights.value a (fun i => weight V (x i)) := by
  rw [←weight_character]
  exact positive_weight_of_maximal_product V c z hc hz _ he

/-- An exact determinant-one tuple of field entries gives sum-zero valuation
weights without any assumption on the value group. -/
theorem sum_weight_mk0_eq_zero {n : ℕ} (d : Fin n → K)
    (hd : ∀ i, d i ≠ 0) (hprod : ∏ i, d i = 1) :
    ∑ i, weight V (Units.mk0 (d i) (hd i)) = 0 := by
  apply sum_weight_eq_zero
  apply Units.ext
  simpa using hprod

/-- Finite weak/strict residue support conditions give an actual integral
SL weight. The coefficients and their scaled values are elements of V. -/
theorem exists_integral_support_weight {n : ℕ} (x : Fin n → Kˣ)
    (hx : ∏ i, x i = 1) (S T : Finset (Fin n → ℤ))
    (hS : ∀ a ∈ S, ∃ c : V, c ∉ IsLocalRing.maximalIdeal V ∧
      (c : K) * ((∏ i, x i ^ a i : Kˣ) : K) ∈ V)
    (hT : ∀ a ∈ T, ∃ c z : V, c ∉ IsLocalRing.maximalIdeal V ∧
      z ∈ IsLocalRing.maximalIdeal V ∧
      (z : K) = (c : K) * ((∏ i, x i ^ a i : Kˣ) : K)) :
    ∃ w : Fin n → ℤ, (∑ i, w i = 0) ∧
      (∀ a ∈ S, 0 ≤ ∑ i, a i * w i) ∧
      (∀ a ∈ T, 0 < ∑ i, a i * w i) := by
  apply UnconditionalOrderedWeights.exists_integral_weight
    (fun i => weight V (x i)) (sum_weight_eq_zero V x hx) S T
  · intro a ha
    obtain ⟨c,hc,hcx⟩ := hS a ha
    exact character_nonnegative V x a c hc hcx
  · intro a ha
    obtain ⟨c,z,hc,hz,he⟩ := hT a ha
    exact character_positive V x a c z hc hz he

end HessianTheorem11.UnconditionalValuationWeights
