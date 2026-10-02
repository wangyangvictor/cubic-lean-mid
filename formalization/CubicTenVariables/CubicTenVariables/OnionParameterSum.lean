import CubicTenVariables.PositiveReciprocalSum
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

/-! A uniform weighted count of the positive parameters `a^3*b^5*e^2`. -/

noncomputable section
namespace CubicTenVariables.OnionParameterSum
open scoped BigOperators

private theorem sqrt_parameter_identity (X a b : ℝ) (hX : 0 ≤ X)
    (ha : 0 < a) (hb : 0 < b) :
    Real.sqrt (X / (a^3*b^5)) * a^((1:ℝ)/2) * b =
      Real.sqrt X * a⁻¹ * b^(-(3:ℝ)/2) := by
  have hsa : Real.sqrt a ≠ 0 := ne_of_gt (Real.sqrt_pos.2 ha)
  have hsb : Real.sqrt b ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hb)
  have ha3 : Real.sqrt (a^3) = a * Real.sqrt a := by
    rw [show a^3 = a^2*a by ring, Real.sqrt_mul (sq_nonneg a), Real.sqrt_sq ha.le]
  have hb5 : Real.sqrt (b^5) = b^2 * Real.sqrt b := by
    rw [show b^5 = (b^2)^2*b by ring, Real.sqrt_mul (sq_nonneg (b^2)),
      Real.sqrt_sq (sq_nonneg b)]
  have hbpow : b^(-(3:ℝ)/2) = (b*Real.sqrt b)⁻¹ := by
    rw [show -(3:ℝ)/2 = -(1+1/2) by norm_num,
      Real.rpow_neg hb.le, Real.rpow_add hb, Real.rpow_one, ← Real.sqrt_eq_rpow]
  rw [Real.sqrt_div hX, Real.sqrt_mul (by positivity : 0 ≤ a^3), ha3, hb5,
    ← Real.sqrt_eq_rpow, hbpow]
  field_simp

/-- A positive integer fiber under a quadratic cutoff has at most the
square root of that cutoff many elements. -/
theorem card_fiber_le (X : ℝ) (hX : 0 ≤ X) (a b : ℕ)
    (ha : 0 < a) (hb : 0 < b) (E : Finset ℕ)
    (hpos : ∀ e ∈ E, 0 < e)
    (hcut : ∀ e ∈ E, ((a^3*b^5*e^2 : ℕ) : ℝ) ≤ X) :
    (E.card : ℝ) ≤ Real.sqrt (X / ((a:ℝ)^3*(b:ℝ)^5)) := by
  have hab : 0 < (a:ℝ)^3*(b:ℝ)^5 := by positivity
  have hsub : E ⊆ Finset.Icc 1 ⌊Real.sqrt (X / ((a:ℝ)^3*(b:ℝ)^5))⌋₊ := by
    intro e he
    refine Finset.mem_Icc.2 ⟨hpos e he, Nat.le_floor ?_⟩
    apply (Real.le_sqrt (Nat.cast_nonneg e) (div_nonneg hX hab.le)).2
    apply (le_div_iff₀ hab).2
    have hh := hcut e he
    push_cast at hh
    nlinarith [hh]
  have hc := Finset.card_le_card hsub
  rw [Nat.card_Icc] at hc
  simp only [Nat.add_sub_cancel] at hc
  exact (by exact_mod_cast hc : (E.card:ℝ) ≤
    (⌊Real.sqrt (X / ((a:ℝ)^3*(b:ℝ)^5))⌋₊:ℝ)).trans
    (Nat.floor_le (Real.sqrt_nonneg _))

/-- The weight on one `(a,b)` fiber cancels the square root of its
cubic/quintic coefficient to a reciprocal and a three-halves power. -/
theorem weighted_fiber_le (X : ℝ) (hX : 0 ≤ X) (a b : ℕ)
    (ha : 0 < a) (hb : 0 < b) (E : Finset ℕ)
    (hpos : ∀ e ∈ E, 0 < e)
    (hcut : ∀ e ∈ E, ((a^3*b^5*e^2 : ℕ) : ℝ) ≤ X) :
    (E.card:ℝ) * (a:ℝ)^((1:ℝ)/2) * (b:ℝ) ≤
      Real.sqrt X * (a:ℝ)⁻¹ * (b:ℝ)^(-(3:ℝ)/2) := by
  calc
    _ ≤ Real.sqrt (X / ((a:ℝ)^3*(b:ℝ)^5)) * (a:ℝ)^((1:ℝ)/2) * (b:ℝ) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (card_fiber_le X hX a b ha hb E hpos hcut)
          (Real.rpow_nonneg (Nat.cast_nonneg a) _)) (Nat.cast_nonneg b)
    _ = _ := sqrt_parameter_identity X a b hX (by exact_mod_cast ha) (by exact_mod_cast hb)

private theorem sum_fixed_pair_le (X : ℝ) (hX : 0 ≤ X)
    (T : Finset (ℕ × ℕ × ℕ))
    (hpos : ∀ t ∈ T, 0 < t.1 ∧ 0 < t.2.1 ∧ 0 < t.2.2)
    (hcut : ∀ t ∈ T, ((t.1^3*t.2.1^5*t.2.2^2:ℕ):ℝ) ≤ X)
    (a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    (∑ t ∈ T with (t.1,t.2.1) = (a,b),
      (t.1:ℝ)^((1:ℝ)/2)*(t.2.1:ℝ)) ≤
      Real.sqrt X * (a:ℝ)⁻¹ * (b:ℝ)^(-(3:ℝ)/2) := by
  let S := T.filter (fun t => (t.1,t.2.1) = (a,b))
  let E := S.image (fun t => t.2.2)
  have hcoords : ∀ t ∈ S, t.1 = a ∧ t.2.1 = b := by
    intro t ht
    simpa only [Prod.mk.injEq] using (Finset.mem_filter.1 ht).2
  have hcard : E.card = S.card := by
    apply Finset.card_image_iff.2
    intro t ht u hu he
    exact Prod.ext ((hcoords t ht).1.trans (hcoords u hu).1.symm)
      (Prod.ext ((hcoords t ht).2.trans (hcoords u hu).2.symm) he)
  have hEpos : ∀ e ∈ E, 0 < e := by
    intro e he
    obtain ⟨t,ht,rfl⟩ := Finset.mem_image.1 he
    exact (hpos t (Finset.mem_filter.1 ht).1).2.2
  have hEcut : ∀ e ∈ E, ((a^3*b^5*e^2:ℕ):ℝ) ≤ X := by
    intro e he
    obtain ⟨t,ht,rfl⟩ := Finset.mem_image.1 he
    simpa only [(hcoords t ht).1, (hcoords t ht).2] using
      hcut t (Finset.mem_filter.1 ht).1
  calc
    _ = ∑ _t ∈ S, (a:ℝ)^((1:ℝ)/2)*(b:ℝ) := by
      apply Finset.sum_congr rfl
      intro t ht
      rw [(hcoords t ht).1, (hcoords t ht).2]
    _ = (E.card:ℝ)*(a:ℝ)^((1:ℝ)/2)*(b:ℝ) := by
      rw [Finset.sum_const, nsmul_eq_mul, hcard]
      ring
    _ ≤ _ := weighted_fiber_le X hX a b ha hb E hEpos hEcut

/-- Summation over distinct triples reduces to two independent finite
reciprocal sums; no rectangular-shape assumption on the triples is used. -/
theorem sum_le_separated (X : ℝ) (hX : 0 ≤ X)
    (T : Finset (ℕ × ℕ × ℕ))
    (hpos : ∀ t ∈ T, 0 < t.1 ∧ 0 < t.2.1 ∧ 0 < t.2.2)
    (hcut : ∀ t ∈ T, ((t.1^3*t.2.1^5*t.2.2^2:ℕ):ℝ) ≤ X) :
    (∑ t ∈ T, (t.1:ℝ)^((1:ℝ)/2)*(t.2.1:ℝ)) ≤
      Real.sqrt X * (∑ a ∈ T.image Prod.fst, (a:ℝ)⁻¹) *
        (∑ b ∈ (T.image (fun t => t.2.1) : Finset ℕ), (b:ℝ)^(-(3:ℝ)/2)) := by
  let A := T.image Prod.fst
  let B := T.image (fun t => t.2.1)
  have hmaps : ∀ t ∈ T, (t.1,t.2.1) ∈ A ×ˢ B := by
    intro t ht
    exact Finset.mem_product.2 ⟨Finset.mem_image_of_mem _ ht, Finset.mem_image_of_mem _ ht⟩
  calc
    _ = ∑ ab ∈ A ×ˢ B, ∑ t ∈ T with (t.1,t.2.1) = ab,
        (t.1:ℝ)^((1:ℝ)/2)*(t.2.1:ℝ) :=
      (Finset.sum_fiberwise_of_maps_to hmaps _).symm
    _ ≤ ∑ ab ∈ A ×ˢ B, Real.sqrt X * (ab.1:ℝ)⁻¹ *
        (ab.2:ℝ)^(-(3:ℝ)/2) := by
      apply Finset.sum_le_sum
      intro ab hab
      obtain ⟨haA,hbB⟩ := Finset.mem_product.1 hab
      obtain ⟨t,ht,ha⟩ := Finset.mem_image.1 haA
      obtain ⟨u,hu,hb⟩ := Finset.mem_image.1 hbB
      apply sum_fixed_pair_le X hX T hpos hcut
      · simpa only [← ha] using (hpos t ht).1
      · simpa only [← hb] using (hpos u hu).2.1
    _ = _ := by
      rw [Finset.sum_product, mul_assoc, Finset.sum_mul_sum]
      simp only [A, B, Finset.mul_sum, mul_assoc]

private theorem first_le_cutoff (t : ℕ × ℕ × ℕ)
    (hpos : 0 < t.1 ∧ 0 < t.2.1 ∧ 0 < t.2.2) :
    (t.1:ℝ) ≤ ((t.1^3*t.2.1^5*t.2.2^2:ℕ):ℝ) := by
  have ha : (1:ℝ) ≤ (t.1:ℝ) := by exact_mod_cast hpos.1
  have hb : (1:ℝ) ≤ (t.2.1:ℝ) := by exact_mod_cast hpos.2.1
  have he : (1:ℝ) ≤ (t.2.2:ℝ) := by exact_mod_cast hpos.2.2
  push_cast
  calc
    (t.1:ℝ) ≤ (t.1:ℝ)^3 := le_self_pow₀ ha (by norm_num)
    _ ≤ (t.1:ℝ)^3*(t.2.1:ℝ)^5 := le_mul_of_one_le_right (by positivity) (one_le_pow₀ hb)
    _ ≤ _ := le_mul_of_one_le_right (by positivity) (one_le_pow₀ he)

/-- One constant, chosen before the cutoff and the finite set, bounds
the weighted positive triples with `a^3*b^5*e^2 ≤ X`. -/
theorem exists_uniform_bound (δ : ℝ) (hδ : 0 < δ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ X : ℝ, 1 ≤ X → ∀ T : Finset (ℕ × ℕ × ℕ),
      (∀ t ∈ T, 0 < t.1 ∧ 0 < t.2.1 ∧ 0 < t.2.2) →
      (∀ t ∈ T, ((t.1^3*t.2.1^5*t.2.2^2:ℕ):ℝ) ≤ X) →
      (∑ t ∈ T, (t.1:ℝ)^((1:ℝ)/2)*(t.2.1:ℝ)) ≤ C*X^((1:ℝ)/2+δ) := by
  obtain ⟨C₁,hC₁,hrecip⟩ := PositiveReciprocalSum.exists_uniform_inverse_bound δ hδ
  obtain ⟨C₂,hC₂,hthree⟩ := PositiveReciprocalSum.exists_uniform_three_halves_bound
  refine ⟨C₁*C₂, one_le_mul_of_one_le_of_one_le hC₁ hC₂, ?_⟩
  intro X hX T hpos hcut
  let A := T.image Prod.fst
  let B := T.image (fun t => t.2.1)
  have hApos : ∀ a ∈ A, 0 < a := by
    intro a ha
    obtain ⟨t,ht,rfl⟩ := Finset.mem_image.1 ha
    exact (hpos t ht).1
  have hAX : ∀ a ∈ A, (a:ℝ) ≤ X := by
    intro a ha
    obtain ⟨t,ht,rfl⟩ := Finset.mem_image.1 ha
    exact (first_le_cutoff t (hpos t ht)).trans (hcut t ht)
  have hsumA := hrecip X hX A hApos hAX
  have hsumB := hthree B
  have hBnonneg : 0 ≤ ∑ b ∈ B, (b:ℝ)^(-(3:ℝ)/2) :=
    Finset.sum_nonneg (fun b _ => Real.rpow_nonneg (Nat.cast_nonneg b) _)
  calc
    _ ≤ Real.sqrt X * (∑ a ∈ A, (a:ℝ)⁻¹) *
        (∑ b ∈ B, (b:ℝ)^(-(3:ℝ)/2)) := sum_le_separated X (by positivity) T hpos hcut
    _ ≤ Real.sqrt X * (C₁*X^δ) * C₂ := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left hsumA (Real.sqrt_nonneg X)
      · exact hsumB
      · exact hBnonneg
      · positivity
    _ = _ := by
      rw [Real.sqrt_eq_rpow, Real.rpow_add (by positivity : 0 < X)]
      ring

end CubicTenVariables.OnionParameterSum
