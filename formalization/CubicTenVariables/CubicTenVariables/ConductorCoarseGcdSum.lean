import CubicTenVariables.GcdWeightedPowerSum
import CubicTenVariables.PositiveReciprocalSum

/-! An elementary coarse modulus sum. Summing the linear modulus first
leaves a harmonic sum in the square modulus; an arbitrary positive power
absorbs it. No squarefreeness or coprimality assumption is needed. -/

set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.ConductorCoarseGcdSum
open scoped BigOperators

private theorem scale (Y b : ℝ) (hb : 0 < b) :
    (Y / b^2)^9 * b^17 = Y^9 * b⁻¹ := by
  field_simp

/-- Uniform over every finite positive pair family with `a*b² ≤ 2D`.
The constant precedes the exceptional integer and every summation parameter. -/
theorem exists_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ M : ℝ, 1 ≤ M ∧ ∀ D : ℝ, 1 ≤ D → ∀ c : ℕ, 1 ≤ c →
      ∀ Q : Finset (ℕ × ℕ),
        (∀ x ∈ Q, 1 ≤ x.1 ∧ 1 ≤ x.2 ∧
          (x.1 : ℝ)*(x.2 : ℝ)^2 ≤ 2*D) →
        (∑ x ∈ Q, (x.1 : ℝ)^8*(x.2 : ℝ)^17*(Nat.gcd x.1 c : ℝ)) ≤
          M*D^(9+ε)*(c.divisors.card : ℝ) := by
  classical
  obtain ⟨R,hR,hrecip⟩ := PositiveReciprocalSum.exists_uniform_inverse_bound ε hε
  let M : ℝ := (2 : ℝ)^18 * R * (2 : ℝ)^ε
  refine ⟨max 1 M, le_max_left _ _, ?_⟩
  intro D hD c hc Q hQ
  let U := Q.image Prod.fst
  let V := Q.image Prod.snd
  let f : ℕ → ℝ := fun a => (a : ℝ)^8*(Nat.gcd a c : ℝ)
  let g : ℕ → ℝ := fun b => (b : ℝ)^17
  let W := (U ×ˢ V).filter (fun x => (x.1 : ℝ)*(x.2 : ℝ)^2 ≤ 2*D)
  let Aset (b : ℕ) := U.filter (fun a : ℕ => (a : ℝ)*(b : ℝ)^2 ≤ 2*D)
  have hU (a : ℕ) (ha : a ∈ U) : 1 ≤ a := by
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp ha
    exact (hQ x hx).1
  have hV (b : ℕ) (hb : b ∈ V) : 1 ≤ b ∧ (b : ℝ)^2 ≤ 2*D := by
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hb
    have h := hQ x hx
    have ha : (1 : ℝ) ≤ x.1 := by exact_mod_cast h.1
    refine ⟨h.2.1,?_⟩
    have hm : (x.2 : ℝ)^2 ≤ (x.1 : ℝ)*(x.2 : ℝ)^2 := by
      simpa only [one_mul] using
        mul_le_mul_of_nonneg_right ha (sq_nonneg (x.2 : ℝ))
    exact hm.trans h.2.2
  have hsub : Q ⊆ W := by
    intro x hx
    exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
      ⟨Finset.mem_image_of_mem _ hx,Finset.mem_image_of_mem _ hx⟩,(hQ x hx).2.2⟩
  have hf (a : ℕ) : 0 ≤ f a := by dsimp [f]; positivity
  have hg (b : ℕ) : 0 ≤ g b := by dsimp [g]; positivity
  have hinner (b : ℕ) (hb : b ∈ V) :
      (∑ a ∈ Aset b, f a)*g b ≤
        (2 : ℝ)^9*(2*D)^9*(c.divisors.card : ℝ)*(b : ℝ)⁻¹ := by
    have hb1 : (1 : ℝ) ≤ b := by exact_mod_cast (hV b hb).1
    have hb0 : 0 < (b : ℝ) := by linarith
    have hX : 1 ≤ 2*D/(b : ℝ)^2 := by
      apply (le_div_iff₀ (sq_pos_of_pos hb0)).mpr
      simpa using (hV b hb).2
    have hsum := GcdWeightedPowerSum.sum_le 8 (2*D/(b : ℝ)^2)
      (by norm_num) hX c 1 hc (by norm_num) (Aset b) (by
        intro a ha
        obtain ⟨haU,haD⟩ := Finset.mem_filter.mp ha
        refine ⟨by have h := hU a haU; omega,?_⟩
        have haX : (a : ℝ) ≤ 2*D/(b : ℝ)^2 :=
          (le_div_iff₀ (sq_pos_of_pos hb0)).mpr haD
        linarith)
    norm_num only [Nat.cast_one, pow_one, show (8 : ℝ)+1 = 9 by norm_num,
      Real.rpow_ofNat] at hsum
    have hsum' : (∑ a ∈ Aset b, f a) ≤
        (2 : ℝ)^9*(2*D/(b : ℝ)^2)^9*(c.divisors.card : ℝ) := by
      simpa only [f, show (2 : ℝ)^9 = 512 by norm_num] using hsum
    calc
      _ ≤ ((2 : ℝ)^9*(2*D/(b : ℝ)^2)^9*(c.divisors.card : ℝ))*g b :=
        mul_le_mul_of_nonneg_right hsum' (hg b)
      _ = (2 : ℝ)^9*(c.divisors.card : ℝ)*
          ((2*D/(b : ℝ)^2)^9*(b : ℝ)^17) := by dsimp [g]; ring
      _ = _ := by rw [scale (2*D) (b : ℝ) hb0]; ring
  have hh : (∑ b ∈ V, (b : ℝ)⁻¹) ≤ R*(2*D)^ε :=
    hrecip (2*D) (by linarith) V
      (fun b hb => by have h := (hV b hb).1; omega)
      (fun b hb => by
        have hb1 : (1 : ℝ) ≤ b := by exact_mod_cast (hV b hb).1
        have hb2 := (hV b hb).2
        nlinarith)
  have he : (2 : ℝ)^9*(2*D)^9*(c.divisors.card : ℝ)*(R*(2*D)^ε) =
      M*D^(9+ε)*(c.divisors.card : ℝ) := by
    rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (by linarith : 0 ≤ D),
      Real.rpow_add (by linarith : 0 < D), Real.rpow_ofNat]
    dsimp [M]
    ring
  calc
    _ = ∑ x ∈ Q, f x.1*g x.2 := by apply Finset.sum_congr rfl; intro x _; dsimp [f,g]; ring
    _ ≤ ∑ x ∈ W, f x.1*g x.2 := Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun x _ _ => mul_nonneg (hf x.1) (hg x.2))
    _ = ∑ b ∈ V, (∑ a ∈ Aset b, f a)*g b := by
      dsimp [W,Aset]
      rw [Finset.sum_filter,Finset.sum_product,Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro b _
      rw [Finset.sum_mul,Finset.sum_filter]
    _ ≤ ∑ b ∈ V, (2 : ℝ)^9*(2*D)^9*(c.divisors.card : ℝ)*(b : ℝ)⁻¹ :=
      Finset.sum_le_sum hinner
    _ = ((2 : ℝ)^9*(2*D)^9*(c.divisors.card : ℝ))*
        ∑ b ∈ V, (b : ℝ)⁻¹ := (Finset.mul_sum ..).symm
    _ ≤ ((2 : ℝ)^9*(2*D)^9*(c.divisors.card : ℝ))*(R*(2*D)^ε) :=
      mul_le_mul_of_nonneg_left hh (by positivity)
    _ = M*D^(9+ε)*(c.divisors.card : ℝ) := he
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_right 1 M) (by positivity))
      (Nat.cast_nonneg _)

end CubicTenVariables.ConductorCoarseGcdSum
