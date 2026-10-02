import CubicTenVariables.GcdWeightedPowerSum
import CubicTenVariables.GcdReciprocalSquareSum

/-! The elementary global modulus sum needed by the fixed-frequency
conductor estimate. Summing the linear part first leaves a reciprocal-square
sum in the square part. No dyadic decomposition or logarithmic loss is used. -/

set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.GcdProductWindowSum
open scoped BigOperators

private theorem scale (Y b : ℝ) (hY : 0 ≤ Y) (hb : 0 < b) :
    (Y/b^2)^((13 : ℝ)/2)*b^11 = Y^((13 : ℝ)/2)/b^2 := by
  have he : (b^2)^((13 : ℝ)/2) = b^13 := by
    rw [← Real.rpow_natCast_mul hb.le]
    norm_num
  rw [Real.div_rpow hY (by positivity),he]
  field_simp

/-- Uniformly over all finite positive pair families with a*b²≤2D.
Squarefreeness and coprimality are not needed for this arithmetic majorant. -/
theorem exists_bound : ∃ C : ℝ, 1 ≤ C ∧ ∀ D : ℝ, 1 ≤ D →
    ∀ Δ Θ : ℕ, 1 ≤ Δ → 1 ≤ Θ → ∀ Q : Finset (ℕ × ℕ),
      (∀ x ∈ Q, 1 ≤ x.1 ∧ 1 ≤ x.2 ∧ (x.1 : ℝ)*(x.2 : ℝ)^2 ≤ 2*D) →
      (∑ x ∈ Q, ((x.1 : ℝ)^((11 : ℝ)/2)*(Nat.gcd x.1 Δ : ℝ))*
        ((x.2 : ℝ)^11*(Nat.gcd x.2 Θ : ℝ)^2)) ≤
          C*D^((13 : ℝ)/2)*(Δ.divisors.card : ℝ)*(Θ.divisors.card : ℝ) := by
  classical
  obtain ⟨R,hR,hrecip⟩ := GcdReciprocalSquareSum.exists_bound
  refine ⟨(2 : ℝ)^13*R,?_,?_⟩
  · norm_num
    linarith
  intro D hD Δ Θ hΔ hΘ Q hQ
  let U := Q.image Prod.fst
  let V := Q.image Prod.snd
  let f : ℕ → ℝ := fun a => (a : ℝ)^((11 : ℝ)/2)*(Nat.gcd a Δ : ℝ)
  let g : ℕ → ℝ := fun b => (b : ℝ)^11*(Nat.gcd b Θ : ℝ)^2
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
      simpa only [one_mul] using mul_le_mul_of_nonneg_right ha (sq_nonneg (x.2 : ℝ))
    exact hm.trans h.2.2
  have hsub : Q ⊆ W := by
    intro x hx
    exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
      ⟨Finset.mem_image_of_mem _ hx,Finset.mem_image_of_mem _ hx⟩,(hQ x hx).2.2⟩
  have hf (a : ℕ) : 0 ≤ f a := by dsimp [f]; positivity
  have hg (b : ℕ) : 0 ≤ g b := by dsimp [g]; positivity
  have hinner (b : ℕ) (hb : b ∈ V) :
      (∑ a ∈ Aset b, f a)*g b ≤
        (2 : ℝ)^((13 : ℝ)/2)*(2*D)^((13 : ℝ)/2)*(Δ.divisors.card : ℝ)*
          ((Nat.gcd b Θ : ℝ)^2/(b : ℝ)^2) := by
    have hb1 : (1 : ℝ) ≤ b := by exact_mod_cast (hV b hb).1
    have hb0 : 0 < (b : ℝ) := by linarith
    have hX : 1 ≤ 2*D/(b : ℝ)^2 := by
      apply (le_div_iff₀ (sq_pos_of_pos hb0)).mpr
      simpa using (hV b hb).2
    have hsum := GcdWeightedPowerSum.prime_sum_le (2*D/(b : ℝ)^2) hX Δ hΔ
      (Aset b) (by
        intro a ha
        obtain ⟨haU,haD⟩ := Finset.mem_filter.mp ha
        refine ⟨by have h := hU a haU; omega,?_⟩
        have haX : (a : ℝ) ≤ 2*D/(b : ℝ)^2 :=
          (le_div_iff₀ (sq_pos_of_pos hb0)).mpr haD
        linarith)
    calc
      _ ≤ ((2 : ℝ)^((13 : ℝ)/2)*(2*D/(b : ℝ)^2)^((13 : ℝ)/2)*
          (Δ.divisors.card : ℝ))*g b := mul_le_mul_of_nonneg_right hsum (hg b)
      _ = (2 : ℝ)^((13 : ℝ)/2)*(Δ.divisors.card : ℝ)*
          ((2*D/(b : ℝ)^2)^((13 : ℝ)/2)*(b : ℝ)^11)*(Nat.gcd b Θ : ℝ)^2 := by
        dsimp [g]
        ring
      _ = (2 : ℝ)^((13 : ℝ)/2)*(Δ.divisors.card : ℝ)*
          ((2*D)^((13 : ℝ)/2)/(b : ℝ)^2)*(Nat.gcd b Θ : ℝ)^2 := by
        rw [scale (2*D) (b : ℝ) (by linarith) hb0]
      _ = _ := by ring
  have he : (2 : ℝ)^((13 : ℝ)/2)*(2*D)^((13 : ℝ)/2) =
      (2 : ℝ)^13*D^((13 : ℝ)/2) := by
    rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (by linarith : 0 ≤ D)]
    rw [← mul_assoc,← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    norm_num
  calc
    _ = ∑ x ∈ Q, f x.1*g x.2 := rfl
    _ ≤ ∑ x ∈ W, f x.1*g x.2 := Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun x _ _ => mul_nonneg (hf x.1) (hg x.2))
    _ = ∑ b ∈ V, (∑ a ∈ Aset b, f a)*g b := by
      dsimp [W,Aset]
      rw [Finset.sum_filter,Finset.sum_product,Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro b _
      rw [Finset.sum_mul,Finset.sum_filter]
    _ ≤ ∑ b ∈ V, (2 : ℝ)^((13 : ℝ)/2)*(2*D)^((13 : ℝ)/2)*
        (Δ.divisors.card : ℝ)*((Nat.gcd b Θ : ℝ)^2/(b : ℝ)^2) :=
      Finset.sum_le_sum hinner
    _ = ((2 : ℝ)^((13 : ℝ)/2)*(2*D)^((13 : ℝ)/2)*(Δ.divisors.card : ℝ))*
        ∑ b ∈ V, (Nat.gcd b Θ : ℝ)^2/(b : ℝ)^2 := (Finset.mul_sum ..).symm
    _ ≤ ((2 : ℝ)^((13 : ℝ)/2)*(2*D)^((13 : ℝ)/2)*(Δ.divisors.card : ℝ))*
        (R*(Θ.divisors.card : ℝ)) := mul_le_mul_of_nonneg_left
      (hrecip Θ hΘ V (fun b hb => (hV b hb).1)) (by positivity)
    _ = ((2 : ℝ)^13*R)*D^((13 : ℝ)/2)*(Δ.divisors.card : ℝ)*(Θ.divisors.card : ℝ) := by
      rw [he]
      ring

end CubicTenVariables.GcdProductWindowSum
