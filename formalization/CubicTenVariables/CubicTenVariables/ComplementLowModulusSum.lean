import CubicTenVariables.ConductorCoarseGcdSum
import CubicTenVariables.PrimeConstantEpsilonBound
import CubicTenVariables.PolynomialHeightDivisorBound

/-! Low-factor sums for the complementary conductor estimate. For any
nonnegative ordinary exponent β, the square exponent 2β+1 leaves a harmonic
sum. The specialized exponents are β=(9+r)/2 and 2β+1=10+r. -/

set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.ComplementLowModulusSum
open scoped BigOperators

private theorem scale (β Y b : ℝ) (hY : 0 ≤ Y) (hb : 0 < b) :
    (Y/b^2)^(β+1)*b^(2*β+1) = Y^(β+1)*b⁻¹ := by
  rw [Real.div_rpow hY (sq_nonneg b),← Real.rpow_natCast_mul hb.le]
  norm_num only [Nat.cast_ofNat]
  calc
    _ = Y^(β+1)*(b^(2*β+1)/b^(2*(β+1))) := by ring
    _ = Y^(β+1)*b^((2*β+1)-2*(β+1)) := by rw [Real.rpow_sub hb]
    _ = _ := by rw [show (2*β+1)-2*(β+1) = -1 by ring,Real.rpow_neg_one]

/-- General borderline low-factor sum; no squarefreeness or coprimality
hypothesis is needed. The constant precedes all summation data. -/
theorem exists_gcd_bound (β : ℝ) (hβ : 0 ≤ β) (ε : ℝ) (hε : 0 < ε) :
    ∃ M : ℝ, 1 ≤ M ∧ ∀ D : ℝ, 1 ≤ D → ∀ Δ : ℕ, 1 ≤ Δ →
      ∀ Q : Finset (ℕ × ℕ),
        (∀ x ∈ Q, 1 ≤ x.1 ∧ 1 ≤ x.2 ∧
          (x.1 : ℝ)*(x.2 : ℝ)^2 ≤ 2*D) →
        (∑ x ∈ Q, (x.1 : ℝ)^β*(x.2 : ℝ)^(2*β+1)*(Nat.gcd x.1 Δ : ℝ)) ≤
          M*D^(β+1+ε)*(Δ.divisors.card : ℝ) := by
  classical
  obtain ⟨R,hR,hrecip⟩ := PositiveReciprocalSum.exists_uniform_inverse_bound ε hε
  let M : ℝ := (2 : ℝ)^(β+1)*(2 : ℝ)^(β+1)*R*(2 : ℝ)^ε
  refine ⟨max 1 M,le_max_left _ _,?_⟩
  intro D hD Δ hΔ Q hQ
  let U := Q.image Prod.fst
  let V := Q.image Prod.snd
  let f : ℕ → ℝ := fun a => (a : ℝ)^β*(Nat.gcd a Δ : ℝ)
  let g : ℕ → ℝ := fun b => (b : ℝ)^(2*β+1)
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
        (2 : ℝ)^(β+1)*(2*D)^(β+1)*(Δ.divisors.card : ℝ)*(b : ℝ)⁻¹ := by
    have hb1 : (1 : ℝ) ≤ b := by exact_mod_cast (hV b hb).1
    have hb0 : 0 < (b : ℝ) := by linarith
    have hX : 1 ≤ 2*D/(b : ℝ)^2 := by
      apply (le_div_iff₀ (sq_pos_of_pos hb0)).mpr
      simpa using (hV b hb).2
    have hsum := GcdWeightedPowerSum.sum_le β (2*D/(b : ℝ)^2)
      hβ hX Δ 1 hΔ (by norm_num) (Aset b) (by
        intro a ha
        obtain ⟨haU,haD⟩ := Finset.mem_filter.mp ha
        refine ⟨by have h := hU a haU; omega,?_⟩
        have haX : (a : ℝ) ≤ 2*D/(b : ℝ)^2 :=
          (le_div_iff₀ (sq_pos_of_pos hb0)).mpr haD
        linarith)
    simp only [Nat.cast_one,pow_one] at hsum
    calc
      _ ≤ ((2 : ℝ)^(β+1)*(2*D/(b : ℝ)^2)^(β+1)*(Δ.divisors.card : ℝ))*g b :=
        mul_le_mul_of_nonneg_right hsum (hg b)
      _ = (2 : ℝ)^(β+1)*(Δ.divisors.card : ℝ)*
          ((2*D/(b : ℝ)^2)^(β+1)*(b : ℝ)^(2*β+1)) := by dsimp [g]; ring
      _ = _ := by rw [scale β (2*D) (b : ℝ) (by linarith) hb0]; ring
  have hh : (∑ b ∈ V, (b : ℝ)⁻¹) ≤ R*(2*D)^ε :=
    hrecip (2*D) (by linarith) V
      (fun b hb => by have h := (hV b hb).1; omega)
      (fun b hb => by
        have hb1 : (1 : ℝ) ≤ b := by exact_mod_cast (hV b hb).1
        have hb2 := (hV b hb).2
        nlinarith)
  have he : (2 : ℝ)^(β+1)*(2*D)^(β+1)*(Δ.divisors.card : ℝ)*(R*(2*D)^ε) =
      M*D^(β+1+ε)*(Δ.divisors.card : ℝ) := by
    rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (by linarith : 0 ≤ D),
      Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (by linarith : 0 ≤ D),
      Real.rpow_add (by linarith : 0 < D) (β+1) ε]
    dsimp [M]
    ring
  calc
    _ = ∑ x ∈ Q, f x.1*g x.2 := by
      apply Finset.sum_congr rfl
      intro x _
      dsimp [f,g]
      ring
    _ ≤ ∑ x ∈ W, f x.1*g x.2 := Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun x _ _ => mul_nonneg (hf x.1) (hg x.2))
    _ = ∑ b ∈ V, (∑ a ∈ Aset b, f a)*g b := by
      dsimp [W,Aset]
      rw [Finset.sum_filter,Finset.sum_product,Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro b _
      rw [Finset.sum_mul,Finset.sum_filter]
    _ ≤ ∑ b ∈ V, (2 : ℝ)^(β+1)*(2*D)^(β+1)*(Δ.divisors.card : ℝ)*(b : ℝ)⁻¹ :=
      Finset.sum_le_sum hinner
    _ = ((2 : ℝ)^(β+1)*(2*D)^(β+1)*(Δ.divisors.card : ℝ))*
        ∑ b ∈ V, (b : ℝ)⁻¹ := (Finset.mul_sum ..).symm
    _ ≤ ((2 : ℝ)^(β+1)*(2*D)^(β+1)*(Δ.divisors.card : ℝ))*(R*(2*D)^ε) :=
      mul_le_mul_of_nonneg_left hh (by positivity)
    _ = M*D^(β+1+ε)*(Δ.divisors.card : ℝ) := he
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_right 1 M) (by positivity)) (Nat.cast_nonneg _)

/-- Prime-factor weights and a polynomial-height exceptional integer are
absorbed uniformly; the underlying arithmetic family remains unrestricted. -/
theorem exists_weighted_bound (β : ℝ) (hβ : 0 ≤ β)
    (C : ℝ) (hC : 1 ≤ C) (d : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ M : ℝ, 1 ≤ M ∧ ∀ D H : ℝ, 1 ≤ D → 1 ≤ H →
      ∀ Δ : ℕ, 1 ≤ Δ → (Δ : ℝ) ≤ C*H^d → ∀ Q : Finset (ℕ × ℕ),
        (∀ x ∈ Q, 1 ≤ x.1 ∧ 1 ≤ x.2 ∧
          (x.1 : ℝ)*(x.2 : ℝ)^2 ≤ 2*D) →
        (∑ x ∈ Q, C^(x.1.primeFactors.card+x.2.primeFactors.card)*
          (x.1 : ℝ)^β*(x.2 : ℝ)^(2*β+1)*(Nat.gcd x.1 Δ : ℝ)) ≤
          M*(D*H)^ε*D^(β+1) := by
  obtain ⟨A,hA,hprime⟩ := PrimeConstantEpsilonBound.exists_two_factor_bound
    C hC (ε/2) (by linarith)
  obtain ⟨R,hR,hsum⟩ := exists_gcd_bound β hβ (ε/2) (by linarith)
  obtain ⟨B,hB,hdiv⟩ := PolynomialHeightDivisorBound.exists_bound C hC d ε hε
  let M : ℝ := A*(2 : ℝ)^(ε/2)*R*B
  refine ⟨max 1 M,le_max_left _ _,?_⟩
  intro D H hD hH Δ hΔ hΔH Q hQ
  have hD0 : 0 < D := zero_lt_one.trans_le hD
  have hH0 : 0 < H := zero_lt_one.trans_le hH
  let g : ℕ × ℕ → ℝ := fun x =>
    (x.1 : ℝ)^β*(x.2 : ℝ)^(2*β+1)*(Nat.gcd x.1 Δ : ℝ)
  have hg (x : ℕ × ℕ) : 0 ≤ g x := by dsimp [g]; positivity
  have hweight (x : ℕ × ℕ) (hx : x ∈ Q) :
      C^(x.1.primeFactors.card+x.2.primeFactors.card) ≤ A*(2*D)^(ε/2) := by
    have hb1 : (1 : ℝ) ≤ x.2 := by exact_mod_cast (hQ x hx).2.1
    have hab : ((x.1*x.2 : ℕ) : ℝ) ≤ 2*D := by
      rw [Nat.cast_mul]
      have hbb : (x.2 : ℝ) ≤ (x.2 : ℝ)^2 := by nlinarith
      exact (mul_le_mul_of_nonneg_left hbb (Nat.cast_nonneg x.1)).trans (hQ x hx).2.2
    exact (hprime x.1 x.2 (hQ x hx).1 (hQ x hx).2.1).trans
      (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (Nat.cast_nonneg _) hab (by linarith)) (by linarith))
  have hdivΔ := hdiv H hH Δ hΔ hΔH
  have he : (A*(2*D)^(ε/2))*(R*D^(β+1+ε/2)*(B*H^ε)) =
      M*(D*H)^ε*D^(β+1) := by
    rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hD0.le,
      Real.mul_rpow hD0.le hH0.le,Real.rpow_add hD0]
    have hd : D^(ε/2)*D^(ε/2) = D^ε := by
      rw [← Real.rpow_add hD0]
      congr 1
      ring
    calc
      _ = (A*(2 : ℝ)^(ε/2)*R*B)*(D^(ε/2)*D^(ε/2))*H^ε*D^(β+1) := by ring
      _ = _ := by rw [hd]; dsimp [M]; ring
  calc
    _ = ∑ x ∈ Q, C^(x.1.primeFactors.card+x.2.primeFactors.card)*g x := by
      apply Finset.sum_congr rfl
      intro x _
      dsimp [g]
      ring
    _ ≤ ∑ x ∈ Q, (A*(2*D)^(ε/2))*g x :=
      Finset.sum_le_sum (fun x hx => mul_le_mul_of_nonneg_right (hweight x hx) (hg x))
    _ = (A*(2*D)^(ε/2))*∑ x ∈ Q, g x := (Finset.mul_sum ..).symm
    _ ≤ (A*(2*D)^(ε/2))*(R*D^(β+1+ε/2)*(Δ.divisors.card : ℝ)) :=
      mul_le_mul_of_nonneg_left (hsum D hD Δ hΔ Q hQ) (by positivity)
    _ ≤ (A*(2*D)^(ε/2))*(R*D^(β+1+ε/2)*(B*H^ε)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hdivΔ (by positivity)) (by positivity)
    _ = M*(D*H)^ε*D^(β+1) := he
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_right 1 M) (by positivity)) (by positivity)

/-- Literal complement-level exponents; valid for every natural level. -/
theorem exists_level_bound (r : ℕ) (C : ℝ) (hC : 1 ≤ C)
    (d : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ M : ℝ, 1 ≤ M ∧ ∀ D H : ℝ, 1 ≤ D → 1 ≤ H →
      ∀ Δ : ℕ, 1 ≤ Δ → (Δ : ℝ) ≤ C*H^d → ∀ Q : Finset (ℕ × ℕ),
        (∀ x ∈ Q, 1 ≤ x.1 ∧ 1 ≤ x.2 ∧
          (x.1 : ℝ)*(x.2 : ℝ)^2 ≤ 2*D) →
        (∑ x ∈ Q, C^(x.1.primeFactors.card+x.2.primeFactors.card)*
          (x.1 : ℝ)^((9+(r : ℝ))/2)*(x.2 : ℝ)^(10+(r : ℝ))*
          (Nat.gcd x.1 Δ : ℝ)) ≤
          M*(D*H)^ε*D^((11+(r : ℝ))/2) := by
  have h := exists_weighted_bound ((9+(r : ℝ))/2) (by positivity) C hC d ε hε
  simpa only [show 2*((9+(r : ℝ))/2)+1 = 10+(r : ℝ) by ring,
    show (9+(r : ℝ))/2+1 = (11+(r : ℝ))/2 by ring] using h

end CubicTenVariables.ComplementLowModulusSum
