import CubicTenVariables.OnionGaussianMajorant
import CubicTenVariables.GaussianOnionEnvelope
import CubicTenVariables.OnionExponentAssembly

/-! The full ten-variable L1 onion bound and its actual complete-sum
consequence. The proof uses all-width Gaussian summation and no unproved
literature premise. -/

noncomputable section
namespace CubicTenVariables.SquarefullOnion
open MvPolynomial HessianTheorem11 SquarefullWeightedSums WeightedHessianRootCRT
open WeightedGaussianPoisson
open scoped BigOperators
attribute [local instance] Classical.propDecidable

/-- The full source L1 estimate, uniformly over all positive moduli and
all translated real boxes. No split at c=R or Gaussian truncation is used. -/
theorem exists_weightedL1_bound (F : MvPolynomial (Fin 10) ℤ)
    (hF : F.IsHomogeneous 3) (hA : Anisotropic (map (Int.castRingHom ℚ) F))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ (c d : ℕ) [NeZero c] [NeZero d],
      Squarefree d → d ∣ c →
      ∀ (V : Finset (Fin 10 → ℤ)) (u : Fin 10 → ℝ) (R : ℝ),
      1 ≤ R → (∀ v ∈ V, ∀ i, |(v i : ℝ)-u i| ≤ R) →
      weightedL1 F c d V (fun _ => 1) ≤
        K*((c^2*d : ℕ) : ℝ)^(6+ε)*(d : ℝ)^((1:ℝ)/2)*
          (SquarefreeResidueFactors.d2 c d : ℝ)^((1:ℝ)/2)*
            (R+((c^2*d : ℕ) : ℝ)^((1:ℝ)/3))^10 := by
  obtain ⟨C,hC,hfreq⟩ := GaussianOnionEnvelope.exists_uniform_bound F hF hA ε hε
  let K : ℝ := 32*Real.exp 10*Real.pi^5*C
  have hC0 : 0 ≤ C := zero_le_one.trans hC
  have hK : 1 ≤ K := by
    have hexp : 1 ≤ Real.exp (10:ℝ) := Real.one_le_exp_iff.mpr (by norm_num)
    have hpi : 1 ≤ Real.pi^5 := one_le_pow₀ (by linarith [Real.two_le_pi])
    have ht : 1 ≤ Real.exp (10:ℝ)*Real.pi^5*C :=
      one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hexp hpi) hC
    dsimp [K]
    nlinarith
  refine ⟨K,hK,?_⟩
  intro c d _ _ hd hdc V u R hR hbox
  have hc0 : 0 < (c : ℝ) := by exact_mod_cast NeZero.pos c
  have hd0 : 0 < (d : ℝ) := by exact_mod_cast NeZero.pos d
  have hc1 : (1:ℝ) ≤ c := by exact_mod_cast NeZero.pos c
  have hd1 : (1:ℝ) ≤ d := by exact_mod_cast NeZero.pos d
  have hr0 : 0 < ((c^2*d : ℕ) : ℝ) := by
    simpa only [Nat.cast_mul, Nat.cast_pow] using mul_pos (pow_pos hc0 2) hd0
  let W : ℝ := R+((c^2*d : ℕ) : ℝ)^((1:ℝ)/3)
  obtain ⟨hW,hRW,hrW⟩ := OnionExponentAssembly.enlarged_width
    ((c^2*d : ℕ) : ℝ) R hr0 (zero_le_one.trans hR)
  change 0 < W at hW
  change R ≤ W at hRW
  have hrW' : (c : ℝ)^2*d ≤ W^3 := by exact_mod_cast hrW
  let r : ℕ := SquarefreeResidueFactors.d1 c d
  have hrc : r ∣ c := OnionModuli.d1_dvd_c c d (NeZero.pos c) hd hdc
  let B : ℝ := C*(c : ℝ)^5*(d : ℝ)^((11:ℝ)/2+ε)*
    (SquarefreeResidueFactors.d2 c d : ℝ)^((1:ℝ)/2)*
      ((c : ℝ)/d+((c : ℝ)/W)^3)^5
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hscalar (a : Fin c) :
      (if Nat.Coprime a.val c then
        ∑' h : Fin 10 → ℤ, dualGaussian (c : ℝ) W h *
          ‖partialRootCharacterMass F c d r hdc hrc (-(a.val : ℤ) : ZMod c) h‖
      else 0) ≤ B := by
    by_cases ha : Nat.Coprime a.val c
    · rw [if_pos ha]
      have hb := (hfreq c d hd hdc W hW (-(ZMod.unitOfCoprime a.val ha))).2
      have hcast : ((c/d : ℕ) : ℝ) = (c : ℝ)/d := Nat.cast_div hdc hd0.ne'
      simpa only [Units.val_neg, ZMod.coe_unitOfCoprime, Int.cast_neg,
        Int.cast_natCast, hcast, B, r] using hb
    · simpa only [if_neg ha] using hB
  have hsum :
      (∑ a : Fin c, if Nat.Coprime a.val c then
        ∑' h : Fin 10 → ℤ, dualGaussian (c : ℝ) W h *
          ‖partialRootCharacterMass F c d r hdc hrc (-(a.val : ℤ) : ZMod c) h‖
      else 0) ≤ (c : ℝ)*B := by
    calc
      _ ≤ ∑ _a : Fin c, B := Finset.sum_le_sum (fun a _ => hscalar a)
      _ = _ := by simp
  calc
    _ ≤ (c : ℝ)^11*(d : ℝ)^6*Real.exp 10*(Real.sqrt Real.pi*W/(c : ℝ))^10 *
        ∑ a : Fin c, if Nat.Coprime a.val c then
          ∑' h : Fin 10 → ℤ, dualGaussian (c : ℝ) W h *
            ‖partialRootCharacterMass F c d r hdc hrc (-(a.val : ℤ) : ZMod c) h‖
        else 0 := OnionGaussianMajorant.weightedL1_le_fourier F c d r hdc hrc
          W R hW (zero_le_one.trans hR) hRW u V hbox
    _ ≤ (c : ℝ)^11*(d : ℝ)^6*Real.exp 10*(Real.sqrt Real.pi*W/(c : ℝ))^10 *
        ((c : ℝ)*B) := mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = (c : ℝ)^11*(d : ℝ)^6*Real.exp 10*(Real.sqrt Real.pi*W/(c : ℝ))^10 *
        (c : ℝ)*B := by ring
    _ ≤ K*((c : ℝ)^2*d)^(6+ε)*(d : ℝ)^((1:ℝ)/2)*
        (SquarefreeResidueFactors.d2 c d : ℝ)^((1:ℝ)/2)*W^10 :=
      OnionExponentAssembly.gaussian_factor_le c d (SquarefreeResidueFactors.d2 c d)
        W ε C hc1 hd1 (by positivity) hW hε.le hC0 hrW'
    _ = _ := by simp only [W, Nat.cast_mul, Nat.cast_pow]

/-- The required L1 branch of nosquash, for the literal complete cubic sums. -/
theorem exists_complete_sum_bound (F : MvPolynomial (Fin 10) ℤ)
    (hF : F.IsHomogeneous 3) (hA : Anisotropic (map (Int.castRingHom ℚ) F))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ (c d : ℕ) [NeZero c] [NeZero d],
      Squarefree d → d ∣ c →
      ∀ (V : Finset (Fin 10 → ℤ)) (u : Fin 10 → ℝ) (R : ℝ),
      1 ≤ R → (∀ v ∈ V, ∀ i, |(v i : ℝ)-u i| ≤ R) →
      (∑ v ∈ V, ‖completeCubicSum F (c^2*d) v‖) ≤
        K*((c^2*d : ℕ) : ℝ)^(6+ε)*(d : ℝ)^((1:ℝ)/2)*
          (SquarefreeResidueFactors.d2 c d : ℝ)^((1:ℝ)/2)*
            (R+((c^2*d : ℕ) : ℝ)^((1:ℝ)/3))^10 := by
  obtain ⟨K,hK,hbound⟩ := exists_weightedL1_bound F hF hA ε hε
  refine ⟨K,hK,?_⟩
  intro c d _ _ hd hdc V u R hR hbox
  have hl := SquarefullWeightedLifting.weighted_norm_sum_le_weightedL1
    F hF c d hdc V (fun _ => 1) (by intros; norm_num)
  simpa only [one_mul] using hl.trans (hbound c d hd hdc V u R hR hbox)

end CubicTenVariables.SquarefullOnion
