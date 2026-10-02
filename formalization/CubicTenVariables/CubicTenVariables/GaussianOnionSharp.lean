import CubicTenVariables.GaussianOnionEnvelope
import CubicTenVariables.OnionCharacterSharp

/-! Full Gaussian frequency envelope with the sharp restricted root mass. -/
set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.GaussianOnionSharp
open MvPolynomial HessianTheorem11 WeightedHessianRootCRT WeightedGaussianPoisson
open GaussianOnionEnvelope
open scoped BigOperators

/-- One constant controls the full nonnegative frequency sum, for every
positive width and all admissible c,d. No literature premise is used. -/
theorem exists_uniform_bound (F : MvPolynomial (Fin 10) ℤ)
    (hF : F.IsHomogeneous 3) (hA : Anisotropic (map (Int.castRingHom ℚ) F))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (c d : ℕ) [NeZero c] [NeZero d],
      ∀ (hd : Squarefree d) (hdc : d ∣ c) (W : ℝ), 0 < W → ∀ (a : (ZMod c)ˣ),
      Summable (fun h : Fin 10 → ℤ => dualGaussian (c : ℝ) W h *
        ‖partialRootCharacterMass F c d (SquarefreeResidueFactors.d1 c d) hdc
          (OnionModuli.d1_dvd_c c d (NeZero.pos c) hd hdc) (a : ZMod c) h‖) ∧
      (∑' h : Fin 10 → ℤ, dualGaussian (c : ℝ) W h *
        ‖partialRootCharacterMass F c d (SquarefreeResidueFactors.d1 c d) hdc
          (OnionModuli.d1_dvd_c c d (NeZero.pos c) hd hdc) (a : ZMod c) h‖) ≤
        C*(c : ℝ)^5*(d : ℝ)^(5+ε)*
          (SquarefreeResidueFactors.d2 c d : ℝ)*
            (((c/d : ℕ) : ℝ)+((c : ℝ)/W)^3)^5 := by
  obtain ⟨U,hU,hchar⟩ := OnionCharacterSharp.exists_uniform_bound F hF hA ε hε
  obtain ⟨V,hV,hgauss⟩ := GaussianHessianKernelAverage.exists_uniform_bound F hF hA
  have hU0 : 0 ≤ U := zero_le_one.trans hU
  have hV0 : 0 ≤ V := zero_le_one.trans hV
  refine ⟨U*V, by nlinarith [mul_le_mul_of_nonneg_left hV hU0], ?_⟩
  intro c d _ _ hd hdc W hW a
  have hc : 0 < (c : ℝ) := by exact_mod_cast NeZero.pos c
  have hquot : 0 < c/d := Nat.div_pos (Nat.le_of_dvd (NeZero.pos c) hdc) (NeZero.pos d)
  have hL : 0 < (c : ℝ)/W := div_pos hc hW
  let B : ℝ := U*(c : ℝ)^5*(d : ℝ)^(5+ε)*
    (SquarefreeResidueFactors.d2 c d : ℝ)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  let g (h : Fin 10 → ℤ) : ℝ :=
    Real.sqrt (GoodHessianKernelAverage.kernelCard F (c/d) h : ℝ) *
      GaussianBoxEnvelope.gaussian ((c : ℝ)/W) h
  have hg := hgauss (c/d) hquot ((c : ℝ)/W) hL
  change Summable g ∧ (∑' h, g h) ≤ V*(((c/d : ℕ) : ℝ)+((c : ℝ)/W)^3)^5 at hg
  have hdom (h : Fin 10 → ℤ) :
      dualGaussian (c : ℝ) W h *
        ‖partialRootCharacterMass F c d (SquarefreeResidueFactors.d1 c d) hdc
          (OnionModuli.d1_dvd_c c d (NeZero.pos c) hd hdc) (a : ZMod c) h‖ ≤ B*g h := by
    have hb := hchar c d hd hdc a h
    change ‖partialRootCharacterMass F c d (SquarefreeResidueFactors.d1 c d) hdc
      (OnionModuli.d1_dvd_c c d (NeZero.pos c) hd hdc) (a : ZMod c) h‖ ≤
        B*Real.sqrt (GoodHessianKernelAverage.kernelCard F (c/d) h : ℝ) at hb
    calc
      _ ≤ GaussianBoxEnvelope.gaussian ((c : ℝ)/W) h *
          (B*Real.sqrt (GoodHessianKernelAverage.kernelCard F (c/d) h : ℝ)) :=
        mul_le_mul (dualGaussian_le (c : ℝ) W hc hW h) hb (norm_nonneg _)
          (Real.exp_nonneg _)
      _ = _ := by dsimp [g]; ring
  have hsmajor : Summable (fun h => B*g h) := hg.1.mul_left B
  have hs := hsmajor.of_nonneg_of_le
    (fun h => mul_nonneg (Real.exp_nonneg _) (norm_nonneg _)) hdom
  refine ⟨hs, ?_⟩
  calc
    _ ≤ ∑' h, B*g h := Summable.tsum_le_tsum hdom hs hsmajor
    _ = B*(∑' h, g h) := tsum_mul_left
    _ ≤ B*(V*(((c/d : ℕ) : ℝ)+((c : ℝ)/W)^3)^5) :=
      mul_le_mul_of_nonneg_left hg.2 hB
    _ = _ := by dsimp [B]; ring

end CubicTenVariables.GaussianOnionSharp
