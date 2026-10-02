import CubicTenVariables.GaussianBoxEnvelope

/-! Full Gaussian average of the actual modular Hessian kernels. -/

noncomputable section
namespace CubicTenVariables.GaussianHessianKernelAverage
open MvPolynomial HessianTheorem11 GoodHessianKernelAverage GaussianBoxEnvelope
open scoped BigOperators

/-- One constant precedes the positive modulus and every positive Gaussian
scale. The sum runs over all integer vectors, including the origin, with
no truncation, logarithmic loss or unproved literature premise. -/
theorem exists_uniform_bound
    (F : MvPolynomial (Fin 10) ℤ) (hF : F.IsHomogeneous 3)
    (hA : Anisotropic (map (Int.castRingHom ℚ) F)) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (m : ℕ), 0 < m → ∀ (L : ℝ), 0 < L →
      Summable (fun h : Fin 10 → ℤ =>
        Real.sqrt (kernelCard F m h : ℝ) * Real.exp (-(∑ i, (h i : ℝ)^2)/L^2)) ∧
      (∑' h : Fin 10 → ℤ,
        Real.sqrt (kernelCard F m h : ℝ) * Real.exp (-(∑ i, (h i : ℝ)^2)/L^2)) ≤
          C*((m:ℝ)+L^3)^5 := by
  obtain ⟨A,hA1,hbox⟩ := GoodHessianKernelAverage.exists_real_box_bound F hF hA
  let B : ℝ := 32*A*(∑' k : ℕ, shellWeight k)
  have hA0 : 0 ≤ A := zero_le_one.trans hA1
  have hB : 0 ≤ B := mul_nonneg (by positivity) (tsum_nonneg shellWeight_nonneg)
  refine ⟨1+B, by linarith, ?_⟩
  intro m hm L hL
  have hm1 : (1:ℝ) ≤ m := by exact_mod_cast hm
  have hg := summable_and_tsum_le
    (fun h : Fin 10 → ℤ => Real.sqrt (kernelCard F m h : ℝ))
    (fun _ => Real.sqrt_nonneg _) A m L hA0 hm1 hL (hbox m hm)
  constructor
  · simpa only [gaussian, energy] using hg.1
  · have hb : (∑' h : Fin 10 → ℤ,
        Real.sqrt (kernelCard F m h : ℝ) * Real.exp (-(∑ i, (h i : ℝ)^2)/L^2)) ≤
        B*((m:ℝ)+L^3)^5 := by
      simpa only [gaussian, energy, B] using hg.2
    exact hb.trans (mul_le_mul_of_nonneg_right (by linarith : B ≤ 1+B) (by positivity))

end CubicTenVariables.GaussianHessianKernelAverage
