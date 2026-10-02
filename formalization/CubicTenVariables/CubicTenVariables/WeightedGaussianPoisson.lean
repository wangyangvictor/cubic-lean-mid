import CubicTenVariables.GaussianLatticePoisson

/-! Finite weighted Gaussian Poisson summation, with the finite Fourier
sum kept inside the frequency sum. -/

noncomputable section
namespace CubicTenVariables.WeightedGaussianPoisson
open scoped BigOperators

def phase {n : ℕ} (c : ℝ) (h : Fin n → ℤ) (b : Fin n → ℝ) : ℂ :=
  Complex.exp (2*Real.pi*Complex.I*((∑ i, (h i : ℝ)*b i) : ℝ)/c)

def dualGaussian {n : ℕ} (c W : ℝ) (h : Fin n → ℤ) : ℝ :=
  Real.exp (-(Real.pi^2*W^2/c^2)*(∑ i, (h i : ℝ)^2))

def residueGaussian {n : ℕ} (c W : ℝ) (b u : Fin n → ℝ) : ℝ :=
  ∑' z : Fin n → ℤ, Real.exp (-(∑ i, ((b i+c*(z i : ℝ)-u i)/W)^2))

def character {X : Type*} [Fintype X] {n : ℕ}
    (c : ℝ) (b : X → Fin n → ℝ) (w : X → ℝ) (h : Fin n → ℤ) : ℂ :=
  ∑ x, (w x : ℂ)*phase c h (b x)

theorem norm_phase {n : ℕ} (c : ℝ) (h : Fin n → ℤ) (b : Fin n → ℝ) :
    ‖phase c h b‖ = 1 := by
  rw [phase, Complex.norm_exp]
  simp

theorem phase_sub {n : ℕ} (c : ℝ) (h : Fin n → ℤ) (b u : Fin n → ℝ) :
    phase c h (fun i => b i-u i) = phase c h b * phase c h (fun i => -u i) := by
  unfold phase
  rw [← Complex.exp_add]
  congr 1
  simp only [mul_sub, Finset.sum_sub_distrib, mul_neg, Finset.sum_neg_distrib]
  push_cast
  ring

theorem summable_dualGaussian {n : ℕ} (c W : ℝ) (hc : 0 < c) (hW : 0 < W) :
    Summable (dualGaussian (n := n) c W) := by
  have hs := GaussianLatticePoisson.summable_dual_gaussian_norm c W
    (0 : Fin n → ℝ) 0 hc hW
  simpa only [Pi.zero_apply, sub_self, mul_zero, Finset.sum_const_zero,
    Complex.ofReal_zero, div_zero, zero_div, Complex.exp_zero, mul_one,
    Complex.norm_of_nonneg (Real.exp_nonneg _), dualGaussian] using hs

theorem summable_dual_character_norm {X : Type*} [Fintype X] {n : ℕ}
    (c W : ℝ) (hc : 0 < c) (hW : 0 < W) (b : X → Fin n → ℝ) (w : X → ℝ) :
    Summable (fun h => dualGaussian c W h * ‖character c b w h‖) := by
  have hb (h : Fin n → ℤ) : ‖character c b w h‖ ≤ ∑ x, |w x| := by
    calc
      _ ≤ ∑ x, ‖(w x : ℂ)*phase c h (b x)‖ := norm_sum_le _ _
      _ = _ := by simp only [norm_mul, norm_phase, mul_one, Complex.norm_real, Real.norm_eq_abs]
  exact Summable.of_nonneg_of_le (fun h => by
    exact mul_nonneg (Real.exp_nonneg _) (norm_nonneg _))
    (fun h => mul_le_mul_of_nonneg_left (hb h) (Real.exp_nonneg _))
    ((summable_dualGaussian c W hc hW).mul_right _)

/-- Exact weighted identity; the translated center remains a unit phase. -/
theorem weighted_identity {X : Type*} [Fintype X] {n : ℕ}
    (c W : ℝ) (hc : 0 < c) (hW : 0 < W)
    (b : X → Fin n → ℝ) (u : Fin n → ℝ) (w : X → ℝ) :
    ((∑ x, w x * residueGaussian c W (b x) u : ℝ) : ℂ) =
      ((Real.sqrt Real.pi*W/c : ℝ) : ℂ)^n *
        ∑' h : Fin n → ℤ,
          (dualGaussian c W h : ℂ) * phase c h (fun i => -u i) * character c b w h := by
  classical
  have hs (x : X) : Summable (fun h : Fin n → ℤ => (w x : ℂ) *
      ((dualGaussian c W h : ℂ) * phase c h (fun i => b x i-u i))) :=
    (GaussianLatticePoisson.summable_dual_gaussian c W (b x) u hc hW).mul_left (w x : ℂ)
  have he (x : X) : (residueGaussian c W (b x) u : ℂ) =
      ((Real.sqrt Real.pi*W/c : ℝ) : ℂ)^n *
        ∑' h : Fin n → ℤ, (dualGaussian c W h : ℂ) *
          phase c h (fun i => b x i-u i) := by
    simpa only [residueGaussian, Complex.ofReal_tsum, dualGaussian, phase] using
      GaussianLatticePoisson.residue_gaussian_eq c W (b x) u hc hW
  simp only [Complex.ofReal_sum, Complex.ofReal_mul, he]
  calc
    _ = ((Real.sqrt Real.pi*W/c : ℝ) : ℂ)^n *
        ∑ x, (w x : ℂ) * ∑' h : Fin n → ℤ,
          (dualGaussian c W h : ℂ) * phase c h (fun i => b x i-u i) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      ring
    _ = _ := by
      congr 1
      rw [show (∑ x, (w x : ℂ) * ∑' h : Fin n → ℤ,
          (dualGaussian c W h : ℂ) * phase c h (fun i => b x i-u i)) =
          ∑ x, ∑' h : Fin n → ℤ, (w x : ℂ) *
          ((dualGaussian c W h : ℂ) * phase c h (fun i => b x i-u i)) by
        simp only [tsum_mul_left]]
      rw [← Summable.tsum_finsetSum (s := Finset.univ) (fun x _ => hs x)]
      apply tsum_congr
      intro h
      simp only [phase_sub, character, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      ring

/-- Taking the norm only after the finite Fourier sum preserves cancellation. -/
theorem weighted_le {X : Type*} [Fintype X] {n : ℕ}
    (c W : ℝ) (hc : 0 < c) (hW : 0 < W)
    (b : X → Fin n → ℝ) (u : Fin n → ℝ) (w : X → ℝ) :
    (∑ x, w x * residueGaussian c W (b x) u) ≤
      (Real.sqrt Real.pi*W/c)^n *
        ∑' h : Fin n → ℤ, dualGaussian c W h * ‖character c b w h‖ := by
  have hp : 0 ≤ (Real.sqrt Real.pi*W/c)^n := by positivity
  have he (h : Fin n → ℤ) :
      ‖(dualGaussian c W h : ℂ)*phase c h (fun i => -u i)*character c b w h‖ =
        dualGaussian c W h * ‖character c b w h‖ := by
    rw [norm_mul, norm_mul, norm_phase, mul_one,
      Complex.norm_of_nonneg (show 0 ≤ dualGaussian c W h from Real.exp_nonneg _)]
  have hs : Summable (fun h : Fin n → ℤ =>
      ‖(dualGaussian c W h : ℂ)*phase c h (fun i => -u i)*character c b w h‖) := by
    simpa only [he] using summable_dual_character_norm c W hc hW b w
  calc
    _ ≤ ‖((∑ x, w x * residueGaussian c W (b x) u : ℝ) : ℂ)‖ := by
      rw [Complex.norm_real, Real.norm_eq_abs]
      exact le_abs_self _
    _ = (Real.sqrt Real.pi*W/c)^n * ‖∑' h : Fin n → ℤ,
          (dualGaussian c W h : ℂ)*phase c h (fun i => -u i)*character c b w h‖ := by
      rw [weighted_identity c W hc hW b u w, norm_mul, norm_pow,
        Complex.norm_of_nonneg (by positivity)]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      ((norm_tsum_le_tsum_norm hs).trans_eq (tsum_congr he)) hp

end CubicTenVariables.WeightedGaussianPoisson
