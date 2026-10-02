import CubicTenVariables.GaussianResiduePoisson
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Data.Fin.Tuple.Basic

/-! Tensorization of the literal shifted residue Gaussian identity. All
lattice sums, including the norm sums needed for interchange, converge. -/

noncomputable section
namespace CubicTenVariables.GaussianLatticePoisson
open scoped BigOperators

/-- Absolute convergence of a finite product of one-dimensional series. -/
theorem summable_norm_pi_prod {n : ℕ} (f : Fin n → ℤ → ℂ)
    (hf : ∀ i, Summable (fun k : ℤ => ‖f i k‖)) :
    Summable (fun z : Fin n → ℤ => ‖∏ i, f i (z i)‖) := by
  induction n with
  | zero => exact Summable.of_finite
  | succ n ih =>
    have ht := ih (fun i => f i.succ) (fun i => hf i.succ)
    have hs := (hf 0).mul_norm ht
    have he := hs.comp_injective (Fin.consEquiv (fun _ : Fin (n+1) => ℤ)).symm.injective
    simpa only [Function.comp_def, Fin.prod_univ_succ, Fin.consEquiv_symm_apply, Fin.tail] using he

/-- Tensor-product summation over the actual integer-coordinate lattice. -/
theorem tsum_pi_prod {n : ℕ} (f : Fin n → ℤ → ℂ)
    (hf : ∀ i, Summable (fun k : ℤ => ‖f i k‖)) :
    (∑' z : Fin n → ℤ, ∏ i, f i (z i)) = ∏ i, ∑' k : ℤ, f i k := by
  induction n with
  | zero =>
    letI : Fintype (Fin 0 → ℤ) := Fintype.ofFinite _
    simp [tsum_fintype]
  | succ n ih =>
    rw [← (Fin.consEquiv (fun _ : Fin (n+1) => ℤ)).tsum_eq
      (fun z => ∏ i, f i (z i))]
    simp only [Fin.consEquiv_apply, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]
    rw [← tsum_mul_tsum_of_summable_norm (hf 0)
      (summable_norm_pi_prod (fun i => f i.succ) (fun i => hf i.succ)), ih]
    exact fun i => hf i.succ

/-- Factor the literal progression Gaussian into its coordinate Gaussians. -/
theorem residue_term_eq_prod {n : ℕ} (c W : ℝ) (a u : Fin n → ℝ) (z : Fin n → ℤ) :
    (Real.exp (-(∑ i, ((a i+c*(z i : ℝ)-u i)/W)^2)) : ℂ) =
      ∏ i, (Real.exp (-((a i+c*(z i : ℝ)-u i)/W)^2) : ℂ) := by
  rw [← Finset.sum_neg_distrib, Real.exp_sum, Complex.ofReal_prod]

/-- The product phase retains the full translated real dot product. -/
theorem dual_term_eq_prod {n : ℕ} (c W : ℝ) (a u : Fin n → ℝ) (h : Fin n → ℤ) :
    (Real.exp (-(Real.pi^2*W^2/c^2)*(∑ i, (h i : ℝ)^2)) : ℂ) *
      Complex.exp (2*Real.pi*Complex.I*((∑ i, (h i : ℝ)*(a i-u i)) : ℝ)/c) =
      ∏ i, (Real.exp (-Real.pi^2*W^2*(h i : ℝ)^2/c^2) : ℂ) *
        Complex.exp (2*Real.pi*Complex.I*(h i : ℂ)*(((a i-u i)/c : ℝ) : ℂ)) := by
  rw [Finset.prod_mul_distrib]
  congr 1
  · rw [← Complex.ofReal_prod, ← Real.exp_sum]
    congr 2
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  · rw [← Complex.exp_sum]
    congr 1
    push_cast
    simp only [Finset.mul_sum, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i _
    ring

/-- Absolute convergence on the translated physical lattice. -/
theorem summable_residue_gaussian_norm {n : ℕ} (c W : ℝ) (a u : Fin n → ℝ)
    (hc : 0 < c) (hW : 0 < W) :
    Summable (fun z : Fin n → ℤ =>
      ‖(Real.exp (-(∑ i, ((a i+c*(z i : ℝ)-u i)/W)^2)) : ℂ)‖) := by
  simpa only [residue_term_eq_prod] using summable_norm_pi_prod
    (fun i k => (Real.exp (-((a i+c*(k : ℝ)-u i)/W)^2) : ℂ))
    (fun i => GaussianResiduePoisson.summable_residue_gaussian_norm c W (a i) (u i) hc hW)

theorem summable_residue_gaussian {n : ℕ} (c W : ℝ) (a u : Fin n → ℝ)
    (hc : 0 < c) (hW : 0 < W) :
    Summable (fun z : Fin n → ℤ =>
      (Real.exp (-(∑ i, ((a i+c*(z i : ℝ)-u i)/W)^2)) : ℂ)) :=
  (summable_residue_gaussian_norm c W a u hc hW).of_norm

/-- Absolute convergence of the full dual lattice, including its phase. -/
theorem summable_dual_gaussian_norm {n : ℕ} (c W : ℝ) (a u : Fin n → ℝ)
    (hc : 0 < c) (hW : 0 < W) :
    Summable (fun h : Fin n → ℤ =>
      ‖(Real.exp (-(Real.pi^2*W^2/c^2)*(∑ i, (h i : ℝ)^2)) : ℂ) *
        Complex.exp (2*Real.pi*Complex.I*((∑ i, (h i : ℝ)*(a i-u i)) : ℝ)/c)‖) := by
  simpa only [dual_term_eq_prod] using summable_norm_pi_prod
    (fun i k => (Real.exp (-Real.pi^2*W^2*(k : ℝ)^2/c^2) : ℂ) *
      Complex.exp (2*Real.pi*Complex.I*(k : ℂ)*(((a i-u i)/c : ℝ) : ℂ)))
    (fun i => GaussianResiduePoisson.summable_dual_gaussian_norm c W (a i) (u i) hc hW)

theorem summable_dual_gaussian {n : ℕ} (c W : ℝ) (a u : Fin n → ℝ)
    (hc : 0 < c) (hW : 0 < W) :
    Summable (fun h : Fin n → ℤ =>
      (Real.exp (-(Real.pi^2*W^2/c^2)*(∑ i, (h i : ℝ)^2)) : ℂ) *
        Complex.exp (2*Real.pi*Complex.I*((∑ i, (h i : ℝ)*(a i-u i)) : ℝ)/c)) :=
  (summable_dual_gaussian_norm c W a u hc hW).of_norm

/-- Exact Gaussian Poisson identity on an arbitrary finite-dimensional
integer lattice, with real center and spacing and no truncation. -/
theorem residue_gaussian_eq {n : ℕ} (c W : ℝ) (a u : Fin n → ℝ)
    (hc : 0 < c) (hW : 0 < W) :
    (∑' z : Fin n → ℤ, (Real.exp (-(∑ i, ((a i+c*(z i : ℝ)-u i)/W)^2)) : ℂ)) =
      ((Real.sqrt Real.pi*W/c : ℝ) : ℂ)^n *
        ∑' h : Fin n → ℤ,
          (Real.exp (-(Real.pi^2*W^2/c^2)*(∑ i, (h i : ℝ)^2)) : ℂ) *
            Complex.exp (2*Real.pi*Complex.I*((∑ i, (h i : ℝ)*(a i-u i)) : ℝ)/c) := by
  simp_rw [residue_term_eq_prod]
  rw [tsum_pi_prod _
    (fun i => GaussianResiduePoisson.summable_residue_gaussian_norm c W (a i) (u i) hc hW)]
  simp_rw [GaussianResiduePoisson.residue_gaussian_eq c W _ _ hc hW]
  rw [Finset.prod_mul_distrib]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  congr 1
  rw [← tsum_pi_prod _
    (fun i => GaussianResiduePoisson.summable_dual_gaussian_norm c W (a i) (u i) hc hW)]
  apply tsum_congr
  intro h
  exact (dual_term_eq_prod c W a u h).symm

end CubicTenVariables.GaussianLatticePoisson
