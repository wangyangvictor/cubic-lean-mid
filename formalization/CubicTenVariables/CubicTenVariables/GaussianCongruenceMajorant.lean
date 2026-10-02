import CubicTenVariables.GaussianLatticePoisson

/-! Gaussian majorization of finite sets in an arbitrary translated box
and one actual integer congruence class. No truncation is used. -/

noncomputable section
namespace CubicTenVariables.GaussianCongruenceMajorant
open scoped BigOperators
attribute [local instance] Classical.propDecidable

/-- The nonnegative real Gaussian is summable on the full progression. -/
theorem summable_progression_gaussian {n : ℕ} (c : ℕ) (hc : 0 < c)
    (W : ℝ) (hW : 0 < W) (u : Fin n → ℝ) (b : Fin n → ℤ) :
    Summable (fun z : Fin n → ℤ =>
      Real.exp (-(∑ i, (((b i : ℝ)+(c : ℝ)*(z i : ℝ)-u i)/W)^2))) := by
  have hcR : 0 < (c : ℝ) := by exact_mod_cast hc
  have hs := GaussianLatticePoisson.summable_residue_gaussian_norm
    (c : ℝ) W (fun i => (b i : ℝ)) u hcR hW
  simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using hs

/-- Exact integer coordinates for a point in the congruence class of b. -/
theorem reconstruct_of_dvd {n : ℕ} (c : ℕ) (b v : Fin n → ℤ)
    (hv : ∀ i, (c : ℤ) ∣ v i-b i) (i : Fin n) :
    b i+(c : ℤ)*((v i-b i)/(c : ℤ)) = v i := by
  have h := Int.ediv_mul_cancel (hv i)
  rw [mul_comm] at h
  omega

/-- A finite portion of a congruence class has Gaussian mass at most the
full lattice progression, using the literal integer quotient injection. -/
theorem sum_congruence_gaussian_le {n : ℕ} (c : ℕ) (hc : 0 < c)
    (W : ℝ) (hW : 0 < W) (u : Fin n → ℝ) (b : Fin n → ℤ)
    (V : Finset (Fin n → ℤ)) :
    (∑ v ∈ V.filter (fun v => ∀ i, (c : ℤ) ∣ v i-b i),
      Real.exp (-(∑ i, (((v i : ℝ)-u i)/W)^2))) ≤
      ∑' z : Fin n → ℤ,
        Real.exp (-(∑ i, (((b i : ℝ)+(c : ℝ)*(z i : ℝ)-u i)/W)^2)) := by
  let S := V.filter (fun v => ∀ i, (c : ℤ) ∣ v i-b i)
  let q : (Fin n → ℤ) → (Fin n → ℤ) := fun v i => (v i-b i)/(c : ℤ)
  let G : (Fin n → ℤ) → ℝ := fun z =>
    Real.exp (-(∑ i, (((b i : ℝ)+(c : ℝ)*(z i : ℝ)-u i)/W)^2))
  have hrec (v : Fin n → ℤ) (hv : v ∈ S) (i : Fin n) :
      b i+(c : ℤ)*q v i = v i :=
    reconstruct_of_dvd c b v (Finset.mem_filter.mp hv).2 i
  have hinj : Set.InjOn q (S : Set (Fin n → ℤ)) := by
    intro v hv v' hv' he
    funext i
    have h₁ := hrec v hv i
    have h₂ := hrec v' hv' i
    rw [congrFun he i] at h₁
    omega
  have hterm (v : Fin n → ℤ) (hv : v ∈ S) :
      Real.exp (-(∑ i, (((v i : ℝ)-u i)/W)^2)) = G (q v) := by
    dsimp [G]
    congr 2
    apply Finset.sum_congr rfl
    intro i _
    have hreal : (b i : ℝ)+(c : ℝ)*(q v i : ℝ) = (v i : ℝ) := by
      exact_mod_cast hrec v hv i
    rw [hreal]
  calc
    _ = ∑ v ∈ S, G (q v) := Finset.sum_congr rfl hterm
    _ = ∑ z ∈ S.image q, G z := (Finset.sum_image hinj).symm
    _ ≤ _ := (summable_progression_gaussian c hc W hW u b).sum_le_tsum _
      (fun z _ => Real.exp_nonneg _)

/-- The Gaussian is at least exp(-n) at every point of a box of radius
at most its width. The center and width are arbitrary real numbers. -/
theorem one_le_gaussian_majorant {n : ℕ} (W R : ℝ) (hW : 0 < W) (hRW : R ≤ W)
    (u : Fin n → ℝ) (v : Fin n → ℤ)
    (hbox : ∀ i, |(v i : ℝ)-u i| ≤ R) :
    1 ≤ Real.exp (n : ℝ) * Real.exp (-(∑ i, (((v i : ℝ)-u i)/W)^2)) := by
  have hs : (∑ i, (((v i : ℝ)-u i)/W)^2) ≤ (n : ℝ) := by
    calc
      _ ≤ ∑ _i : Fin n, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro i _
        apply (sq_le_one_iff_abs_le_one _).mpr
        rw [abs_div, abs_of_pos hW]
        exact (div_le_one hW).mpr ((hbox i).trans hRW)
      _ = _ := by simp
  rw [← Real.exp_add]
  exact Real.one_le_exp_iff.mpr (by linarith)

/-- Literal cardinality bound for one congruence class inside the given box. -/
theorem card_congruence_le {n : ℕ} (c : ℕ) (hc : 0 < c)
    (W R : ℝ) (hW : 0 < W) (_hR : 0 ≤ R) (hRW : R ≤ W)
    (u : Fin n → ℝ) (b : Fin n → ℤ) (V : Finset (Fin n → ℤ))
    (hbox : ∀ v ∈ V, ∀ i, |(v i : ℝ)-u i| ≤ R) :
    ((V.filter fun v => ∀ i, (c : ℤ) ∣ v i-b i).card : ℝ) ≤
      Real.exp (n : ℝ) * ∑' z : Fin n → ℤ,
        Real.exp (-(∑ i, (((b i : ℝ)+(c : ℝ)*(z i : ℝ)-u i)/W)^2)) := by
  calc
    _ = ∑ _v ∈ V.filter (fun v => ∀ i, (c : ℤ) ∣ v i-b i), (1 : ℝ) := by simp
    _ ≤ ∑ v ∈ V.filter (fun v => ∀ i, (c : ℤ) ∣ v i-b i),
        Real.exp (n : ℝ) * Real.exp (-(∑ i, (((v i : ℝ)-u i)/W)^2)) := by
      apply Finset.sum_le_sum
      intro v hv
      exact one_le_gaussian_majorant W R hW hRW u v (hbox v (Finset.mem_filter.mp hv).1)
    _ = Real.exp (n : ℝ) *
        ∑ v ∈ V.filter (fun v => ∀ i, (c : ℤ) ∣ v i-b i),
          Real.exp (-(∑ i, (((v i : ℝ)-u i)/W)^2)) := (Finset.mul_sum _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left (sum_congruence_gaussian_le c hc W hW u b V)
      (Real.exp_nonneg _)

/-- A bounded finite weighting obeys the same majorant, multiplied by
its upper bound. Negative weights are also permitted. -/
theorem weighted_congruence_le {n : ℕ} (c : ℕ) (hc : 0 < c)
    (W R : ℝ) (hW : 0 < W) (hR : 0 ≤ R) (hRW : R ≤ W)
    (u : Fin n → ℝ) (b : Fin n → ℤ) (V : Finset (Fin n → ℤ))
    (hbox : ∀ v ∈ V, ∀ i, |(v i : ℝ)-u i| ≤ R)
    (w : (Fin n → ℤ) → ℝ) (M : ℝ) (hM : 0 ≤ M) (hw : ∀ v ∈ V, w v ≤ M) :
    (∑ v ∈ V.filter (fun v => ∀ i, (c : ℤ) ∣ v i-b i), w v) ≤
      M * Real.exp (n : ℝ) * ∑' z : Fin n → ℤ,
        Real.exp (-(∑ i, (((b i : ℝ)+(c : ℝ)*(z i : ℝ)-u i)/W)^2)) := by
  calc
    _ ≤ ∑ _v ∈ V.filter (fun v => ∀ i, (c : ℤ) ∣ v i-b i), M :=
      Finset.sum_le_sum (fun v hv => hw v (Finset.mem_filter.mp hv).1)
    _ = M * ((V.filter fun v => ∀ i, (c : ℤ) ∣ v i-b i).card : ℝ) := by
      simp [mul_comm]
    _ ≤ M * (Real.exp (n : ℝ) * ∑' z : Fin n → ℤ,
        Real.exp (-(∑ i, (((b i : ℝ)+(c : ℝ)*(z i : ℝ)-u i)/W)^2))) :=
      mul_le_mul_of_nonneg_left (card_congruence_le c hc W R hW hR hRW u b V hbox) hM
    _ = _ := by rw [mul_assoc]

end CubicTenVariables.GaussianCongruenceMajorant
