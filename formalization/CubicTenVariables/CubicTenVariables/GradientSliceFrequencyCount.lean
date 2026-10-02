import CubicTenVariables.GradientChartLipschitz
import CubicTenVariables.ResidueBoxCount

/-! Integer complementary frequencies on a fixed input slice of the actual
rank-seven gradient chart. Input columns and output rows remain independent. -/
set_option autoImplicit false
set_option maxHeartbeats 1500000
noncomputable section
namespace CubicTenVariables.GradientSliceFrequencyCount
open MvPolynomial HessianTheorem11 RealRegularGradientChart SelectedGradientCoordinates
open scoped NNReal

attribute [local instance] Classical.propDecidable

/-- The complementary output coordinates have dimension exactly three. -/
theorem card_complement_rows (F : MvPolynomial (Fin 10) ℝ) (D : Data F) :
    Fintype.card (Complement D.rows) = 3 := by
  have h := Fintype.card_congr
    (SelectedGradientSliceVolume.indexEquiv D.rows D.rows_injective)
  simp only [Fintype.card_sum, Fintype.card_fin] at h
  omega

/-- A coordinate reindexing, with no identification between rows and columns. -/
def complementRowsEquiv (F : MvPolynomial (Fin 10) ℝ) (D : Data F) :
    Complement D.rows ≃ Fin 3 :=
  (Fintype.equivFin _).trans (finCongr (card_complement_rows F D))

/-- A shifted integer box count transported across a finite index equivalence. -/
theorem card_le_shifted_box {ι : Type*} [Fintype ι] {n : ℕ}
    (e : ι ≃ Fin n) (S : Finset (ι → ℤ)) (u : ι → ℝ) (R : ℝ)
    (hR : 0 ≤ R) (hbox : ∀ a ∈ S, ∀ i, |(a i : ℝ)-u i| ≤ R) :
    (S.card : ℝ) ≤ (4*R+3)^n := by
  classical
  let reindex : (ι → ℤ) → (Fin n → ℤ) := fun a i => a (e.symm i)
  have hinj : Function.Injective reindex := by
    intro a b hab
    funext i
    simpa only [reindex, Equiv.symm_apply_apply] using congrFun hab (e i)
  have h := ResidueBoxCount.card_le_of_constant_residue 1 (S.image reindex)
    (fun i => u (e.symm i)) R hR (by
      intro a ha i
      obtain ⟨a',ha',heq⟩ := Finset.mem_image.mp ha
      rw [← heq]
      exact hbox a' ha' (e.symm i)) (by intros; exact Subsingleton.elim _ _)
  simpa only [Finset.card_image_of_injective S hinj, Nat.cast_one, div_one] using h

/-- One constant works before every scalar phase, width, input slice, selected
frequency and finite family of complementary integer frequencies. The witnesses
need not depend continuously on the frequency. In particular the statement
includes zero scalar phase and zero width. -/
theorem exists_uniform_bound (F : MvPolynomial (Fin 10) ℝ) (D : Data F) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ (α B : ℝ), 0 ≤ B →
      ∀ (w : Complement D.cols → ℝ) (b : Fin 7 → ℝ)
        (S : Finset (Complement D.rows → ℤ)),
      (∀ a ∈ S, ∃ x ∈ D.box,
        (∀ i : Complement D.cols, x i = w i) ∧
        (∀ i : Fin 7, |α * eval x (pderiv (D.rows i) F)-b i| ≤ B) ∧
        (∀ i : Complement D.rows, |α * eval x (pderiv i.val F)-(a i : ℝ)| ≤ B)) →
      (S.card : ℝ) ≤ K*(1+B)^3 := by
  classical
  obtain ⟨L,hL,hvariation⟩ := GradientChartLipschitz.exists_scaled_window_variation_bound F D
  let K : ℝ := (4*(1+2*(L : ℝ))+3)^3
  have hL0 : 0 ≤ (L : ℝ) := L.coe_nonneg
  have hK : 1 ≤ K := one_le_pow₀ (by linarith)
  refine ⟨K,hK,?_⟩
  intro α B hB w b S hS
  by_cases hne : S.Nonempty
  · obtain ⟨a₀,ha₀⟩ := hne
    obtain ⟨x₀,hx₀,hw₀,hb₀,ha₀x⟩ := hS a₀ ha₀
    have hnorm₀ : ‖α • (fun i : Fin 7 => eval x₀ (pderiv (D.rows i) F))-b‖ ≤ B := by
      apply (pi_norm_le_iff_of_nonneg hB).mpr
      intro i
      simpa only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Real.norm_eq_abs] using hb₀ i
    have hbox (a : Complement D.rows → ℤ) (ha : a ∈ S) (i : Complement D.rows) :
        |(a i : ℝ)-α*eval x₀ (pderiv i.val F)| ≤ (1+2*(L : ℝ))*B := by
      obtain ⟨x,hx,hw,hb,hax⟩ := hS a ha
      have hnorm : ‖α • (fun i : Fin 7 => eval x (pderiv (D.rows i) F))-b‖ ≤ B := by
        apply (pi_norm_le_iff_of_nonneg hB).mpr
        intro j
        simpa only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Real.norm_eq_abs] using hb j
      have hv := hvariation α B b hB x hx x₀ hx₀
        (fun j => (hw j).trans (hw₀ j).symm) hnorm hnorm₀
      have hcoord := (norm_le_pi_norm (α • gradient F x-α • gradient F x₀) i.val).trans hv
      have hcoord' : |α*eval x (pderiv i.val F)-α*eval x₀ (pderiv i.val F)| ≤
          2*(L : ℝ)*B := by
        simpa only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, gradient, Real.norm_eq_abs] using hcoord
      have hfirst : |(a i : ℝ)-α*eval x (pderiv i.val F)| ≤ B := by
        simpa only [abs_sub_comm] using hax i
      exact (abs_sub_le (a i : ℝ) (α*eval x (pderiv i.val F))
        (α*eval x₀ (pderiv i.val F))).trans (by nlinarith)
    have hc := card_le_shifted_box (complementRowsEquiv F D) S
      (fun i => α*eval x₀ (pderiv i.val F)) ((1+2*(L : ℝ))*B)
      (by positivity) hbox
    apply hc.trans
    have hbase : 4*((1+2*(L : ℝ))*B)+3 ≤ (4*(1+2*(L : ℝ))+3)*(1+B) := by
      nlinarith
    calc
      _ ≤ ((4*(1+2*(L : ℝ))+3)*(1+B))^3 :=
        pow_le_pow_left₀ (by positivity) hbase 3
      _ = K*(1+B)^3 := by simp only [mul_pow,K]
  · have he : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    simp only [he, Finset.card_empty, Nat.cast_zero]
    exact mul_nonneg (zero_le_one.trans hK) (by positivity)

end CubicTenVariables.GradientSliceFrequencyCount
