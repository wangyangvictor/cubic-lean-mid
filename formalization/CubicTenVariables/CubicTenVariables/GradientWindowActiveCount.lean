import CubicTenVariables.GradientSliceFrequencyCount
import CubicTenVariables.GradientWindowScaling

/-! Actual active lattice centers on a fixed selected-output fiber and a
fixed untouched-input slice. The two coordinate selections are independent. -/
set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.GradientWindowActiveCount
open MvPolynomial HessianTheorem11 RealRegularGradientChart SelectedGradientCoordinates
open SelectedGradientSliceVolume GradientWindowScaling
variable {F : MvPolynomial (Fin 10) ℝ}

def selected (D : Data F) (v : Fin 10 → ℤ) : Fin 7 → ℤ := fun i => v (D.rows i)
def complementary (D : Data F) (v : Fin 10 → ℤ) : Complement D.rows → ℤ := fun i => v i

theorem ext_of_selected_complementary (D : Data F) (v v' : Fin 10 → ℤ)
    (hr : selected D v=selected D v') (hc : complementary D v=complementary D v') : v=v' := by
  classical
  funext i
  by_cases hi : i ∈ Set.range D.rows
  · obtain ⟨j,rfl⟩ := hi
    exact congrFun hr j
  · exact congrFun hc ⟨i,hi⟩

/-- The literal set of active centers at a fixed untouched-input vector. -/
def active (D : Data F) (T : Finset (Fin 10 → ℤ))
    (a : (Fin 10 → ℤ) → (Fin 10 → ℤ)) (β δ : ℝ) (w : Complement D.cols → ℝ) :
    Finset (Fin 10 → ℤ) := by
  classical
  exact T.filter fun v => ∃ z : Fin 7 → ℝ,
    combine D.cols D.cols_injective z w ∈
      window F D.box 1 β (fun i => (a v i : ℝ)) δ

/-- The complementary-frequency count bounds the number of full centers
because their seven selected output coordinates are fixed. -/
theorem exists_bound (D : Data F) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ (β δ L : ℝ), 0 ≤ δ → 0 ≤ L →
      ∀ (w : Complement D.cols → ℝ) (b : Fin 7 → ℤ)
        (T : Finset (Fin 10 → ℤ)) (a : (Fin 10 → ℤ) → (Fin 10 → ℤ)),
      (∀ v ∈ T, selected D v=b) →
      (∀ v ∈ T, ∀ i, |(a v i : ℝ)-(v i : ℝ)| ≤ L) →
      ((active D T a β δ w).card : ℝ) ≤ K*(1+δ+L)^3 := by
  classical
  obtain ⟨K,hK,hcount⟩ := GradientSliceFrequencyCount.exists_uniform_bound F D
  refine ⟨K,hK,?_⟩
  intro β δ L hδ hL w b T a hrow hnear
  let A := active D T a β δ w
  let S := A.image (complementary D)
  have hcard : S.card=A.card := by
    apply Finset.card_image_of_injOn
    intro v hv v' hv' he
    apply ext_of_selected_complementary D v v' _ he
    exact (hrow v (Finset.mem_filter.mp hv).1).trans
      (hrow v' (Finset.mem_filter.mp hv').1).symm
  have hS : ∀ c ∈ S, ∃ x ∈ D.box,
      (∀ i : Complement D.cols, x i=w i) ∧
      (∀ i : Fin 7, |β*eval x (pderiv (D.rows i) F)-(b i : ℝ)| ≤ δ+L) ∧
      (∀ i : Complement D.rows, |β*eval x (pderiv i.val F)-(c i : ℝ)| ≤ δ+L) := by
    intro c hc
    obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hc
    obtain ⟨hvT,z,hz⟩ := Finset.mem_filter.mp hv
    have hz' : combine D.cols D.cols_injective z w ∈ D.box ∧
        ∀ i, |β*eval (combine D.cols D.cols_injective z w) (pderiv i F)-(a v i : ℝ)| ≤ δ := by
      simpa only [window,Set.mem_setOf_eq,inv_one,one_smul] using hz
    have hfull (i : Fin 10) :
        |β*eval (combine D.cols D.cols_injective z w) (pderiv i F)-(v i : ℝ)| ≤ δ+L :=
      (abs_sub_le _ (a v i : ℝ) _).trans (add_le_add (hz'.2 i) (hnear v hvT i))
    refine ⟨combine D.cols D.cols_injective z w,hz'.1,?_,?_,?_⟩
    · exact fun i => combine_complement D.cols D.cols_injective z w i
    · intro i
      have he : v (D.rows i)=b i := congrFun (hrow v hvT) i
      simpa only [he] using hfull (D.rows i)
    · exact fun i => hfull i.val
  have h := hcount β (δ+L) (add_nonneg hδ hL) w (fun i => (b i : ℝ)) S hS
  rw [hcard] at h
  simpa only [add_assoc] using h

end CubicTenVariables.GradientWindowActiveCount
