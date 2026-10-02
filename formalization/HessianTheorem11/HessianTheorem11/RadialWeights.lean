import HessianTheorem11.Polarization
import HessianTheorem11.AdaptedFlag
import HessianTheorem11.CubicWeights

/-! Singular radial weights applied to the actual cubic tensor. -/

noncomputable section
namespace HessianTheorem11
open MvPolynomial Module

def singularRadialWeight {n : ℕ} (radial : Fin n) (IT IL : Finset (Fin n))
    (i : Fin n) : ℤ :=
  (if i = radial then -6 else 0) + (if i ∈ IT then -2 else 0) +
    (if i ∈ IL then 0 else 4)

theorem singularRadialWeight_radial {n : ℕ} {radial : Fin n} {IT IL : Finset (Fin n)}
    (hr : radial ∈ IT) (hnest : IT ⊆ IL) : singularRadialWeight radial IT IL radial = -8 := by
  simp [singularRadialWeight, hr, hnest hr]

theorem singularRadialWeight_normal {n : ℕ} {radial i : Fin n} {IT IL : Finset (Fin n)}
    (hr : radial ∈ IT) (hnest : IT ⊆ IL) (hi : i ∉ IL) :
    singularRadialWeight radial IT IL i = 4 := by
  have hne : i ≠ radial := by rintro rfl; exact hi (hnest hr)
  have hnot : i ∉ IT := fun h => hi (hnest h)
  simp [singularRadialWeight, hne, hnot, hi]

theorem singularRadialWeight_lower {n : ℕ} {radial i : Fin n} {IT IL : Finset (Fin n)}
    (hne : i ≠ radial) : -2 ≤ singularRadialWeight radial IT IL i := by
  unfold singularRadialWeight
  simp only [hne, if_false, zero_add]
  split_ifs <;> omega

theorem sum_singularRadialWeight {n : ℕ} (radial : Fin n) (IT IL : Finset (Fin n)) :
    ∑ i, singularRadialWeight radial IT IL i =
      -6 - 2 * (IT.card : ℤ) + 4 * ((n : ℤ) - (IL.card : ℤ)) := by
  classical
  unfold singularRadialWeight
  simp only [Finset.sum_add_distrib]
  have h1 : (∑ i : Fin n, if i = radial then (-6 : ℤ) else 0) = -6 := by simp
  have h2 : (∑ i : Fin n, if i ∈ IT then (-2 : ℤ) else 0) = -2 * IT.card := by
    rw [← Finset.sum_filter]
    simp [mul_comm]
  have h3 : (∑ i : Fin n, if i ∈ IL then (0 : ℤ) else 4) = 4 * ((n : ℤ) - IL.card) := by
    calc
      _ = ∑ i : Fin n, (4 - if i ∈ IL then (4 : ℤ) else 0) := by
        apply Finset.sum_congr rfl
        intro i _
        split_ifs <;> norm_num
      _ = _ := by
        rw [Finset.sum_sub_distrib, ← Finset.sum_filter]
        simp
        ring
  rw [h1, h2, h3]
  ring

section Tensor
variable {K : Type*} [Field K] {n : ℕ}

theorem singularRadialWeight_nonnegative_tensor
    (F : MvPolynomial (Fin n) K) (hF : F.IsHomogeneous 3)
    (b : Basis (Fin n) K (Fin n → K)) (radial : Fin n) (IT IL : Finset (Fin n))
    (hr : radial ∈ IT) (hnest : IT ⊆ IL)
    (hkernel : ∀ i ∈ IL, (hessian F (b radial)).mulVec (b i) = 0)
    (htangent : ∀ i ∈ IT, ∀ j ∈ IL, ∀ l ∈ IL,
      polarization F (b i) (b j) (b l) = 0)
    (i j l : Fin n) (hne : polarization F (b i) (b j) (b l) ≠ 0) :
    0 ≤ singularRadialWeight radial IT IL i + singularRadialWeight radial IT IL j +
      singularRadialWeight radial IT IL l := by
  have hradzero (a c : Fin n) (ha : a ∈ IL) :
      polarization F (b radial) (b a) (b c) = 0 := by
    rw [polarization_rotate hF, polarization_swap_last hF]
    change dotProduct (b c) ((hessian F (b radial)).mulVec (b a)) = 0
    rw [hkernel a ha]
    simp
  have hradweights (a c : Fin n)
      (h : polarization F (b radial) (b a) (b c) ≠ 0) :
      singularRadialWeight radial IT IL a = 4 ∧ singularRadialWeight radial IT IL c = 4 := by
    have ha : a ∉ IL := fun ha => h (hradzero a c ha)
    have hc : c ∉ IL := by
      intro hc
      apply h
      rw [polarization_swap_last hF]
      exact hradzero c a hc
    exact ⟨singularRadialWeight_normal hr hnest ha, singularRadialWeight_normal hr hnest hc⟩
  by_cases hir : i = radial
  · subst i
    obtain ⟨hj, hl⟩ := hradweights j l hne
    rw [singularRadialWeight_radial hr hnest, hj, hl]
    norm_num
  by_cases hjr : j = radial
  · subst j
    have h' : polarization F (b radial) (b i) (b l) ≠ 0 := by
      rwa [polarization_swap_first]
    obtain ⟨hi, hl⟩ := hradweights i l h'
    rw [hi, singularRadialWeight_radial hr hnest, hl]
    norm_num
  by_cases hlr : l = radial
  · subst l
    have h' : polarization F (b radial) (b i) (b j) ≠ 0 := by
      intro hz
      apply hne
      rw [polarization_rotate hF]
      exact hz
    obtain ⟨hi, hj⟩ := hradweights i j h'
    rw [hi, hj, singularRadialWeight_radial hr hnest]
    norm_num
  have hi_low := singularRadialWeight_lower (IT := IT) (IL := IL) hir
  have hj_low := singularRadialWeight_lower (IT := IT) (IL := IL) hjr
  have hl_low := singularRadialWeight_lower (IT := IT) (IL := IL) hlr
  by_cases hiL : i ∈ IL
  swap
  · have hi := singularRadialWeight_normal hr hnest hiL
    omega
  by_cases hjL : j ∈ IL
  swap
  · have hj := singularRadialWeight_normal hr hnest hjL
    omega
  by_cases hlL : l ∈ IL
  swap
  · have hl := singularRadialWeight_normal hr hnest hlL
    omega
  have hiT : i ∉ IT := fun hi => hne (htangent i hi j hjL l hlL)
  have hjT : j ∉ IT := by
    intro hj
    apply hne
    rw [polarization_swap_first]
    exact htangent j hj i hiL l hlL
  have hlT : l ∉ IT := by
    intro hl
    apply hne
    rw [polarization_rotate hF]
    exact htangent l hl i hiL j hjL
  simp [singularRadialWeight, hir, hjr, hlr, hiT, hjT, hlT, hiL, hjL, hlL]

end Tensor
end HessianTheorem11
