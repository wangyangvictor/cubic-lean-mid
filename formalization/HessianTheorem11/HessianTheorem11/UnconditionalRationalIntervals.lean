import Mathlib.Data.Finset.Max
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic

/-! Finite compatible rational lower and upper bounds have a common
rational solution, with each strict endpoint condition retained. -/
namespace HessianTheorem11.UnconditionalOrderedWeights

def Holds (strict : Bool) {Γ : Type*} [Zero Γ] [LT Γ] [LE Γ] (x : Γ) : Prop :=
  if strict then 0 < x else 0 ≤ x

theorem rational_between {α β : Type*} [Fintype α] [Fintype β]
    (L : α → ℚ) (U : β → ℚ) (sl : α → Bool) (su : β → Bool)
    (h : ∀ i j, if sl i || su j then L i < U j else L i ≤ U j) :
    ∃ x : ℚ, (∀ i, if sl i then L i < x else L i ≤ x) ∧
      (∀ j, if su j then x < U j else x ≤ U j) := by
  classical
  by_cases hα : Nonempty α
  · letI := hα
    obtain ⟨i,_,hi⟩ := Finset.exists_max_image Finset.univ L Finset.univ_nonempty
    by_cases hβ : Nonempty β
    · letI := hβ
      obtain ⟨j,_,hj⟩ := Finset.exists_min_image Finset.univ U Finset.univ_nonempty
      have hij : L i ≤ U j := by
        have hh := h i j
        split_ifs at hh with hs
        · exact hh.le
        · exact hh
      rcases lt_or_eq_of_le hij with hlt | heq
      · refine ⟨(L i + U j)/2,?_,?_⟩
        · intro a
          have ha := hi a (Finset.mem_univ a)
          split_ifs <;> linarith
        · intro b
          have hb := hj b (Finset.mem_univ b)
          split_ifs <;> linarith
      · refine ⟨L i,?_,?_⟩
        · intro a
          split_ifs with hs
          · have hh := h a j
            simp only [hs,Bool.true_or,if_true] at hh
            linarith
          · exact hi a (Finset.mem_univ a)
        · intro b
          split_ifs with hs
          · have hh := h i b
            simpa only [hs,Bool.or_true,if_true] using hh
          · rw [heq]
            exact hj b (Finset.mem_univ b)
    · letI : IsEmpty β := not_nonempty_iff.mp hβ
      refine ⟨L i + 1,?_,fun j => isEmptyElim j⟩
      intro a
      have ha := hi a (Finset.mem_univ a)
      split_ifs <;> linarith
  · letI : IsEmpty α := not_nonempty_iff.mp hα
    by_cases hβ : Nonempty β
    · letI := hβ
      obtain ⟨j,_,hj⟩ := Finset.exists_min_image Finset.univ U Finset.univ_nonempty
      refine ⟨U j - 1,fun i => isEmptyElim i,?_⟩
      intro b
      have hb := hj b (Finset.mem_univ b)
      split_ifs <;> linarith
    · letI : IsEmpty β := not_nonempty_iff.mp hβ
      exact ⟨0,fun i => isEmptyElim i,fun j => isEmptyElim j⟩

end HessianTheorem11.UnconditionalOrderedWeights
