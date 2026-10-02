import Mathlib.Data.Finset.Max
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Real.Basic

/-! A class majorant obtained by choosing a maximizing representative
from every nonempty fiber of a finite set. -/
set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.FiniteClassMajorant
open scoped BigOperators

/-- A bound on every finite transversal supplies a nonnegative class
majorant with the same total-mass bound. No periodicity of `a` is needed. -/
theorem exists_majorant {α β : Type*} [Fintype β]
    (E : Finset α) (tag : α → β) (a : α → ℝ) (K : ℝ)
    (ha : ∀ x ∈ E, 0 ≤ a x) (hK : 0 ≤ K)
    (htrans : ∀ U : Finset α, U ⊆ E → Set.InjOn tag (U : Set α) →
      (∑ x ∈ U, a x) ≤ K) :
    ∃ P : β → ℝ, (∀ b, 0 ≤ P b) ∧
      (∀ x ∈ E, a x ≤ P (tag x)) ∧ (∑ b, P b) ≤ K := by
  classical
  rcases E.eq_empty_or_nonempty with rfl | hE
  · exact ⟨fun _ => 0, fun _ => le_rfl, by simp, by simpa using hK⟩
  obtain ⟨x₀,hx₀⟩ := hE
  let B : Finset β := E.image tag
  have hex (b : β) (hb : b ∈ B) :
      ∃ x ∈ E, tag x = b ∧ ∀ y ∈ E, tag y = b → a y ≤ a x := by
    obtain ⟨y,hy,hyb⟩ := Finset.mem_image.mp hb
    have hne : (E.filter (fun x => tag x = b)).Nonempty :=
      ⟨y,Finset.mem_filter.mpr ⟨hy,hyb⟩⟩
    obtain ⟨x,hx,hmax⟩ := Finset.exists_max_image (E.filter (fun x => tag x = b)) a hne
    exact ⟨x,(Finset.mem_filter.mp hx).1,(Finset.mem_filter.mp hx).2,
      fun y hy hyb => hmax y (Finset.mem_filter.mpr ⟨hy,hyb⟩)⟩
  let pick (b : β) : α := if hb : b ∈ B then (hex b hb).choose else x₀
  have hpick (b : β) (hb : b ∈ B) :
      pick b ∈ E ∧ tag (pick b) = b ∧ ∀ y ∈ E, tag y = b → a y ≤ a (pick b) := by
    simpa only [pick,dif_pos hb] using (hex b hb).choose_spec
  let U : Finset α := B.image pick
  let P (b : β) : ℝ := if b ∈ B then a (pick b) else 0
  have hU : U ⊆ E := by
    intro x hx
    obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hx
    exact (hpick b hb).1
  have htag : Set.InjOn tag (U : Set α) := by
    intro x hx y hy hxy
    obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨c,hc,rfl⟩ := Finset.mem_image.mp hy
    have hbc : b = c := (hpick b hb).2.1.symm.trans (hxy.trans (hpick c hc).2.1)
    rw [hbc]
  have hinj : Set.InjOn pick (B : Set β) := by
    intro b hb c hc hbc
    exact (hpick b hb).2.1.symm.trans ((congrArg tag hbc).trans (hpick c hc).2.1)
  have hmass : (∑ b, P b) = ∑ x ∈ U, a x := by
    calc
      _ = ∑ b ∈ B, a (pick b) := by simp [P,← Finset.sum_filter]
      _ = _ := (Finset.sum_image hinj).symm
  refine ⟨P,?_,?_,hmass.trans_le (htrans U hU htag)⟩
  · intro b
    by_cases hb : b ∈ B
    · simpa only [P,if_pos hb] using ha (pick b) (hpick b hb).1
    · simp only [P,if_neg hb,le_refl]
  · intro x hx
    have hb : tag x ∈ B := Finset.mem_image_of_mem tag hx
    simpa only [P,if_pos hb] using (hpick (tag x) hb).2.2 x hx rfl

end CubicTenVariables.FiniteClassMajorant
