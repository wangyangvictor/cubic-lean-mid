import HessianTheorem11.UnconditionalOrderedRational
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Localization.Integer

/-! Finite homogeneous integral inequalities valid in an arbitrary ordered
valuation group admit actual integral weights. Weak inequalities, strict
inequalities, and the determinant-one sum-zero equation are preserved. -/
noncomputable section
namespace HessianTheorem11.UnconditionalOrderedWeights
open Finset
variable {Γ : Type*} [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]

theorem integral_solution (n : ℕ) {ι : Type} [Fintype ι]
    (c : ι → Fin n → ℤ) (s : ι → Bool) (x : Fin n → Γ)
    (h : ∀ a, Holds (s a) (value (c a) x)) :
    ∃ w : Fin n → ℤ, ∀ a, Holds (s a) (∑ i, c a i * w i) := by
  classical
  obtain ⟨y,hy⟩ := rational_solution n c s x h
  obtain ⟨N,hN⟩ := IsLocalization.exist_integer_multiples_of_finite (Submonoid.pos ℤ) y
  choose w hw using hN
  have he (i : Fin n) : (w i : ℚ) = (N.val : ℚ) * y i := by
    simpa only [Algebra.smul_def] using hw i
  have hNp : (0 : ℚ) < N.val := by exact_mod_cast N.property
  refine ⟨w,?_⟩
  intro a
  have hd : ((∑ i, c a i * w i : ℤ) : ℚ) = (N.val : ℚ) * value (c a) y := by
    simp only [Int.cast_sum,Int.cast_mul,he,value_rat,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hh := hy a
  cases hs : s a <;> simp only [Holds,hs,↓reduceIte] at hh ⊢
  · have hp := mul_nonneg hNp.le hh
    rw [← hd] at hp
    exact_mod_cast hp
  · have hp := mul_pos hNp hh
    rw [← hd] at hp
    exact_mod_cast hp

/-- Finite weak and strict valuation inequalities can be realized by a
single determinant-one integral one-parameter weight. No Archimedean
hypothesis on the ordered group is needed. -/
theorem exists_integral_weight {n : ℕ} (x : Fin n → Γ) (hx : ∑ i, x i = 0)
    (S T : Finset (Fin n → ℤ))
    (hS : ∀ a ∈ S, 0 ≤ value a x) (hT : ∀ a ∈ T, 0 < value a x) :
    ∃ w : Fin n → ℤ, (∑ i, w i = 0) ∧
      (∀ a ∈ S, 0 ≤ ∑ i, a i * w i) ∧
      (∀ a ∈ T, 0 < ∑ i, a i * w i) := by
  classical
  let I := Bool ⊕ (S ⊕ T)
  let c : I → Fin n → ℤ := Sum.elim
    (fun b _ => if b then 1 else -1) (Sum.elim (fun a => a.val) (fun a => a.val))
  let s : I → Bool := Sum.elim (fun _ => false) (Sum.elim (fun _ => false) (fun _ => true))
  have h : ∀ a, Holds (s a) (value (c a) x) := by
    intro a
    cases a with
    | inl b =>
      cases b <;> simp [s,c,Holds,value,Finset.sum_neg_distrib,hx]
    | inr a =>
      cases a with
      | inl a => exact hS a.val a.property
      | inr a => exact hT a.val a.property
  obtain ⟨w,hw⟩ := integral_solution n c s x h
  have hp := hw (Sum.inl true)
  have hm := hw (Sum.inl false)
  simp [c,s,Holds,Finset.sum_neg_distrib] at hp hm
  refine ⟨w,by omega,?_,?_⟩
  · intro a ha
    exact hw (Sum.inr (Sum.inl ⟨a,ha⟩))
  · intro a ha
    exact hw (Sum.inr (Sum.inr ⟨a,ha⟩))

theorem exists_nonzero_integral_weight {n : ℕ} (x : Fin n → Γ) (hx : ∑ i, x i = 0)
    (S T : Finset (Fin n → ℤ)) (hne : T.Nonempty)
    (hS : ∀ a ∈ S, 0 ≤ value a x) (hT : ∀ a ∈ T, 0 < value a x) :
    ∃ w : Fin n → ℤ, w ≠ 0 ∧ (∑ i, w i = 0) ∧
      (∀ a ∈ S, 0 ≤ ∑ i, a i * w i) ∧
      (∀ a ∈ T, 0 < ∑ i, a i * w i) := by
  obtain ⟨w,hw,hSw,hTw⟩ := exists_integral_weight x hx S T hS hT
  refine ⟨w,?_,hw,hSw,hTw⟩
  intro hz
  obtain ⟨a,ha⟩ := hne
  have hp := hTw a ha
  simp [hz] at hp

end HessianTheorem11.UnconditionalOrderedWeights
