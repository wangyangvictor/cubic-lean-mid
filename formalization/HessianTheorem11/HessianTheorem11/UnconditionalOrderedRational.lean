import HessianTheorem11.UnconditionalOrderedLinear

/-! Finite homogeneous integral inequalities feasible in an arbitrary
ordered additive group are feasible over ℚ. Fourier–Motzkin elimination
preserves the strict inequalities exactly. -/
namespace HessianTheorem11.UnconditionalOrderedWeights
open Finset
variable {Γ : Type*} [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]

theorem rational_solution (n : ℕ) {ι : Type} [Fintype ι]
    (c : ι → Fin n → ℤ) (s : ι → Bool) (x : Fin n → Γ)
    (h : ∀ a, Holds (s a) (value (c a) x)) :
    ∃ y : Fin n → ℚ, ∀ a, Holds (s a) (value (c a) y) := by
  classical
  induction n generalizing ι with
  | zero =>
    refine ⟨0,?_⟩
    intro a
    have ha := h a
    cases hs : s a <;> simp [Holds,value,hs] at *
  | succ n ih =>
    let I0 := {a : ι // c a 0 = 0}
    let Ip := {a : ι // 0 < c a 0}
    let Im := {a : ι // c a 0 < 0}
    let J := I0 ⊕ (Ip × Im)
    let C : J → Fin n → ℤ := Sum.elim
      (fun a => c a.val ∘ Fin.succ) (fun ab => eliminate (c ab.1.val) (c ab.2.val))
    let S : J → Bool := Sum.elim (fun a => s a.val) (fun ab => s ab.1.val || s ab.2.val)
    have hC : ∀ j, Holds (S j) (value (C j) (x ∘ Fin.succ)) := by
      intro j
      cases j with
      | inl a =>
        have ha := h a.val
        rw [value_succ,a.property,zero_smul,zero_add] at ha
        exact ha
      | inr ab =>
        change Holds (s ab.1.val || s ab.2.val)
          (value (eliminate (c ab.1.val) (c ab.2.val)) (x ∘ Fin.succ))
        rw [value_eliminate]
        exact holds_positive_combination (h ab.1.val) (h ab.2.val)
          (neg_pos.mpr ab.2.property) ab.1.property
    obtain ⟨y,hy⟩ := ih C S (x ∘ Fin.succ) hC
    let L : Ip → ℚ := fun a => -value (c a.val ∘ Fin.succ) y / (c a.val 0 : ℚ)
    let U : Im → ℚ := fun b => value (c b.val ∘ Fin.succ) y / (-(c b.val 0 : ℚ))
    have hpair : ∀ a b, if s a.val || s b.val then L a < U b else L a ≤ U b := by
      intro a b
      have hab := hy (Sum.inr (a,b))
      change Holds (s a.val || s b.val) (value (eliminate (c a.val) (c b.val)) y) at hab
      rw [value_eliminate_tail] at hab
      simp only [zsmul_eq_mul,Int.cast_neg] at hab
      have ha : (0 : ℚ) < c a.val 0 := by exact_mod_cast a.property
      have hb : (0 : ℚ) < -(c b.val 0 : ℚ) := by exact_mod_cast (neg_pos.mpr b.property)
      unfold Holds at hab
      split_ifs at hab ⊢ with hs
      · apply (div_lt_div_iff₀ ha hb).mpr
        nlinarith
      · apply (div_le_div_iff₀ ha hb).mpr
        nlinarith
    obtain ⟨r,hrL,hrU⟩ := rational_between L U (fun a => s a.val) (fun b => s b.val) hpair
    refine ⟨Fin.cons r y,?_⟩
    intro a
    rw [value_succ]
    simp only [Fin.cons_zero,Fin.cons_succ,Function.comp_def,zsmul_eq_mul]
    change Holds (s a) ((c a 0 : ℚ) * r + value (c a ∘ Fin.succ) y)
    rcases lt_trichotomy (c a 0) 0 with ha | ha | ha
    · let b : Im := ⟨a,ha⟩
      have hb := hrU b
      have ha' : (0 : ℚ) < -(c a 0 : ℚ) := by exact_mod_cast (neg_pos.mpr ha)
      change (if s a then r < value (c a ∘ Fin.succ) y / -(c a 0 : ℚ)
        else r ≤ value (c a ∘ Fin.succ) y / -(c a 0 : ℚ)) at hb
      unfold Holds
      split_ifs at hb ⊢ with hs
      · have hh := (lt_div_iff₀ ha').mp hb
        nlinarith
      · have hh := (le_div_iff₀ ha').mp hb
        nlinarith
    · have hh := hy (Sum.inl (⟨a,ha⟩ : I0))
      simpa only [ha,Int.cast_zero,zero_mul,zero_add,C,S,Sum.elim_inl,Function.comp_def] using hh
    · let b : Ip := ⟨a,ha⟩
      have hb := hrL b
      have ha' : (0 : ℚ) < c a 0 := by exact_mod_cast ha
      change (if s a then -value (c a ∘ Fin.succ) y / (c a 0 : ℚ) < r
        else -value (c a ∘ Fin.succ) y / (c a 0 : ℚ) ≤ r) at hb
      unfold Holds
      split_ifs at hb ⊢ with hs
      · have hh := (div_lt_iff₀ ha').mp hb
        nlinarith
      · have hh := (div_le_iff₀ ha').mp hb
        nlinarith

end HessianTheorem11.UnconditionalOrderedWeights
