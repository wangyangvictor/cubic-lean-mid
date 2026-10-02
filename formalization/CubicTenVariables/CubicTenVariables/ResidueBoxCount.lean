import CubicTenVariables.WeightedResidueMaximum
import CubicTenVariables.IntegerProjectionCount
import Mathlib.Algebra.Order.Floor.Ring

/-! Uniform residue-class counts in arbitrarily translated real boxes. -/

noncomputable section
namespace CubicTenVariables.ResidueBoxCount
open scoped BigOperators

/-- A loose absolute constant avoids any alignment assumption on the box. -/
theorem card_le_of_constant_residue {n : ℕ} (c : ℕ) [NeZero c]
    (S : Finset (Fin n → ℤ)) (u : Fin n → ℝ) (R : ℝ) (hR : 0 ≤ R)
    (hbox : ∀ x ∈ S, ∀ i, |(x i : ℝ)-u i| ≤ R)
    (hres : ∀ x ∈ S, ∀ y ∈ S, ∀ i, (x i : ZMod c) = (y i : ZMod c)) :
    (S.card : ℝ) ≤ (4*R/(c : ℝ)+3)^n := by
  classical
  have hc : 0 < (c : ℝ) := by exact_mod_cast NeZero.pos c
  by_cases hS : S.Nonempty
  · obtain ⟨x₀,hx₀⟩ := hS
    let B : ℕ := ⌈2*R/(c : ℝ)⌉₊
    let q : (Fin n → ℤ) → (Fin n → ℤ) := fun x i => (x i-x₀ i)/(c : ℤ)
    have hmul (x : Fin n → ℤ) (hx : x ∈ S) (i : Fin n) :
        q x i*(c : ℤ) = x i-x₀ i := by
      apply Int.ediv_mul_cancel
      apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
      simp only [Int.cast_sub, hres x hx x₀ hx₀ i, sub_self]
    have hq (x : Fin n → ℤ) (hx : x ∈ S) : q x ∈ integerBox n B := by
      rw [mem_integerBox]
      intro i
      have hm : (q x i : ℝ)*(c : ℝ) = (x i : ℝ)-(x₀ i : ℝ) := by
        exact_mod_cast hmul x hx i
      have hd : |(x i : ℝ)-(x₀ i : ℝ)| ≤ 2*R :=
        (abs_sub_le (x i : ℝ) (u i) (x₀ i : ℝ)).trans (by
          rw [abs_sub_comm (u i)]
          linarith [hbox x hx i,hbox x₀ hx₀ i])
      have hqR : |(q x i : ℝ)| ≤ 2*R/(c : ℝ) := by
        apply (le_div_iff₀ hc).mpr
        rw [← abs_of_pos hc, ← abs_mul, hm]
        exact hd
      have hB : |(q x i : ℝ)| ≤ (B : ℝ) := hqR.trans (Nat.le_ceil _)
      exact_mod_cast hB
    have hinj : Set.InjOn q (S : Set (Fin n → ℤ)) := by
      intro x hx y hy hxy
      funext i
      have hm₁ := hmul x hx i
      have hm₂ := hmul y hy i
      rw [congrFun hxy i] at hm₁
      omega
    have hcard : S.card ≤ (2*B+1)^n := by
      calc
        _ = (S.image q).card := (Finset.card_image_iff.mpr hinj).symm
        _ ≤ (integerBox n B).card := Finset.card_le_card (by
          intro y hy
          obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hy
          exact hq x hx)
        _ = _ := card_integerBox n B
    have hB : (B : ℝ) ≤ 2*R/(c : ℝ)+1 :=
      (Nat.ceil_lt_add_one (div_nonneg (by positivity) hc.le)).le
    have hbase : ((2*B+1 : ℕ) : ℝ) ≤ 4*R/(c : ℝ)+3 := by
      push_cast
      have he : 4*R/(c : ℝ) = 2*(2*R/(c : ℝ)) := by ring
      rw [he]
      linarith
    calc
      _ ≤ (((2*B+1)^n : ℕ) : ℝ) := by exact_mod_cast hcard
      _ ≤ _ := by rw [Nat.cast_pow]; exact pow_le_pow_left₀ (Nat.cast_nonneg _) hbase n
  · have he : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
    simp only [he,Finset.card_empty,Nat.cast_zero]
    positivity

/-- The maximum is literal, and the center can have arbitrary real coordinates. -/
theorem maximum_one_le {n : ℕ} (c : ℕ) [NeZero c]
    (V : Finset (Fin n → ℤ)) (u : Fin n → ℝ) (R : ℝ) (hR : 0 ≤ R)
    (hbox : ∀ x ∈ V, ∀ i, |(x i : ℝ)-u i| ≤ R) :
    WeightedResidueMaximum.maximum c V (fun _ => 1) ≤ (4*R/(c : ℝ)+3)^n := by
  classical
  obtain ⟨k,hk⟩ := WeightedResidueMaximum.maximum_attained c V (fun _ => 1)
  rw [hk,WeightedResidueMaximum.classWeight]
  simp only [Finset.sum_const,nsmul_eq_mul,mul_one]
  apply card_le_of_constant_residue c _ u R hR
  · intro x hx
    exact hbox x (Finset.mem_filter.mp hx).1
  · intro x hx y hy i
    have hxk := congrFun (Finset.mem_filter.mp hx).2 i
    have hyk := congrFun (Finset.mem_filter.mp hy).2 i
    exact hxk.trans hyk.symm

/-- The elementary large-box range used before Poisson summation. -/
theorem maximum_one_le_of_modulus_le_radius {n : ℕ} (c : ℕ) [NeZero c]
    (V : Finset (Fin n → ℤ)) (u : Fin n → ℝ) (R : ℝ) (hcR : (c : ℝ) ≤ R)
    (hbox : ∀ x ∈ V, ∀ i, |(x i : ℝ)-u i| ≤ R) :
    WeightedResidueMaximum.maximum c V (fun _ => 1) ≤ (7*R/(c : ℝ))^n := by
  have hc : 0 < (c : ℝ) := by exact_mod_cast NeZero.pos c
  have hR : 0 ≤ R := hc.le.trans hcR
  apply (maximum_one_le c V u R hR hbox).trans
  apply pow_le_pow_left₀ (by positivity)
  have hr : 1 ≤ R/(c : ℝ) := (one_le_div hc).mpr hcR
  have he : 4*R/(c : ℝ) = 4*(R/(c : ℝ)) := by ring
  have he' : 7*R/(c : ℝ) = 7*(R/(c : ℝ)) := by ring
  rw [he,he']
  linarith

end CubicTenVariables.ResidueBoxCount
