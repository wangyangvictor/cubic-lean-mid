import CubicTenVariables.GeometricSieveTupleMultiplicity

/-! Elimination of modulus-tuple multiplicity over the literal pivot-point
image. The result is stronger than a fixed-tail version: it holds before
restricting the tuple set to any tail slice. -/
set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.StratifiedPrefixElimination
open MvPolynomial

theorem point_image_card_le_pivot_image_card {n s : ℕ}
    (j : Fin s) (E : Finset ((Fin s → ℕ) × (Fin n → ℤ))) :
    (E.image Prod.snd).card≤(E.image fun a => (a.1 j,a.2)).card := by
  classical
  have he : (E.image fun a => (a.1 j,a.2)).image Prod.snd=E.image Prod.snd := by
    rw [Finset.image_image]
    rfl
  rw [←he]
  exact Finset.card_image_le

/-- One constant precedes the pivot, center, radius and finite pair set.
No fixed-tail, coprimality, squarefree or supplied prefix-count premise is
needed. Thus this also applies to every literal fixed-tail slice. -/
theorem exists_uniform_bound {n s : ℕ}
    (J : Fin s → Ideal (MvPolynomial (Fin n) ℤ)) (ε : ℝ) (hε : 0 < ε) :
    ∃K : ℝ,1≤K ∧ ∀j : Fin s,∀u : Fin n → ℝ,∀L : ℝ,1≤L →
      ∀E : Finset ((Fin s → ℕ) × (Fin n → ℤ)),
      (∀a∈E,∀i,|(a.2 i : ℝ)-u i|≤L) →
      (∀a∈E,∀i,∃f∈J i,eval a.2 f≠0) →
      (∀a∈E,∀i,0<a.1 i) →
      (∀a∈E,∀i,∀f∈J i,(a.1 i : ℤ)∣eval a.2 f) →
      (E.card : ℝ)≤K*(L+‖u‖)^ε*((E.image fun a => (a.1 j,a.2)).card : ℝ) := by
  classical
  obtain ⟨K,hK,hb⟩ := GeometricSieveTupleMultiplicity.exists_uniform_bound J ε hε
  refine ⟨K,hK,?_⟩
  intro j u L hL E hbox hout hpos hdiv
  apply (hb u L hL E hbox hout hpos hdiv).trans
  apply mul_le_mul_of_nonneg_left
    (show ((E.image Prod.snd).card : ℝ)≤((E.image fun a => (a.1 j,a.2)).card : ℝ) by
      exact_mod_cast point_image_card_le_pivot_image_card j E)
  exact mul_nonneg (zero_le_one.trans hK)
    (Real.rpow_nonneg (by linarith [norm_nonneg u]) ε)

end CubicTenVariables.StratifiedPrefixElimination
