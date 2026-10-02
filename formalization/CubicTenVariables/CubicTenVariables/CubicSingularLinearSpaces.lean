import CubicTenVariables.PlaneCubicSingularGeometry
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! Concrete secant eliminations for an integral cubic threefold.
Joins of singular linear spaces lie on the cubic. A join that is a hyperplane
would force a linear factor. No singular-locus classification is assumed,
and the joining points are never asserted to be singular. -/
set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.CubicSingularLinearSpaces
open MvPolynomial HessianTheorem11 Module PlaneCubicSingularGeometry

variable {K : Type*} [Field K]

/-- Secants between two actual singular linear spaces lie on the cubic. -/
theorem eval_eq_zero_on_sup {n : ℕ}
    (F : MvPolynomial (Fin n) K) (hF : F.IsHomogeneous 3)
    (L M : Submodule K (Fin n → K))
    (hL : ∀ x ∈ L, eval x F = 0 ∧ gradient F x = 0)
    (hM : ∀ x ∈ M, eval x F = 0 ∧ gradient F x = 0)
    (x : Fin n → K) (hx : x ∈ L ⊔ M) : eval x F = 0 := by
  obtain ⟨u, hu, v, hv, rfl⟩ := Submodule.mem_sup.mp hx
  simpa only [one_smul] using eval_singular_span F hF u v
    (hL u hu).1 (hL u hu).2 (hM v hv).1 (hM v hv).2 1 1

/-- A four-dimensional affine join would be a projective hyperplane
component, impossible for an irreducible cubic in five variables. -/
theorem singular_sup_finrank_ne_four [IsAlgClosed K]
    (F : MvPolynomial (Fin 5) K) (hF : F.IsHomogeneous 3) (hirr : Irreducible F)
    (L M : Submodule K (Fin 5 → K))
    (hL : ∀ x ∈ L, eval x F = 0 ∧ gradient F x = 0)
    (hM : ∀ x ∈ M, eval x F = 0 ∧ gradient F x = 0) :
    finrank K (L ⊔ M : Submodule K (Fin 5 → K)) ≠ 4 := by
  intro hdim
  let W : Submodule K (Fin 5 → K) := L ⊔ M
  have hWlt : W < ⊤ := Submodule.lt_top_of_finrank_lt_finrank (by
    simpa only [W, hdim, Module.finrank_pi, Fintype.card_fin] using (by decide : 4 < 5))
  obtain ⟨f, hf, hWf⟩ := W.exists_le_ker_of_lt_top hWlt
  have hker := Module.Dual.finrank_ker_add_one_of_ne_zero hf
  have hWeq : W = LinearMap.ker f := Submodule.eq_of_le_of_finrank_eq hWf (by
    simp only [Module.finrank_pi, Fintype.card_fin] at hker
    change finrank K (L ⊔ M : Submodule K (Fin 5 → K)) = _
    omega)
  have hd := degree_le_one_of_vanishes_on_hyperplane F hirr f hf (by
    intro x hx
    have hxW : x ∈ W := hWeq ▸ hx
    exact eval_eq_zero_on_sup F hF L M hL hM x hxW)
  rw [hF.totalDegree hirr.ne_zero] at hd
  omega

/-- Two geometric singular lines on an integral cubic threefold intersect.
Their affine two-dimensional spaces cannot have zero intersection. -/
theorem not_disjoint_singular_lines [IsAlgClosed K]
    (F : MvPolynomial (Fin 5) K) (hF : F.IsHomogeneous 3) (hirr : Irreducible F)
    (L M : Submodule K (Fin 5 → K)) (hLd : finrank K L = 2) (hMd : finrank K M = 2)
    (hL : ∀ x ∈ L, eval x F = 0 ∧ gradient F x = 0)
    (hM : ∀ x ∈ M, eval x F = 0 ∧ gradient F x = 0) : ¬ Disjoint L M := by
  intro hd
  have hdim := L.finrank_sup_add_finrank_inf_eq M
  rw [hd.eq_bot, finrank_bot, add_zero, hLd, hMd] at hdim
  exact singular_sup_finrank_ne_four F hF hirr L M hL hM hdim

/-- Once a projective singular plane is present, every singular point is
on that plane. A point outside it would produce a hyperplane of secants. -/
theorem singular_point_mem_singular_plane [IsAlgClosed K]
    (F : MvPolynomial (Fin 5) K) (hF : F.IsHomogeneous 3) (hirr : Irreducible F)
    (L : Submodule K (Fin 5 → K)) (hLd : finrank K L = 3)
    (hL : ∀ x ∈ L, eval x F = 0 ∧ gradient F x = 0)
    (p : Fin 5 → K) (hp : eval p F = 0) (hgp : gradient F p = 0) : p ∈ L := by
  by_contra hnot
  have hp0 : p ≠ 0 := by intro h; exact hnot (h ▸ L.zero_mem)
  let M : Submodule K (Fin 5 → K) := Submodule.span K {p}
  have hM : ∀ x ∈ M, eval x F = 0 ∧ gradient F x = 0 := by
    intro x hx
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hx
    constructor
    · simpa only [eval₂_id, hp, mul_zero] using
        CubicGradientScaling.homogeneous_eval₂_smul F hF (RingHom.id K) p a
    · funext i
      have hi : eval p (pderiv i F) = 0 := congrFun hgp i
      change eval (a • p) (pderiv i F) = 0
      simpa only [eval₂_id, hi, mul_zero] using
        CubicGradientScaling.eval₂_partial_smul F hF (RingHom.id K) i p a
  have hMd : finrank K M = 1 := finrank_span_singleton hp0
  have hdis : Disjoint L M := Submodule.disjoint_span_singleton_of_notMem hnot
  have hdim := L.finrank_sup_add_finrank_inf_eq M
  rw [hdis.eq_bot, finrank_bot, add_zero, hLd, hMd] at hdim
  exact singular_sup_finrank_ne_four F hF hirr L M hL hM hdim

end CubicTenVariables.CubicSingularLinearSpaces
