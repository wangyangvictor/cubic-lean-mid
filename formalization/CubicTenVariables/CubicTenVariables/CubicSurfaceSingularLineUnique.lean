import CubicTenVariables.CubicSurfaceNonisolatedLine
import CubicTenVariables.CubicSurfaceIsolatedSingularBound
import CubicTenVariables.CubicSingularLinearSpaces

/-! The singular line of an integral cubic surface is the whole geometric
singular cone. A singular point outside it would produce a hyperplane of
secants contained in the cubic and hence a forbidden linear factor. -/
set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.CubicSurfaceSingularLineUnique
open MvPolynomial HessianTheorem11 Module PlaneCubicSingularGeometry
open CubicSingularLinearSpaces CubicSurfaceProjectiveSingular
variable {K : Type*} [Field K]

/-- A three-dimensional affine join would be a projective hyperplane
component, impossible for an irreducible cubic in four variables. -/
theorem singular_sup_finrank_ne_three [IsAlgClosed K]
    (F : MvPolynomial (Fin 4) K) (hF : F.IsHomogeneous 3) (hirr : Irreducible F)
    (L M : Submodule K (Fin 4 → K))
    (hL : ∀ x ∈ L, eval x F = 0 ∧ gradient F x = 0)
    (hM : ∀ x ∈ M, eval x F = 0 ∧ gradient F x = 0) :
    finrank K (L ⊔ M : Submodule K (Fin 4 → K)) ≠ 3 := by
  intro hdim
  let W : Submodule K (Fin 4 → K) := L ⊔ M
  have hWlt : W < ⊤ := Submodule.lt_top_of_finrank_lt_finrank (by
    simpa only [W, hdim, Module.finrank_pi, Fintype.card_fin] using (by decide : 3 < 4))
  obtain ⟨f, hf, hWf⟩ := W.exists_le_ker_of_lt_top hWlt
  have hker := Module.Dual.finrank_ker_add_one_of_ne_zero hf
  have hWeq : W = LinearMap.ker f := Submodule.eq_of_le_of_finrank_eq hWf (by
    simp only [Module.finrank_pi, Fintype.card_fin] at hker
    change finrank K (L ⊔ M : Submodule K (Fin 4 → K)) = _
    omega)
  have hd := degree_le_one_of_vanishes_on_hyperplane F hirr f hf (by
    intro x hx
    have hxW : x ∈ W := hWeq ▸ hx
    exact eval_eq_zero_on_sup F hF L M hL hM x hxW)
  rw [hF.totalDegree hirr.ne_zero] at hd
  omega

/-- Once a projective singular line is present, every singular point is
on that line. A point outside it would produce a hyperplane of secants. -/
theorem singular_point_mem_line [IsAlgClosed K]
    (F : MvPolynomial (Fin 4) K) (hF : F.IsHomogeneous 3) (hirr : Irreducible F)
    (L : Submodule K (Fin 4 → K)) (hLd : finrank K L = 2)
    (hL : ∀ x ∈ L, eval x F = 0 ∧ gradient F x = 0)
    (p : Fin 4 → K) (hp : eval p F = 0) (hgp : gradient F p = 0) : p ∈ L := by
  by_contra hnot
  have hp0 : p ≠ 0 := by intro h; exact hnot (h ▸ L.zero_mem)
  let M : Submodule K (Fin 4 → K) := Submodule.span K {p}
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
  exact singular_sup_finrank_ne_three F hF hirr L M hL hM hdim

/-- The entire actual singular cone is the unique two-dimensional singular vector space
(projectively a line) whenever the projective singular set is nonfinite. -/
theorem exists_unique_line_of_not_finite [IsAlgClosed K]
    (F : MvPolynomial (Fin 4) K) (hF : F.IsHomogeneous 3) (hirr : Irreducible F)
    (hinf : ¬ (singularPoints F).Finite) :
    ∃! L : Submodule K (Fin 4 → K), finrank K L = 2 ∧
      ∀ x, x ∈ L ↔ eval x F = 0 ∧ gradient F x = 0 := by
  obtain ⟨L,hLd,hL⟩ := CubicSurfaceNonisolatedLine.exists_line_of_not_finite F hF hirr hinf
  have he : ∀ x, x ∈ L ↔ eval x F = 0 ∧ gradient F x = 0 := by
    intro x
    exact ⟨hL x, fun hx => singular_point_mem_line F hF hirr L hLd hL x hx.1 hx.2⟩
  refine ⟨L,⟨hLd,he⟩,?_⟩
  intro M hM
  ext x
  exact (hM.2 x).trans (he x).symm

/-- Exact classification of the underlying singular-point set. This does
not assert scheme multiplicities or any birational classification. -/
theorem finite_le_four_or_unique_line [IsAlgClosed K]
    (F : MvPolynomial (Fin 4) K) (hF : F.IsHomogeneous 3) (hirr : Irreducible F) :
    ((singularPoints F).Finite ∧ (singularPoints F).ncard ≤ 4) ∨
      ∃! L : Submodule K (Fin 4 → K), finrank K L = 2 ∧
        ∀ x, x ∈ L ↔ eval x F = 0 ∧ gradient F x = 0 := by
  classical
  by_cases hfin : (singularPoints F).Finite
  · exact Or.inl ⟨hfin,
      CubicSurfaceIsolatedSingularBound.ncard_singularPoints_le_four F hF hirr hfin⟩
  · exact Or.inr (exists_unique_line_of_not_finite F hF hirr hfin)

end CubicTenVariables.CubicSurfaceSingularLineUnique
