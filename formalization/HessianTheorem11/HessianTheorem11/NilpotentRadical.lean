import HessianTheorem11.CliffordDivisibility
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Matrix.Rank

/-! The actual rank obstruction for a self-adjoint square-zero radical
operator anticommuting with a self-adjoint involution. -/

noncomputable section
namespace HessianTheorem11.NilpotentRadical
open Module

variable {K V : Type*} [Field K] [CharZero K]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/-- A skew pairing with radical `ker N` makes the actual image of `N`
even-dimensional. The proof constructs a nondegenerate restriction on a
complement of the kernel. -/
theorem even_finrank_range_of_skew_pairing
    (N : Module.End K V) (γ : LinearMap.BilinForm K V)
    (hskew : ∀ v w, γ v w = -γ w v)
    (hker : ∀ v, N v = 0 ↔ ∀ w, γ v w = 0) :
    Even (finrank K (LinearMap.range N)) := by
  obtain ⟨W, hW⟩ := (LinearMap.ker N).exists_isCompl
  have hnondeg : (γ.restrict W).Nondegenerate := by
    intro v hv
    apply Subtype.ext
    have hvker : (v : V) ∈ LinearMap.ker N := by
      apply (hker v).mpr
      intro y
      obtain ⟨k, w, hk, hw, rfl⟩ :=
        Submodule.codisjoint_iff_exists_add_eq.mp hW.codisjoint y
      have hk0 : γ (v : V) k = 0 := by
        rw [hskew]
        have ht := (hker k).mp hk (v : V)
        rw [ht, neg_zero]
      have hw0 : γ (v : V) w = 0 := hv ⟨w, hw⟩
      rw [map_add, hk0, hw0, add_zero]
    exact Submodule.disjoint_def.mp hW.disjoint _ hvker v.property
  have he := CliffordDivisibility.even_finrank_of_nondegenerate_skew_form
    (γ.restrict W) hnondeg (fun v w => hskew v w)
  have hd := Submodule.finrank_sup_add_finrank_inf_eq (LinearMap.ker N) W
  rw [hW.sup_eq_top, hW.inf_eq_bot, finrank_top, finrank_bot, add_zero] at hd
  have hr := N.finrank_range_add_finrank_ker
  have heq : finrank K W = finrank K (LinearMap.range N) := by omega
  rwa [heq] at he

/-- Anticommuting self-adjointness supplies the skew pairing. No square-zero
hypothesis or algebraic closedness is needed for this parity conclusion. -/
theorem even_rank_of_self_adjoint_anticommuting_involution
    (β : LinearMap.BilinForm K V) (hβ : β.Nondegenerate) (hβsym : β.IsSymm)
    (N J : Module.End K V) (hJ : J * J = 1)
    (hanti : N * J = -(J * N))
    (hNself : ∀ v w, β (N v) w = β v (N w))
    (hJself : ∀ v w, β (J v) w = β v (J w)) :
    Even (finrank K (LinearMap.range N)) := by
  let γ := (β.compLeft N).compRight J
  have hskew : ∀ v w, γ v w = -γ w v := by
    intro v w
    change β (N v) (J w) = -β (N w) (J v)
    calc
      _ = β v (N (J w)) := hNself v (J w)
      _ = β v (-(J (N w))) := by
        rw [CliffordDivisibility.anticommuting_apply N J hanti]
      _ = -β v (J (N w)) := map_neg _ _
      _ = -β (J v) (N w) := congrArg Neg.neg (hJself v (N w)).symm
      _ = _ := congrArg Neg.neg (hβsym.eq _ _)
  apply even_finrank_range_of_skew_pairing N γ hskew
  intro v
  constructor
  · intro hv w
    change β (N v) (J w) = 0
    rw [hv, map_zero, LinearMap.zero_apply]
  · intro hv
    apply hβ (N v)
    intro w
    have ht := hv (J w)
    change β (N v) (J (J w)) = 0 at ht
    rwa [CliffordDivisibility.involution_apply_twice J hJ] at ht

omit [CharZero K] in
/-- A square-zero endomorphism has image contained in its kernel. -/
theorem twice_rank_le_of_square_zero (N : Module.End K V) (hN : N * N = 0) :
    2 * finrank K (LinearMap.range N) ≤ finrank K V := by
  have hle : LinearMap.range N ≤ LinearMap.ker N := by
    rintro _ ⟨v, rfl⟩
    have h := congrArg (fun f : Module.End K V => f v) hN
    simpa only [Module.End.mul_apply, LinearMap.zero_apply] using h
  have hr := Submodule.finrank_mono hle
  have hd := N.finrank_range_add_finrank_ker
  omega

/-- In dimension at most seven, a self-adjoint square-zero operator
anticommuting with a self-adjoint involution has actual rank at most two. -/
theorem rank_le_two_of_dimension_le_seven
    (β : LinearMap.BilinForm K V) (hβ : β.Nondegenerate) (hβsym : β.IsSymm)
    (N J : Module.End K V) (hN : N * N = 0) (hJ : J * J = 1)
    (hanti : N * J = -(J * N))
    (hNself : ∀ v w, β (N v) w = β v (N w))
    (hJself : ∀ v w, β (J v) w = β v (J w))
    (hdim : finrank K V ≤ 7) : finrank K (LinearMap.range N) ≤ 2 := by
  obtain ⟨k, hk⟩ := even_rank_of_self_adjoint_anticommuting_involution
    β hβ hβsym N J hJ hanti hNself hJself
  have hr := twice_rank_le_of_square_zero N hN
  omega

theorem matrix_rank_le_two {q : ℕ}
    (β : LinearMap.BilinForm K (Fin q → K)) (hβ : β.Nondegenerate) (hβsym : β.IsSymm)
    (N J : Matrix (Fin q) (Fin q) K) (hN : N * N = 0) (hJ : J * J = 1)
    (hanti : N * J = -(J * N))
    (hNself : ∀ v w, β (N.mulVec v) w = β v (N.mulVec w))
    (hJself : ∀ v w, β (J.mulVec v) w = β v (J.mulVec w))
    (hq : q ≤ 7) : N.rank ≤ 2 := by
  apply rank_le_two_of_dimension_le_seven β hβ hβsym
    (Matrix.toLinAlgEquiv' N) (Matrix.toLinAlgEquiv' J)
  · simpa only [map_mul, map_zero] using congrArg (Matrix.toLinAlgEquiv' (R := K)) hN
  · simpa only [map_mul, map_one] using congrArg (Matrix.toLinAlgEquiv' (R := K)) hJ
  · simpa only [map_mul, map_neg] using congrArg (Matrix.toLinAlgEquiv' (R := K)) hanti
  · exact hNself
  · exact hJself
  · simpa using hq

end HessianTheorem11.NilpotentRadical
