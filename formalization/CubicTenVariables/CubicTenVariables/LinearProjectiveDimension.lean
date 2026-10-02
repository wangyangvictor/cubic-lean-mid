import CubicTenVariables.LinearSubspaceDimension

/-! The normalized-chart projective dimension of a linear space of vector
dimension at most s+1 is at most s, in every infinite characteristic. -/

noncomputable section
namespace CubicTenVariables.LinearProjectiveDimension
open MvPolynomial Module ReducedGaussSection LinearSubspaceDimension
variable {K : Type*} [Field K] {n : ℕ}

def translationEquiv (c : Fin n → K) :
    MvPolynomial (Fin n) K ≃ₐ[K] MvPolynomial (Fin n) K :=
  AlgEquiv.ofAlgHom (aeval (fun i => X i+C (c i)))
    (aeval (fun i => X i-C (c i)))
    (by apply MvPolynomial.algHom_ext; intro i; simp)
    (by apply MvPolynomial.algHom_ext; intro i; simp)

theorem eval_translation (c x : Fin n → K) (p : MvPolynomial (Fin n) K) :
    eval (c+x) p = eval x (translationEquiv c p) := by
  change aeval (c+x) p = aeval x (aeval (fun i => X i+C (c i)) p)
  rw [comp_aeval_apply]
  congr 2
  funext i
  simp [Pi.add_apply,add_comm]

theorem dimension_translation (c : Fin n → K) (Z : Set (Fin n → K)) :
    coordinateDimension ((fun x => c+x) '' Z) = coordinateDimension Z := by
  let f := (translationEquiv c).toRingHom
  let I := vanishingIdeal K Z
  have he : vanishingIdeal K ((fun x => c+x) '' Z)=I.comap f := by
    ext p
    constructor
    · intro hp x hx
      exact (eval_translation c x p).symm.trans (hp (c+x) ⟨x,hx,rfl⟩)
    · intro hp y hy
      obtain ⟨x,hx,rfl⟩ := hy
      exact (eval_translation c x p).trans (hp x hx)
  unfold coordinateDimension
  rw [he]
  exact ringKrullDim_eq_of_ringEquiv (RingEquiv.ofBijective
    (Ideal.quotientMap I f le_rfl)
    ⟨Ideal.quotientMap_injective,
      Ideal.quotientMap_surjective (translationEquiv c).surjective⟩)

theorem dimension_empty : coordinateDimension (∅ : Set (Fin n → K))=⊥ := by
  unfold coordinateDimension
  rw [vanishingIdeal_empty]
  exact ringKrullDim_eq_bot_of_subsingleton

/-- A nonempty normalized chart is an actual translate of the kernel of
one nonzero linear functional on the given subspace. -/
theorem chart_dimension_le [Infinite K] (W : Submodule K (Fin n → K))
    (s : ℕ) (hW : finrank K W ≤ s+1) (k : Fin n) :
    coordinateDimension (normalizedChart (W : Set (Fin n → K)) k) ≤
      (s : WithBot ℕ∞) := by
  classical
  by_cases hc : (normalizedChart (W : Set (Fin n → K)) k).Nonempty
  · obtain ⟨c,hcW,hck⟩ := hc
    let l : W →ₗ[K] K := (LinearMap.proj k).comp W.subtype
    let U : Submodule K (Fin n → K) := (LinearMap.ker l).map W.subtype
    have hl : Function.Surjective l := by
      intro a
      refine ⟨a • (⟨c,hcW⟩ : W),?_⟩
      change a*c k=a
      rw [hck,mul_one]
    have hdim := l.finrank_range_add_finrank_ker
    rw [LinearMap.range_eq_top.mpr hl] at hdim
    simp only [finrank_top,finrank_self] at hdim
    have hU : finrank K U = finrank K (LinearMap.ker l) :=
      (Submodule.equivMapOfInjective W.subtype W.subtype_injective
        (LinearMap.ker l)).finrank_eq.symm
    have hUs : finrank K U ≤ s := by omega
    have he : normalizedChart (W : Set (Fin n → K)) k =
        (fun x => c+x) '' (U : Set (Fin n → K)) := by
      ext x
      constructor
      · rintro ⟨hxW,hxk⟩
        refine ⟨x-c,?_,by abel_nf⟩
        refine ⟨⟨x-c,W.sub_mem hxW hcW⟩,?_,rfl⟩
        change x k-c k=0
        rw [hxk,hck,sub_self]
      · rintro ⟨y,⟨u,hu,rfl⟩,rfl⟩
        refine ⟨W.add_mem hcW u.property,?_⟩
        change c k+u.val k=1
        have hu0 : u.val k=0 := hu
        rw [hck,hu0,add_zero]
    rw [he,dimension_translation,dimension_submodule]
    exact_mod_cast hUs
  · rw [Set.not_nonempty_iff_eq_empty.mp hc,dimension_empty]
    exact bot_le

/-- This proves the source projective vertex convention using the actual
normalized affine charts, rather than merely renaming a linear rank. -/
theorem projectiveDimension_le [Infinite K] (W : Submodule K (Fin n → K))
    (s : ℕ) (hW : finrank K W ≤ s+1) :
    ReducedGaussSection.projectiveDimension (W : Set (Fin n → K)) ≤
      (s : WithBot ℕ∞) :=
  iSup_le (chart_dimension_le W s hW)

end CubicTenVariables.LinearProjectiveDimension
