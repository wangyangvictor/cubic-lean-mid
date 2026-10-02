import CubicTenVariables.FixedEquationDimensionReduction
import CubicTenVariables.ReducedGaussSection
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-! Coordinate-ring dimension of a linear subspace over every infinite
field. This transfers the already proved geometric rank-locus bounds to
actual dimensions of vertices in positive characteristic. -/

noncomputable section
namespace CubicTenVariables.LinearSubspaceDimension
open MvPolynomial Module
open ReducedGaussSection
variable {K : Type*} [Field K] [Infinite K] {m n : ℕ}

def coordinatePolynomials (L : (Fin m → K) →ₗ[K] (Fin n → K)) :
    Fin n → MvPolynomial (Fin m) K :=
  fun j => ∑ i, C (L ((Pi.basisFun K (Fin m)) i) j) * X i

omit [Infinite K] in
theorem eval_coordinates (L : (Fin m → K) →ₗ[K] (Fin n → K)) (x : Fin m → K) :
    (fun j => eval x (coordinatePolynomials L j)) = L x := by
  funext j
  simp only [coordinatePolynomials,eval_sum,eval_mul,eval_C,eval_X]
  have h := congrArg (fun z => L z j) ((Pi.basisFun K (Fin m)).sum_repr x)
  simpa only [map_sum,map_smul,Finset.sum_apply,Pi.smul_apply,smul_eq_mul,
    Pi.basisFun_repr,mul_comm] using h

omit [Infinite K] in
theorem eval_pullback (L : (Fin m → K) →ₗ[K] (Fin n → K))
    (x : Fin m → K) (p : MvPolynomial (Fin n) K) :
    eval (L x) p = eval x (aeval (coordinatePolynomials L) p) := by
  rw [← eval_coordinates L x]
  change aeval (fun j => eval x (coordinatePolynomials L j)) p =
    aeval x (aeval (coordinatePolynomials L) p)
  rw [comp_aeval_apply]
  rfl

/-- An injective linear map preserves the dimension of every actual
field-valued set. Infinitude is needed for polynomial extensionality. -/
theorem dimension_image (L : (Fin m → K) →ₗ[K] (Fin n → K))
    (hL : Function.Injective L) (Z : Set (Fin m → K)) :
    coordinateDimension (L '' Z) = coordinateDimension Z := by
  obtain ⟨R,hR⟩ := L.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr hL)
  let f : MvPolynomial (Fin n) K →+* MvPolynomial (Fin m) K :=
    (aeval (coordinatePolynomials L)).toRingHom
  have hsurj : Function.Surjective f := by
    intro p
    refine ⟨aeval (coordinatePolynomials R) p,?_⟩
    apply MvPolynomial.funext
    intro x
    change eval x (aeval (coordinatePolynomials L)
      (aeval (coordinatePolynomials R) p)) = eval x p
    rw [← eval_pullback,← eval_pullback]
    exact congrArg (fun z => eval z p) (LinearMap.congr_fun hR x)
  let I := vanishingIdeal K Z
  have hI : vanishingIdeal K (L '' Z) = I.comap f := by
    ext p
    constructor
    · intro hp x hx
      exact (eval_pullback L x p).symm.trans (hp (L x) ⟨x,hx,rfl⟩)
    · intro hp y hy
      obtain ⟨x,hx,rfl⟩ := hy
      exact (eval_pullback L x p).trans (hp x hx)
  unfold coordinateDimension
  rw [hI]
  exact ringKrullDim_eq_of_ringEquiv (RingEquiv.ofBijective
    (Ideal.quotientMap I f le_rfl)
    ⟨Ideal.quotientMap_injective,Ideal.quotientMap_surjective hsurj⟩)

theorem dimension_univ : coordinateDimension (Set.univ : Set (Fin n → K)) =
    (n : WithBot ℕ∞) := by
  have he : vanishingIdeal K (Set.univ : Set (Fin n → K)) = ⊥ := by
    apply le_antisymm
    · intro p hp
      change p=0
      apply MvPolynomial.funext
      intro x
      simpa only [eval_zero] using hp x (Set.mem_univ x)
    · exact bot_le
  unfold coordinateDimension
  rw [he,ringKrullDim_eq_of_ringEquiv (RingEquiv.quotientBot _)]
  exact FixedEquationDimensionReduction.polynomial_dimension K n

def subspaceCoordinates (W : Submodule K (Fin n → K)) :
    (Fin (finrank K W) → K) →ₗ[K] (Fin n → K) :=
  W.subtype.comp ((Module.finBasis K W).equivFun.symm.toLinearMap)

omit [Infinite K] in
theorem subspaceCoordinates_injective (W : Submodule K (Fin n → K)) :
    Function.Injective (subspaceCoordinates W) :=
  W.subtype_injective.comp (Module.finBasis K W).equivFun.symm.injective

omit [Infinite K] in
theorem subspaceCoordinates_range (W : Submodule K (Fin n → K)) :
    Set.range (subspaceCoordinates W) = W := by
  ext x
  constructor
  · rintro ⟨y,rfl⟩
    exact ((Module.finBasis K W).equivFun.symm y).property
  · intro hx
    exact ⟨(Module.finBasis K W).equivFun ⟨x,hx⟩,
      congrArg Subtype.val ((Module.finBasis K W).equivFun.symm_apply_apply ⟨x,hx⟩)⟩

/-- The literal reduced coordinate ring of a linear subspace has its linear
algebra dimension. This theorem is valid in every infinite characteristic. -/
theorem dimension_submodule (W : Submodule K (Fin n → K)) :
    coordinateDimension (W : Set (Fin n → K)) = (finrank K W : WithBot ℕ∞) := by
  have h := dimension_image (subspaceCoordinates W) (subspaceCoordinates_injective W) Set.univ
  rw [Set.image_univ,subspaceCoordinates_range,dimension_univ] at h
  exact h

/-- The source hyperplane-vertex argument needs only this comparison. -/
theorem finrank_le_of_injective_image_subset
    (W : Submodule K (Fin m → K)) (L : (Fin m → K) →ₗ[K] (Fin n → K))
    (hL : Function.Injective L) (Z : Set (Fin n → K)) (r : ℕ)
    (hsub : L '' (W : Set (Fin m → K)) ⊆ Z)
    (hdim : coordinateDimension Z ≤ (r : WithBot ℕ∞)) : finrank K W ≤ r := by
  have h := (coordinateDimension_mono hsub).trans hdim
  rw [dimension_image L hL,dimension_submodule] at h
  exact_mod_cast h

end CubicTenVariables.LinearSubspaceDimension
