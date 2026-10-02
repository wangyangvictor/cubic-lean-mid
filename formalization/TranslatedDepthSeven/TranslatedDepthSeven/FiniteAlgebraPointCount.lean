import Mathlib.FieldTheory.Fixed
import Mathlib.RingTheory.TensorProduct.Finite
import TranslatedDepthSeven.FiniteProjectionResidueCount

/-!
# Field-valued points of a finite algebra

Let `K` be a finite field and let `A` be a finite-dimensional commutative
`K`-algebra.  A `K`-point of `Spec A` is a `K`-algebra homomorphism
`A →ₐ[K] K`.  Distinct algebra homomorphisms are linearly independent as
linear maps (Dedekind independence), so there are at most `finrank K A` of
them.

This is the exact elementary counting statement needed after one component
has been made finite free over its Noether-normalisation base.  It avoids any
choice of generators or ordering of integral equations in the residue fibre.
-/

namespace TranslatedDepthSeven

noncomputable section

open scoped TensorProduct

universe u v

/-- A point of affine `s`-space is exactly an algebra homomorphism from its
polynomial coordinate ring. -/
def mvPolynomialAlgHomEquiv
    (K : Type u) (s : ℕ) [CommSemiring K] :
    (MvPolynomial (Fin s) K →ₐ[K] K) ≃ (Fin s → K) where
  toFun f := fun i ↦ f (MvPolynomial.X i)
  invFun x := MvPolynomial.aeval x
  left_inv f := by
    apply MvPolynomial.algHom_ext
    intro i
    simp
  right_inv x := by
    funext i
    simp

/-- Consequently affine `s`-space over a finite coefficient ring has
exactly `(#K)^s` points. -/
theorem natCard_mvPolynomial_algHom_self
    (K : Type u) (s : ℕ) [CommSemiring K] [Finite K] :
    Nat.card (MvPolynomial (Fin s) K →ₐ[K] K) = Nat.card K ^ s := by
  rw [Nat.card_congr (mvPolynomialAlgHomEquiv K s)]
  simp only [Nat.card_fun, Nat.card_fin]

/-- Summing uniformly bounded fibres over the points of affine `s`-space
gives the exact factor `(#K)^s`.  This is the finite-set bookkeeping used
with a normalization map. -/
theorem natCard_le_mul_pow_of_mvPolynomial_fibers
    (K : Type u) (s D : ℕ) [CommSemiring K] [Finite K]
    (X : Type v) [Finite X]
    (f : X → (MvPolynomial (Fin s) K →ₐ[K] K))
    (hfibre : ∀ y, Nat.card {x : X // f x = y} ≤ D) :
    Nat.card X ≤ D * Nat.card K ^ s := by
  letI : Fintype K := Fintype.ofFinite K
  letI : Fintype X := Fintype.ofFinite X
  letI : DecidableEq X := Classical.decEq X
  letI : Fintype (MvPolynomial (Fin s) K →ₐ[K] K) :=
    Fintype.ofEquiv (Fin s → K) (mvPolynomialAlgHomEquiv K s).symm
  letI : DecidableEq (MvPolynomial (Fin s) K →ₐ[K] K) :=
    Classical.decEq _
  have hfibre' : ∀ y,
      (finiteMapFiber f (Finset.univ : Finset X) y).card ≤ D := by
    intro y
    rw [finiteMapFiber, ← Fintype.card_subtype]
    simpa only [Nat.card_eq_fintype_card] using hfibre y
  rw [Nat.card_eq_fintype_card]
  calc
    Fintype.card X ≤
        D * Fintype.card (MvPolynomial (Fin s) K →ₐ[K] K) := by
      simpa using
        card_finiteSet_le_of_map_fibers_le f (Finset.univ : Finset X) hfibre'
    _ = D * Nat.card K ^ s := by
      rw [← natCard_mvPolynomial_algHom_self K s,
        Nat.card_eq_fintype_card]

/-- A finite-dimensional algebra over a finite field has at most its vector
space dimension many rational points. -/
theorem natCard_algHom_self_le_finrank
    (K : Type u) (A : Type v)
    [Field K] [Finite K]
    [CommRing A] [Algebra K A] [FiniteDimensional K A] :
    Nat.card (A →ₐ[K] K) ≤ Module.finrank K A := by
  letI : Fintype K := Fintype.ofFinite K
  letI : Fintype (A →ₐ[K] K) := Fintype.ofFinite (A →ₐ[K] K)
  rw [Nat.card_eq_fintype_card]
  simpa only [Module.finrank_linearMap, Module.finrank_self, Nat.mul_one] using
    (linearIndependent_toLinearMap K A K).fintype_card_le_finrank

/-- The same bound with a displayed numerical upper bound for the fibre
dimension. -/
theorem natCard_algHom_self_le_of_finrank_le
    (K : Type u) (A : Type v)
    [Field K] [Finite K]
    [CommRing A] [Algebra K A] [FiniteDimensional K A]
    {D : ℕ} (hD : Module.finrank K A ≤ D) :
    Nat.card (A →ₐ[K] K) ≤ D :=
  (natCard_algHom_self_le_finrank K A).trans hD

/-- In particular, a finite free fibre of rank `D` has at most `D`
field-valued points. -/
theorem natCard_algHom_self_le_of_finrank_eq
    (K : Type u) (A : Type v)
    [Field K] [Finite K]
    [CommRing A] [Algebra K A] [FiniteDimensional K A]
    {D : ℕ} (hD : Module.finrank K A = D) :
    Nat.card (A →ₐ[K] K) ≤ D := by
  rw [← hD]
  exact natCard_algHom_self_le_finrank K A

/-- Extension of a point `A →ₐ[R] K` across scalar base change.  The
normalization-base point is encoded by the chosen `R`-algebra structure on
`K`; hence this is precisely one fibre of restriction from component points
to normalization-base points. -/
def baseChangeLiftAlgHom
    (R : Type u) (K : Type v) (A : Type*)
    [CommRing R] [Field K] [CommRing A]
    [Algebra R K] [Algebra R A]
    (g : A →ₐ[R] K) : (K ⊗[R] A) →ₐ[K] K :=
  Algebra.TensorProduct.lift (AlgHom.id K K) g
    (fun _ _ ↦ mul_comm _ _)

/-- Base-change extension is injective because restriction along the right
tensor factor recovers the original point. -/
theorem baseChangeLiftAlgHom_injective
    (R : Type u) (K : Type v) (A : Type*)
    [CommRing R] [Field K] [CommRing A]
    [Algebra R K] [Algebra R A] :
    Function.Injective (baseChangeLiftAlgHom R K A) := by
  intro g h hgh
  have hrestrict := congrArg
    (fun q : (K ⊗[R] A) →ₐ[K] K ↦
      (q.restrictScalars R).comp Algebra.TensorProduct.includeRight)
    hgh
  simpa only [baseChangeLiftAlgHom,
    Algebra.TensorProduct.lift_comp_includeRight] using hrestrict

/-- A fibre of restriction to one normalization-base point has cardinality
at most the vector-space dimension of the corresponding scalar fibre
algebra. -/
theorem natCard_algHom_over_base_le_baseChange_finrank
    (R : Type u) (K : Type v) (A : Type*)
    [CommRing R] [Field K] [Finite K] [CommRing A]
    [Algebra R K] [Algebra R A] [Module.Finite R A] :
    Nat.card (A →ₐ[R] K) ≤ Module.finrank K (K ⊗[R] A) := by
  letI : Module.Finite K (K ⊗[R] A) :=
    Module.Finite.base_change R K A
  exact (Nat.card_le_card_of_injective _
      (baseChangeLiftAlgHom_injective R K A)).trans
    (natCard_algHom_self_le_finrank K (K ⊗[R] A))

/-- Numerical form of the normalization-fibre estimate. -/
theorem natCard_algHom_over_base_le_of_baseChange_finrank_le
    (R : Type u) (K : Type v) (A : Type*)
    [CommRing R] [Field K] [Finite K] [CommRing A]
    [Algebra R K] [Algebra R A] [Module.Finite R A]
    {D : ℕ} (hD : Module.finrank K (K ⊗[R] A) ≤ D) :
    Nat.card (A →ₐ[R] K) ≤ D :=
  (natCard_algHom_over_base_le_baseChange_finrank R K A).trans hD

end

end TranslatedDepthSeven
